"""Mendi BLE protobuf decoder — derived from 2026-05-06 10-min meditation capture.

Service: fc3eabb0-c6c4-49e6-922a-6e551c455af5  (Mendi proprietary)
Characteristics:
  bb1  read+notify  → device-state snapshot at startup (97 bytes, ~16 protobuf fields)
  bb2  write+notify → control channel A (untested)
  bb3  write+notify → control channel B (untested)
  bb4  read+notify  → MAIN STREAM, 3-byte protobuf @ ~2 Hz: tag 1 varint
  bb5  notify       → session/status (9-byte one-shot at startup)
  bb6  read+write+notify → config (untested)

Wire format on bb4 (the main stream):
    08 <varint> = protobuf field 1, wire type 0 (varint)
    All observed values 0x?? 0x1d encode integers in the range ~3700-3850.
    Hypothesis: 12-bit ADC reading from NIR photodetector (raw optical intensity).
    Could also be: blood-flow-score × 1000 OR oxygenation index × 100.
"""
from __future__ import annotations
import json, struct, math
from typing import Iterator


def varint(buf: bytes, pos: int) -> tuple[int, int]:
    """Decode a protobuf varint starting at pos. Returns (value, bytes_consumed)."""
    result = 0
    shift = 0
    start = pos
    while pos < len(buf):
        b = buf[pos]
        result |= (b & 0x7F) << shift
        pos += 1
        if not (b & 0x80):
            return result, pos - start
        shift += 7
    raise ValueError("truncated varint")


def decode_protobuf(buf: bytes) -> dict:
    """Generic protobuf decoder for unknown messages — returns {field_id: [values]}."""
    out: dict[int, list] = {}
    pos = 0
    while pos < len(buf):
        tag, n = varint(buf, pos)
        pos += n
        field_id = tag >> 3
        wire = tag & 0x7
        if wire == 0:  # varint
            val, n = varint(buf, pos)
            pos += n
            # signed-int hint: very large values that would be small negative under zigzag/two's-complement
            sint = val if val < (1 << 63) else val - (1 << 64)
            out.setdefault(field_id, []).append({"u": val, "s": sint})
        elif wire == 1:  # 64-bit (double or fixed64)
            raw = buf[pos:pos+8]; pos += 8
            out.setdefault(field_id, []).append({
                "raw": raw.hex(), "u64": struct.unpack("<Q", raw)[0],
                "i64": struct.unpack("<q", raw)[0], "f64": struct.unpack("<d", raw)[0],
            })
        elif wire == 2:  # length-delimited
            ln, n = varint(buf, pos); pos += n
            data = buf[pos:pos+ln]; pos += ln
            out.setdefault(field_id, []).append({"bytes": data.hex(), "len": ln})
        elif wire == 5:  # 32-bit (float or fixed32)
            raw = buf[pos:pos+4]; pos += 4
            out.setdefault(field_id, []).append({
                "raw": raw.hex(), "u32": struct.unpack("<I", raw)[0],
                "i32": struct.unpack("<i", raw)[0], "f32": struct.unpack("<f", raw)[0],
            })
        else:
            raise ValueError(f"unknown wire type {wire} at pos {pos}")
    return out


def decode_bb4_frame(hex_str: str) -> int | None:
    """Decode a 3-byte bb4 stream frame. Returns the integer signal value."""
    buf = bytes.fromhex(hex_str)
    msg = decode_protobuf(buf)
    if 1 in msg and msg[1]:
        return msg[1][0]["u"]
    return None


def iter_jsonl(path: str) -> Iterator[dict]:
    with open(path) as fh:
        for line in fh:
            line = line.strip()
            if line:
                yield json.loads(line)


if __name__ == "__main__":
    import sys, statistics
    path = sys.argv[1] if len(sys.argv) > 1 else "data/mendi/ble_capture/raw_meditation-2026-05-06.jsonl"

    by_uuid: dict[str, list] = {}
    for rec in iter_jsonl(path):
        by_uuid.setdefault(rec["uuid"], []).append(rec)

    print(f"\n=== Mendi BLE capture decode  ({path}) ===\n")
    for uuid, frames in by_uuid.items():
        print(f"UUID {uuid}  →  {len(frames)} frame(s)")

    # Decode startup frames (bb1, bb5)
    for uuid_suffix, label in [("bb1", "Device-state snapshot (bb1)"),
                                ("bb5", "Session/status header (bb5)")]:
        matches = [u for u in by_uuid if uuid_suffix in u]
        if not matches: continue
        for f in by_uuid[matches[0]]:
            print(f"\n--- {label}  hex={f['hex']}")
            try:
                msg = decode_protobuf(bytes.fromhex(f["hex"]))
                for fid, vals in sorted(msg.items()):
                    print(f"   field {fid:>2}: {vals}")
            except Exception as e:
                print(f"   decode error: {e}")

    # Decode the main stream (bb4)
    bb4_uuid = next((u for u in by_uuid if "bb4" in u), None)
    if bb4_uuid:
        bb4_frames = by_uuid[bb4_uuid]
        print(f"\n=== bb4 main stream ({len(bb4_frames)} frames) ===")
        values = []
        timestamps = []
        for f in bb4_frames:
            v = decode_bb4_frame(f["hex"])
            if v is not None:
                values.append(v)
                timestamps.append(f["t"])
        print(f"Decoded values: n={len(values)}")
        print(f"  min={min(values)}  max={max(values)}  range={max(values)-min(values)}")
        print(f"  mean={statistics.mean(values):.2f}  median={statistics.median(values)}")
        print(f"  stdev={statistics.stdev(values):.2f}")
        # First 20, last 20
        print(f"\n  first 20: {values[:20]}")
        print(f"  last 20:  {values[-20:]}")
        # Inter-frame timing
        from datetime import datetime
        ts = [datetime.fromisoformat(t) for t in timestamps]
        deltas = [(ts[i+1]-ts[i]).total_seconds() for i in range(len(ts)-1)]
        if deltas:
            print(f"\n  inter-frame Δt: min={min(deltas):.3f}s  mean={statistics.mean(deltas):.3f}s  max={max(deltas):.3f}s")
            # Detect gaps (likely device went silent)
            gaps = [(i, d) for i, d in enumerate(deltas) if d > 2.0]
            print(f"  Gaps >2s: {len(gaps)}")
            if gaps:
                print(f"    first 5 gaps: {[(timestamps[i], f'{d:.1f}s') for i, d in gaps[:5]]}")

        # Save decoded CSV
        import csv as _csv
        out_csv = "data/mendi/ble_capture/decoded_meditation-2026-05-06.csv"
        with open(out_csv, "w", newline="") as fh:
            w = _csv.writer(fh)
            w.writerow(["timestamp", "elapsed_s", "value"])
            t0 = ts[0]
            for t, v in zip(ts, values):
                w.writerow([t.isoformat(), (t-t0).total_seconds(), v])
        print(f"\n  Saved → {out_csv}")
