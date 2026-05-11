#!/usr/bin/env python3
"""
Mendi 20-minute neurofeedback / stimulus-validation session — Acer laptop runner.

Uses the already-decoded bb4 protobuf-varint stream (Path B Phase 2 complete,
2026-05-06). Runs a structured 20-min protocol with 4 known stimulus events
(2 mental-arithmetic + 2 breath-hold) interleaved with baseline / recovery
windows so post-hoc you can detect stimulus-locked hemodynamic responses.

Usage on Acer (Windows, terminal):
    py mendi_session_20min.py --address F8:1C:96:82:73:AD

Optional:
    --duration 1200            # default 1200s = 20 min
    --label morning-session    # tag the output files
    --no-prompts               # silent run (no on-screen stimulus prompts)
    --device-mac AA:BB:...     # override default MAC

Outputs (timestamped, written to data/mendi/sessions/):
    <label>_<ts>_raw.jsonl        — raw bb4 hex frames + receive timestamps
    <label>_<ts>_decoded.csv      — t_elapsed_s, raw_value, norm_intensity, phase
    <label>_<ts>_events.json      — schedule + actual event timestamps + summary
    <label>_<ts>_summary.txt      — phase-mean / phase-min / phase-max table

After session: open the CSV in Excel / pandas / etc. Per-phase stats already
in summary.txt; for finer hemodynamic-response detection use mendi_decode.py
or your favourite analysis notebook.

Pre-flight (do once): see MENDI_20MIN_SESSION_RUNBOOK.md
"""
from __future__ import annotations
import argparse, asyncio, csv, json, os, sys, time, statistics
from datetime import datetime
from pathlib import Path

try:
    from bleak import BleakClient, BleakScanner
except ImportError:
    print("ERROR: 'bleak' is required. Install with:", file=sys.stderr)
    print("    py -m pip install bleak", file=sys.stderr)
    sys.exit(1)

# ── Config (matches mendi_ble_client.py post-Phase-2 discovery) ─────────────
DEFAULT_MAC = "F8:1C:96:82:73:AD"
STREAM_CHAR_UUID = "fc3eabb4-c6c4-49e6-922a-6e551c455af5"
STREAM_SVC_UUID  = "fc3eabb0-c6c4-49e6-922a-6e551c455af5"
ADC_FULL_SCALE = 4095.0  # 12-bit ADC hypothesis per MENDI_PATH_B_PHASE_2_COMPLETE

# ── 20-min protocol schedule (seconds from start) ───────────────────────────
# Designed so each stimulus is preceded by ≥60s baseline and followed by ≥120s
# recovery, allowing hemodynamic-response detection by paired comparison.
SCHEDULE = [
    (0,    "BASELINE",            "Sit comfortably. Breathe normally. Eyes soft-focus on a fixed point. Stay still. (2 min)"),
    (120,  "STIM1_ARITHMETIC",    "STIMULUS 1 — Count backwards from 1000 by 7s OUT LOUD for 60 seconds. Begin NOW."),
    (180,  "RECOVERY1",           "Stop counting. Relax. Breathe normally. (2 min recovery)"),
    (300,  "STIM2_BREATHHOLD",    "STIMULUS 2 — Exhale fully, then HOLD your breath for 30-45 seconds. Resume normal breathing when uncomfortable."),
    (360,  "RECOVERY2",           "Recovery — eyes closed, meditation posture, breath natural. (4 min)"),
    (600,  "STIM3_ARITHMETIC",    "STIMULUS 3 (replication) — Count backwards from 999 by 13s OUT LOUD for 60 seconds. Begin NOW."),
    (660,  "RECOVERY3",           "Stop counting. Relax. (2 min)"),
    (780,  "STIM4_BREATHHOLD",    "STIMULUS 4 (replication) — Exhale fully, HOLD 30-45 seconds. Resume."),
    (840,  "CLOSING_MEDITATION",  "Closing meditation — eyes closed, breath natural, no task. (6 min)"),
    (1200, "SESSION_END",         "Session complete. Remove headband. Stop the script with Ctrl+C if it doesn't auto-stop."),
]

def decode_bb4(frame: bytes) -> int | None:
    """Decode one bb4 protobuf varint → int. Returns None if malformed."""
    if len(frame) < 2 or frame[0] != 0x08:
        return None
    val, shift, pos = 0, 0, 1
    while pos < len(frame):
        b = frame[pos]
        val |= (b & 0x7F) << shift
        pos += 1
        if not (b & 0x80):
            return val
        shift += 7
    return None

def phase_at(t: float) -> str:
    """Return the protocol phase name for elapsed seconds t."""
    current = SCHEDULE[0][1]
    for ts, name, _msg in SCHEDULE:
        if t >= ts:
            current = name
        else:
            break
    return current

async def run_session(address: str, duration_s: float, label: str, prompts: bool) -> int:
    out_dir = Path("data/mendi/sessions")
    out_dir.mkdir(parents=True, exist_ok=True)
    ts = datetime.now().strftime("%Y-%m-%dT%H-%M-%S")
    raw_path     = out_dir / f"{label}_{ts}_raw.jsonl"
    decoded_path = out_dir / f"{label}_{ts}_decoded.csv"
    events_path  = out_dir / f"{label}_{ts}_events.json"
    summary_path = out_dir / f"{label}_{ts}_summary.txt"

    print("=" * 60)
    print(f"  Mendi 20-min session — '{label}'")
    print(f"  MAC: {address}")
    print(f"  Duration: {duration_s:.0f} s ({duration_s/60:.1f} min)")
    print(f"  Output dir: {out_dir}")
    print("=" * 60)
    print()
    print("Make sure the Mendi headband is ON, BLINKING, NOT paired in")
    print("Windows Bluetooth, and the Mendi PHONE APP is CLOSED.")
    print()
    input("Press ENTER when ready to connect...")
    print(f"\nConnecting to {address}...")

    async with BleakClient(address) as client:
        if not client.is_connected:
            print("Connection failed. Troubleshoot per runbook §3.")
            return 1
        print("Connected. Subscribing to main stream (bb4)...\n")

        # State
        t0 = time.monotonic()
        samples = []          # (t_elapsed, raw, norm, phase)
        raw_log_f = open(raw_path, "w", encoding="utf-8")
        decoded_log_f = open(decoded_path, "w", newline="", encoding="utf-8")
        csv_w = csv.writer(decoded_log_f)
        csv_w.writerow(["t_elapsed_s", "wallclock", "raw_value", "norm_intensity", "phase"])
        last_print_t = [0.0]
        last_sample_t = [time.monotonic()]
        actual_event_starts = {}

        def on_notify(_handle, data: bytes):
            t_now = time.monotonic()
            t_elapsed = t_now - t0
            wall = datetime.now().isoformat()
            raw_log_f.write(json.dumps({"t": wall, "elapsed_s": round(t_elapsed,3),
                                        "hex": data.hex(), "len": len(data)}) + "\n")
            val = decode_bb4(data)
            if val is None:
                return
            phase = phase_at(t_elapsed)
            norm = val / ADC_FULL_SCALE
            samples.append((t_elapsed, val, norm, phase))
            csv_w.writerow([round(t_elapsed,3), wall, val, round(norm,5), phase])
            last_sample_t[0] = t_now

        await client.start_notify(STREAM_CHAR_UUID, on_notify)

        # Schedule pump: print prompts at scheduled times + live stats every 10 s
        next_event_ix = 0
        try:
            while True:
                t_elapsed = time.monotonic() - t0
                if t_elapsed >= duration_s:
                    break
                # Fire prompts
                while (next_event_ix < len(SCHEDULE)
                       and SCHEDULE[next_event_ix][0] <= t_elapsed):
                    ts_sched, name, msg = SCHEDULE[next_event_ix]
                    actual_event_starts[name] = {
                        "scheduled_s": ts_sched,
                        "actual_elapsed_s": round(t_elapsed, 3),
                        "wallclock": datetime.now().isoformat(),
                    }
                    if prompts:
                        bar = "─" * 60
                        print(f"\n{bar}")
                        print(f"  [t={int(t_elapsed//60):02d}:{int(t_elapsed%60):02d}]  {name}")
                        print(f"  → {msg}")
                        print(f"{bar}")
                    next_event_ix += 1
                # Live stats every 10 s
                if t_elapsed - last_print_t[0] >= 10.0:
                    last_print_t[0] = t_elapsed
                    recent = [s[1] for s in samples if s[0] >= t_elapsed - 10.0]
                    dropout_s = time.monotonic() - last_sample_t[0]
                    if recent:
                        msg = (f"  t={int(t_elapsed//60):02d}:{int(t_elapsed%60):02d}  "
                               f"phase={phase_at(t_elapsed):<22}  "
                               f"n_samp_10s={len(recent):3d}  "
                               f"mean={statistics.mean(recent):7.1f}  "
                               f"min={min(recent):4d}  max={max(recent):4d}")
                        if dropout_s > 5.0:
                            msg += f"  ⚠ DROPOUT {dropout_s:.0f}s"
                        print(msg)
                    else:
                        print(f"  t={int(t_elapsed//60):02d}:{int(t_elapsed%60):02d}  ⚠ NO SAMPLES last 10s "
                              f"(dropout {dropout_s:.0f}s — check forehead contact)")
                await asyncio.sleep(0.5)
        except KeyboardInterrupt:
            print("\nInterrupted by user (Ctrl+C). Saving partial session...")
        finally:
            try: await client.stop_notify(STREAM_CHAR_UUID)
            except Exception: pass
            raw_log_f.close()
            decoded_log_f.close()

        # Per-phase summary
        phase_groups: dict[str, list[int]] = {}
        for _t, val, _n, ph in samples:
            phase_groups.setdefault(ph, []).append(val)

        with summary_path.open("w", encoding="utf-8") as f:
            f.write(f"Mendi 20-min session summary — '{label}' @ {ts}\n")
            f.write(f"Total frames: {len(samples)}\n")
            f.write(f"Total duration: {duration_s:.0f}s\n")
            f.write(f"Effective sample rate: {len(samples)/max(duration_s,1):.2f} Hz\n")
            f.write("\nPer-phase stats (raw bb4 ADC values; lower = more absorption):\n")
            f.write(f"{'phase':<22} {'n':>5} {'mean':>8} {'min':>5} {'max':>5} {'stdev':>7}\n")
            f.write("-" * 60 + "\n")
            for name in [s[1] for s in SCHEDULE if s[1] != "SESSION_END"]:
                vals = phase_groups.get(name, [])
                if vals:
                    sd = statistics.stdev(vals) if len(vals) > 1 else 0.0
                    f.write(f"{name:<22} {len(vals):>5d} {statistics.mean(vals):>8.2f} "
                            f"{min(vals):>5d} {max(vals):>5d} {sd:>7.2f}\n")
                else:
                    f.write(f"{name:<22} {'-':>5} {'-':>8} {'-':>5} {'-':>5} {'-':>7}\n")
            # Stimulus comparison: stimulus mean vs preceding-baseline mean
            f.write("\nStimulus deltas (mean during stim − mean during preceding recovery/baseline):\n")
            comparisons = [
                ("STIM1_ARITHMETIC", "BASELINE"),
                ("STIM2_BREATHHOLD", "RECOVERY1"),
                ("STIM3_ARITHMETIC", "RECOVERY2"),
                ("STIM4_BREATHHOLD", "RECOVERY3"),
            ]
            for stim, base in comparisons:
                sv = phase_groups.get(stim, []); bv = phase_groups.get(base, [])
                if sv and bv:
                    delta = statistics.mean(sv) - statistics.mean(bv)
                    f.write(f"  {stim:<20} − {base:<12} = {delta:+7.2f} ADC units "
                            f"(n_stim={len(sv)}, n_base={len(bv)})\n")
                else:
                    f.write(f"  {stim:<20} − {base:<12} = (insufficient data)\n")
            f.write("\nInterpretation note: per Pass-2 audit, only deltas >|3| ADC units are\n")
            f.write("above device noise floor (~2.4 stdev). Deltas of 5-50 units would be\n")
            f.write("consistent with a real prefrontal hemodynamic response.\n")

        with events_path.open("w", encoding="utf-8") as f:
            json.dump({
                "label": label, "address": address, "started_at": ts,
                "duration_s": duration_s,
                "schedule": [{"scheduled_s": s, "name": n, "prompt": m} for s,n,m in SCHEDULE],
                "actual_event_starts": actual_event_starts,
                "n_frames": len(samples),
                "stream_char_uuid": STREAM_CHAR_UUID,
            }, f, indent=2)

        print("\n" + "=" * 60)
        print("  Session done.")
        print(f"  Raw frames:  {raw_path}")
        print(f"  Decoded CSV: {decoded_path}")
        print(f"  Events:      {events_path}")
        print(f"  Summary:     {summary_path}")
        print("=" * 60)
        print()
        # Echo summary to stdout for convenience
        print(summary_path.read_text())
        return 0

def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__,
        formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--address", default=DEFAULT_MAC, help=f"Mendi MAC (default {DEFAULT_MAC})")
    ap.add_argument("--duration", type=float, default=1200.0, help="seconds (default 1200 = 20 min)")
    ap.add_argument("--label", default="session", help="output file label")
    ap.add_argument("--no-prompts", action="store_true", help="silent run")
    args = ap.parse_args()
    return asyncio.run(run_session(args.address, args.duration, args.label, not args.no_prompts))

if __name__ == "__main__":
    sys.exit(main())
