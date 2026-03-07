"""
Polar H10 → TI Platform Bridge  (Enhanced)
============================================
Run this on your LOCAL machine (Acer), NOT on Replit.

Captures from Polar H10:
  • Heart Rate (BPM)
  • RR Intervals → RMSSD, SDNN, pNN50
  • LF / HF / LF-HF ratio (frequency-domain HRV)
  • Raw ECG waveform at 130 Hz

SETUP:
  1. Install dependencies:
         pip install bleak requests numpy

  2. IMPORTANT — disconnect Polar from Windows BT settings first:
         Windows Settings → Bluetooth → Polar H10 → Remove device

  3. Run:
         python polar_bridge.py

  4. Put on the Polar H10 strap (moisten electrodes first)
"""

import asyncio
import requests
import time
import struct
import math
from datetime import datetime
from collections import deque

try:
    from bleak import BleakScanner, BleakClient
    BLEAK_OK = True
except ImportError:
    print("ERROR: bleak not installed.  Run: pip install bleak requests numpy")
    BLEAK_OK = False

try:
    import numpy as np
    NUMPY_OK = True
except ImportError:
    NUMPY_OK = False
    print("⚠  numpy not found — LF/HF computation disabled.  Run: pip install numpy")

# ─── CONFIG ──────────────────────────────────────────────────────────────────
REPLIT_URL   = "https://5c1b8726-c8b2-4bdf-a0a8-632ec557671f-00-307bfud8cnm36.worf.replit.dev"
SESSION_ID   = "polar_bridge_live"
HR_ENDPOINT  = f"{REPLIT_URL}/api/upload"
ECG_ENDPOINT = f"{REPLIT_URL}/api/polar/upload"

# BLE UUIDs — HR service
HR_SERVICE_UUID     = "0000180d-0000-1000-8000-00805f9b34fb"
HR_MEASUREMENT_UUID = "00002a37-0000-1000-8000-00805f9b34fb"

# BLE UUIDs — Polar Measurement Data (ECG + ACC)
PMD_SERVICE_UUID    = "fb005c80-02e7-f387-1cad-8acd2d8df0c8"
PMD_CP_UUID         = "fb005c81-02e7-f387-1cad-8acd2d8df0c8"   # Control Point
PMD_DATA_UUID       = "fb005c82-02e7-f387-1cad-8acd2d8df0c8"   # Data stream

# HRV window for LF/HF — 5 minutes of RR intervals
HRV_WINDOW_S    = 300        # seconds
RR_BUFFER_MAX   = 3000       # ~5 min at 60 bpm
ECG_BATCH_SIZE  = 260        # 2 seconds of ECG at 130 Hz → send per batch
ECG_FS          = 130.0      # Polar H10 ECG sample rate

# LF/HF frequency bands
LF_LOW, LF_HIGH = 0.04, 0.15
HF_LOW, HF_HIGH = 0.15, 0.40
# ─────────────────────────────────────────────────────────────────────────────

# Shared state
latest_hr      = 0
rr_buffer      = deque(maxlen=RR_BUFFER_MAX)   # (timestamp_s, rr_ms)
ecg_buffer     = []
upload_count   = 0
ecg_count      = 0


# ─── HR PARSING ─────────────────────────────────────────────────────────────

def parse_hr_measurement(data: bytearray):
    if not data:
        return 0, []
    flags        = data[0]
    hr_16bit     = flags & 0x01
    rr_present   = flags & 0x10
    idx = 1
    hr  = struct.unpack_from('<H', data, idx)[0] if hr_16bit else data[idx]
    idx += 2 if hr_16bit else 1
    rr_list = []
    if rr_present:
        while idx + 1 < len(data):
            rr_raw = struct.unpack_from('<H', data, idx)[0]
            rr_list.append(rr_raw / 1024.0 * 1000.0)   # → ms
            idx += 2
    return hr, rr_list


def hr_callback(sender, data: bytearray):
    global latest_hr
    hr, rr_list = parse_hr_measurement(data)
    latest_hr = hr
    now = time.time()
    for rr in rr_list:
        rr_buffer.append((now, rr))


# ─── ECG PARSING ─────────────────────────────────────────────────────────────

def parse_pmd_ecg(data: bytearray):
    """Extract ECG samples from Polar PMD data frame."""
    samples = []
    if len(data) < 10:
        return samples
    # Byte 0: measurement type (0 = ECG)
    if data[0] != 0x00:
        return samples
    # Bytes 1-8: timestamp (little-endian nanoseconds)
    idx = 10   # skip header
    while idx + 2 < len(data):
        # ECG sample: 3 bytes signed little-endian (microvolts)
        raw = data[idx] | (data[idx+1] << 8) | (data[idx+2] << 16)
        if raw & 0x800000:
            raw -= 0x1000000
        samples.append(raw / 1000.0)   # → millivolts
        idx += 3
    return samples


def ecg_callback(sender, data: bytearray):
    global ecg_buffer
    samples = parse_pmd_ecg(bytes(data))
    ecg_buffer.extend(samples)


# ─── HRV ANALYSIS ────────────────────────────────────────────────────────────

def compute_time_domain_hrv(rr_list):
    """RMSSD, SDNN, pNN50 from list of RR intervals in ms."""
    if len(rr_list) < 2:
        return 0.0, 0.0, 0.0
    n      = len(rr_list)
    mean   = sum(rr_list) / n
    sdnn   = math.sqrt(sum((r - mean)**2 for r in rr_list) / (n - 1))
    diffs  = [abs(rr_list[i+1] - rr_list[i]) for i in range(n-1)]
    rmssd  = math.sqrt(sum(d**2 for d in diffs) / len(diffs))
    pnn50  = 100.0 * sum(1 for d in diffs if d > 50) / len(diffs)
    return round(rmssd, 2), round(sdnn, 2), round(pnn50, 1)


def compute_lf_hf(rr_buffer_snapshot):
    """
    Frequency-domain HRV: LF power, HF power, LF/HF ratio.
    Requires numpy. Uses Lomb-Scargle style resampling + FFT.
    Returns (lf, hf, ratio) or (None, None, None) if insufficient data.
    """
    if not NUMPY_OK or len(rr_buffer_snapshot) < 60:
        return None, None, None

    times = np.array([t for t, _ in rr_buffer_snapshot])
    rrs   = np.array([r for _, r in rr_buffer_snapshot])

    # Need at least 30 seconds of data
    if times[-1] - times[0] < 30:
        return None, None, None

    # Resample RR at 4 Hz (standard HRV analysis)
    fs_target = 4.0
    t_start   = times[0]
    t_end     = times[-1]
    t_uniform = np.arange(t_start, t_end, 1.0 / fs_target)
    rr_interp = np.interp(t_uniform, times, rrs)

    # Remove DC, apply Hann window, FFT
    rr_detrend = rr_interp - np.mean(rr_interp)
    window     = np.hanning(len(rr_detrend))
    fft_vals   = np.fft.rfft(rr_detrend * window)
    freqs      = np.fft.rfftfreq(len(rr_detrend), d=1.0/fs_target)
    power      = (np.abs(fft_vals) ** 2) / len(rr_detrend)

    # Integrate power in LF and HF bands
    lf_mask = (freqs >= LF_LOW) & (freqs < LF_HIGH)
    hf_mask = (freqs >= HF_LOW) & (freqs < HF_HIGH)
    lf      = float(np.trapz(power[lf_mask], freqs[lf_mask])) if lf_mask.any() else 0.0
    hf      = float(np.trapz(power[hf_mask], freqs[hf_mask])) if hf_mask.any() else 0.0
    ratio   = round(lf / hf, 3) if hf > 0 else None

    return round(lf, 4), round(hf, 4), ratio


# ─── UPLOAD ──────────────────────────────────────────────────────────────────

def upload_hrv_snapshot():
    global upload_count
    rr_snap   = list(rr_buffer)
    rr_list   = [r for _, r in rr_snap]

    rmssd, sdnn, pnn50 = compute_time_domain_hrv(rr_list)
    lf, hf, ratio      = compute_lf_hf(rr_snap)
    rr_avg = round(sum(rr_list[-10:]) / min(len(rr_list), 10), 1) if rr_list else 0

    payload = {
        "heart_rate":      latest_hr,
        "hr":              latest_hr,
        "rr_interval":     int(rr_avg),
        "rmssd":           rmssd,
        "sdnn":            sdnn,
        "polar_connected": True,
        "muse_connected":  False,
        "device_id":       "POLAR_H10_BRIDGE",
        "session_id":      SESSION_ID,
        "timestamp":       datetime.utcnow().isoformat(),
    }

    # Extended HRV stored in metadata JSON field
    meta = {"pnn50": pnn50, "rr_count": len(rr_list)}
    if lf is not None:
        meta.update({"lf_power": lf, "hf_power": hf, "lf_hf_ratio": ratio})
        payload["lf_power"]   = lf
        payload["hf_power"]   = hf
        payload["lf_hf_ratio"]= ratio
    payload["metadata"] = meta

    try:
        r = requests.post(HR_ENDPOINT, json=payload, timeout=5)
        upload_count += 1
        bar    = "█" * min(int(latest_hr / 5), 20)
        lf_str = f"  LF={lf:.4f} HF={hf:.4f} LF/HF={ratio}" if lf else "  (LF/HF: collecting…)"
        ok     = f"✓ {r.status_code}" if r.status_code in (200, 201) else f"✗ {r.status_code}"
        print(f"  {datetime.now().strftime('%H:%M:%S')}  HR:{latest_hr:3d}bpm [{bar:<20}]"
              f"  RMSSD={rmssd}ms  SDNN={sdnn}ms{lf_str}  {ok}")
    except Exception as e:
        print(f"  {datetime.now().strftime('%H:%M:%S')}  Upload error: {e}")


def upload_ecg_batch(samples):
    global ecg_count
    if not samples:
        return
    payload = {
        "session_id": SESSION_ID,
        "device_id":  "POLAR_H10_BRIDGE",
        "samples":    samples,
        "fs_hz":      ECG_FS,
        "timestamp":  datetime.utcnow().isoformat(),
    }
    try:
        r = requests.post(ECG_ENDPOINT, json=payload, timeout=5)
        ecg_count += len(samples)
        if r.status_code not in (200, 201):
            print(f"  ECG upload error: {r.status_code}")
    except Exception as e:
        print(f"  ECG upload error: {e}")


# ─── ECG START COMMAND ───────────────────────────────────────────────────────

ECG_START_CMD = bytes([
    0x02,   # start stream
    0x00,   # ECG measurement type
    0x00, 0x01,           # sample rate setting (unused for ECG start)
    0x82, 0x00, 0x01, 0x01, 0x0E, 0x00   # ECG at 130Hz
])


async def enable_ecg(client):
    """Write start command to PMD Control Point to begin ECG stream."""
    try:
        await client.write_gatt_char(PMD_CP_UUID, ECG_START_CMD, response=True)
        await client.start_notify(PMD_DATA_UUID, ecg_callback)
        print("  ECG stream started (130 Hz) ✓")
        return True
    except Exception as e:
        print(f"  ECG not available on this firmware: {e}")
        return False


# ─── MAIN ────────────────────────────────────────────────────────────────────

async def find_polar():
    print("\n  Scanning for Polar H10 (10 seconds)...")
    devices = await BleakScanner.discover(timeout=10.0)
    for d in devices:
        if d.name and "Polar" in d.name:
            print(f"  Found: {d.name}  [{d.address}]")
            return d.address
    return None


async def run():
    global ecg_buffer

    if not BLEAK_OK:
        return

    print("=" * 62)
    print("  Polar H10 → TI Platform Bridge  (HR + HRV + LF/HF + ECG)")
    print("=" * 62)
    print(f"  HR/HRV endpoint : {HR_ENDPOINT}")
    print(f"  ECG endpoint    : {ECG_ENDPOINT}")
    print(f"  LF/HF analysis  : {'ENABLED' if NUMPY_OK else 'DISABLED (install numpy)'}")
    print("=" * 62)

    address = await find_polar()
    if not address:
        print("\n  ERROR: Polar H10 not found.")
        print("  Make sure:")
        print("    1. Polar H10 is on (moisten strap, wear it)")
        print("    2. Removed from Windows BT Settings → Remove device")
        print("    3. Within ~3 metres of the laptop")
        return

    print(f"\n  Connecting to {address}...")
    try:
        async with BleakClient(address, timeout=15.0) as client:
            if not client.is_connected:
                print("  ERROR: Could not connect.")
                return

            print("  CONNECTED ✓")
            await client.start_notify(HR_MEASUREMENT_UUID, hr_callback)
            print("  HR stream started ✓")

            ecg_enabled = await enable_ecg(client)
            print()

            tick = 0
            while client.is_connected:
                await asyncio.sleep(2)
                tick += 1

                # Upload HR + HRV snapshot every 2 seconds
                if latest_hr > 0:
                    upload_hrv_snapshot()

                # Upload ECG batch every 2 seconds
                if ecg_enabled and len(ecg_buffer) >= ECG_BATCH_SIZE:
                    batch       = ecg_buffer[:ECG_BATCH_SIZE]
                    ecg_buffer  = ecg_buffer[ECG_BATCH_SIZE:]
                    upload_ecg_batch(batch)
                    print(f"  ECG: {ecg_count} samples sent total")

                if latest_hr == 0:
                    print(f"  {datetime.now().strftime('%H:%M:%S')}  Waiting for HR signal...")

    except Exception as e:
        err = str(e)
        print(f"\n  Connection error: {err}")
        if any(k in err.lower() for k in ("access", "in use", "winrt", "denied")):
            print("\n  FIX: Windows BT is still holding Polar H10.")
            print("       Settings → Bluetooth → Polar H10 → Remove device → retry")


def main():
    try:
        asyncio.run(run())
    except KeyboardInterrupt:
        print(f"\n\n  Stopped.  {upload_count} HR uploads | {ecg_count} ECG samples sent.")


if __name__ == "__main__":
    main()
