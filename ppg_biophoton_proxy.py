"""
PPG Biophoton-Signature Proxy
==============================

Computes a "biophoton-signature proxy" from Oura PPG-derived BPM samples.

HONEST SCOPE (asymmetric-standards #69)
---------------------------------------
This module does NOT measure photons emitted by DNA. It does NOT replicate
GDV/Bio-Well's claimed gas-discharge-around-fingertip measurement. It does
NOT validate URB #826's biophoton/EM-DNA carrier hypothesis.

What it DOES:
- Reads Oura's BPM samples (5-min awake / 30-sec sleep resolution from the
  ring's optical PPG sensor)
- Computes time-domain, frequency-domain, and nonlinear-complexity features
  from the BPM time series
- Aggregates these features into a single scalar in [0, 1] called
  `ppg_biophoton_signature`
- Maps the components to the GILE dimensions per the prior PPG paper
  (papers/SKIN_CONDUCTANCE_GDV_REPLACEMENT_EAV_TCM.md, §3 "PPG for
  Meridian Assessment")

The justification for calling this a "biophoton-signature proxy" rests on
the prior paper's argument: PPG measures peripheral microvascular blood-flow
dynamics, which integrate autonomic, vascular, endothelial, and (per the
URB #826 hypothesis) potentially EM-coupled DNA-resonance signals. Whether
that last component is real is what URB #826 + Phase B are trying to test.

The proxy is therefore a **structural placeholder** for the biophoton
component in R_intra_em — analogous to how `cpg_promoter_density` is a
structural placeholder for personal CpG content.

Limitations explicitly stated:
- Oura's API exposes BPM only, not raw PPG waveform → we cannot compute
  optical morphology features (pulse-shape area, dicrotic notch position,
  etc.) that GDV-replacement papers normally use
- BPM samples are inhomogeneously sampled (5 min awake, 30 sec sleep,
  workout fills); we resample to 1-min uniform grid before analysis
- Sample entropy, DFA, etc. require N≥100 samples; days with sparse
  ring wear may not have enough data → component returns None
"""

from __future__ import annotations
import json
import math
import os
import sys
from dataclasses import dataclass, asdict
from datetime import datetime, date
from typing import Dict, List, Optional, Tuple, Any

import numpy as np


# ────────────────────────────────────────────────────────────────────────────
# Feature computations
# ────────────────────────────────────────────────────────────────────────────

def _resample_to_minute_grid(samples: List[Dict[str, Any]]) -> Optional[np.ndarray]:
    """
    Resample BPM samples to a uniform 1-min grid via forward-fill.
    Returns None if < 60 samples (less than 1 hour of meaningful coverage).
    """
    if len(samples) < 60:
        return None
    parsed = []
    for s in samples:
        try:
            ts = datetime.fromisoformat(s["timestamp"].replace("Z", "+00:00"))
            parsed.append((ts, float(s["bpm"])))
        except Exception:
            continue
    if len(parsed) < 60:
        return None
    parsed.sort(key=lambda x: x[0])

    t0 = parsed[0][0]
    t_end = parsed[-1][0]
    n_minutes = int((t_end - t0).total_seconds() / 60) + 1
    if n_minutes < 60:
        return None

    grid = np.full(n_minutes, np.nan)
    for ts, bpm in parsed:
        idx = int((ts - t0).total_seconds() / 60)
        if 0 <= idx < n_minutes:
            grid[idx] = bpm

    # Forward-fill, then back-fill any leading NaNs
    last = np.nan
    for i in range(n_minutes):
        if np.isnan(grid[i]):
            grid[i] = last
        else:
            last = grid[i]
    if np.isnan(grid[0]):
        first_valid = next((g for g in grid if not np.isnan(g)), np.nan)
        if np.isnan(first_valid):
            return None
        for i in range(n_minutes):
            if np.isnan(grid[i]):
                grid[i] = first_valid
            else:
                break
    return grid


def time_domain_features(bpm_grid: np.ndarray) -> Dict[str, float]:
    """RMSSD-from-BPM, SDNN-from-BPM, mean, std on minute-resampled grid."""
    diffs = np.diff(bpm_grid)
    return {
        "mean_bpm":  float(np.mean(bpm_grid)),
        "std_bpm":   float(np.std(bpm_grid)),
        "rmssd_bpm": float(np.sqrt(np.mean(diffs ** 2))),
        "sdnn_bpm":  float(np.std(bpm_grid)),
    }


def frequency_domain_features(bpm_grid: np.ndarray) -> Dict[str, float]:
    """
    Welch-style power spectral density on the 1-min-grid BPM series.
    Bands (cycles/min, since fs=1/min):
      VLF: 0.0033–0.04  (3.3–40 mHz   → 5–60 sec rhythm? at 1-min res this is
           the LF lower band; we approximate)
      LF:  0.04–0.15
      HF:  0.15–0.40
    Returns LF/HF ratio + spectral centroid as proxies for autonomic balance
    and rhythmic complexity.
    """
    from numpy.fft import rfft, rfftfreq
    n = len(bpm_grid)
    detrended = bpm_grid - np.mean(bpm_grid)
    # Hann window
    window = 0.5 - 0.5 * np.cos(2 * np.pi * np.arange(n) / max(n - 1, 1))
    spectrum = np.abs(rfft(detrended * window)) ** 2
    freqs = rfftfreq(n, d=1.0)  # cycles per minute

    def band_power(lo, hi):
        mask = (freqs >= lo) & (freqs < hi)
        if not mask.any():
            return 0.0
        return float(np.sum(spectrum[mask]))

    lf = band_power(0.04, 0.15)
    hf = band_power(0.15, 0.40)
    total_power = float(np.sum(spectrum[1:]))  # exclude DC
    centroid = (
        float(np.sum(freqs * spectrum) / np.sum(spectrum))
        if np.sum(spectrum) > 0
        else 0.0
    )
    return {
        "lf_power": lf,
        "hf_power": hf,
        "lf_hf_ratio":     (lf / hf) if hf > 1e-9 else float("inf"),
        "total_power":     total_power,
        "spectral_centroid": centroid,
    }


def sample_entropy(series: np.ndarray, m: int = 2, r_factor: float = 0.2) -> Optional[float]:
    """
    Sample entropy (Richman & Moorman 2000) — measures regularity of a time
    series. Higher = more complex/irregular. r_factor × std is the tolerance.
    Returns None if series too short or std too small.
    """
    n = len(series)
    if n < 30:
        return None
    r = r_factor * float(np.std(series))
    if r < 1e-9:
        return None

    def _phi(mm):
        templates = np.array([series[i:i + mm] for i in range(n - mm)])
        if len(templates) < 2:
            return None
        # count pairs whose Chebyshev distance <= r (excluding self-match)
        c = 0
        for i in range(len(templates)):
            dists = np.max(np.abs(templates - templates[i]), axis=1)
            c += int(np.sum(dists <= r)) - 1  # subtract self-match
        return c / (len(templates) * (len(templates) - 1))

    a = _phi(m + 1)
    b = _phi(m)
    if a is None or b is None or a <= 0 or b <= 0:
        return None
    return float(-math.log(a / b))


def hurst_exponent(series: np.ndarray) -> Optional[float]:
    """
    Hurst exponent via rescaled-range (R/S) method.
    H ≈ 0.5 → random walk; H > 0.5 → persistent (long memory);
    H < 0.5 → anti-persistent.
    """
    n = len(series)
    if n < 64:
        return None
    lags = [4, 8, 16, 32, 64]
    if n >= 128: lags.append(128)
    if n >= 256: lags.append(256)
    rs_values = []
    for lag in lags:
        if n < lag * 2:
            continue
        rs = []
        for start in range(0, n - lag, lag):
            chunk = series[start:start + lag]
            mean = np.mean(chunk)
            cumdev = np.cumsum(chunk - mean)
            rng = np.max(cumdev) - np.min(cumdev)
            std = np.std(chunk)
            if std > 1e-9:
                rs.append(rng / std)
        if rs:
            rs_values.append((math.log(lag), math.log(np.mean(rs))))
    if len(rs_values) < 2:
        return None
    xs, ys = zip(*rs_values)
    h, _intercept = np.polyfit(xs, ys, 1)
    return float(h)


def spectral_slope_one_over_f(bpm_grid: np.ndarray) -> Optional[float]:
    """
    Slope of log-log power spectrum — the "1/f" exponent.
    A slope of -1 corresponds to pink noise (canonical 1/f); -2 → brown noise.
    The brain literature (Voytek 2015, Donoghue 2020) treats 1/f-like activity
    as an indicator of asynchronous neural activity and excitation/inhibition
    balance. Applied to BPM here as an autonomic-rhythmic-complexity proxy.
    """
    from numpy.fft import rfft, rfftfreq
    n = len(bpm_grid)
    if n < 64:
        return None
    detrended = bpm_grid - np.mean(bpm_grid)
    spectrum = np.abs(rfft(detrended)) ** 2
    freqs = rfftfreq(n, d=1.0)
    mask = (freqs > 0) & (spectrum > 1e-12)
    if mask.sum() < 8:
        return None
    log_f = np.log10(freqs[mask])
    log_p = np.log10(spectrum[mask])
    slope, _intercept = np.polyfit(log_f, log_p, 1)
    return float(slope)


# ────────────────────────────────────────────────────────────────────────────
# Aggregation: GILE mapping → biophoton-signature scalar
# ────────────────────────────────────────────────────────────────────────────

def _norm(value: Optional[float], lo: float, hi: float) -> Optional[float]:
    """Min-max normalize to [0, 1]; None if value is None or NaN."""
    if value is None or (isinstance(value, float) and (math.isnan(value) or math.isinf(value))):
        return None
    return float(min(1.0, max(0.0, (value - lo) / max(hi - lo, 1e-9))))


@dataclass
class PPGBiophotonSignature:
    """Per-day PPG biophoton-signature with diagnostics."""
    day: str
    n_samples: int
    n_minutes: int

    # Raw features
    mean_bpm: Optional[float] = None
    std_bpm: Optional[float] = None
    rmssd_bpm: Optional[float] = None
    lf_hf_ratio: Optional[float] = None
    spectral_centroid: Optional[float] = None
    sample_entropy_val: Optional[float] = None
    hurst: Optional[float] = None
    spectral_slope: Optional[float] = None

    # Normalized in [0, 1] (GILE-mapped)
    g_stability: Optional[float] = None    # 1 - normalized std (low variance = high G)
    i_complexity: Optional[float] = None   # normalized sample entropy
    l_variability: Optional[float] = None  # normalized RMSSD-from-BPM (autonomic flexibility)
    e_environment: Optional[float] = None  # normalized hurst (long-memory persistence)

    # Composite signature
    ppg_biophoton_signature: Optional[float] = None
    note: str = ""


def compute_signature_for_day(day: str, samples: List[Dict[str, Any]]) -> PPGBiophotonSignature:
    """Compute the per-day biophoton-signature scalar from raw HR samples.

    Time-domain + frequency-domain features → forward-filled minute grid
        (acceptable: these are robust to flat-fill at low frequencies)
    Nonlinear features (sample entropy, Hurst, 1/f slope) → RAW BPM values
        (forward-fill saturates both upward, biasing toward 0 entropy and
        1.0 Hurst; raw samples preserve actual variability structure).
    """
    n = len(samples)
    grid = _resample_to_minute_grid(samples)

    if grid is None:
        return PPGBiophotonSignature(
            day=day, n_samples=n, n_minutes=0,
            note="insufficient samples (<60 min coverage)"
        )

    raw_bpm = np.array(
        [float(s["bpm"]) for s in samples if "bpm" in s],
        dtype=float
    )

    td = time_domain_features(grid)
    fd = frequency_domain_features(grid)
    # Nonlinear features on RAW samples (avoid forward-fill bias)
    se = sample_entropy(raw_bpm) if len(raw_bpm) >= 30 else None
    hu = hurst_exponent(raw_bpm) if len(raw_bpm) >= 64 else None
    ss = spectral_slope_one_over_f(raw_bpm) if len(raw_bpm) >= 64 else None

    # GILE normalization bounds — derived from observed BPM-series statistics
    # on Brandon's actual Oura data (n=13 days, calibrated 2026-05-01).
    # NOT from NN-interval HRV literature (Shaffer & Ginsberg 2017) because
    # Oura BPM samples are already a smoothed measure with different
    # statistical properties than R-R intervals from ECG.
    #   std_bpm 2-15 typical for daily wear (dominated by activity transitions)
    #   rmssd_bpm 1-12 typical (smaller than ECG RMSSD due to BPM aggregation)
    #   sample_entropy 0.05-0.50 typical for BPM (much lower than NN entropy)
    #   hurst 0.70-1.00 typical for BPM (BPM is highly persistent due to
    #     activity-state autocorrelation; near-1.0 = pure trend, ~0.7 = mixed)
    g = _norm(td["std_bpm"], 2.0, 15.0)
    g = (1.0 - g) if g is not None else None  # invert: low variance = high stability
    i = _norm(se, 0.05, 0.50)
    l = _norm(td["rmssd_bpm"], 1.0, 12.0)
    e = _norm(hu, 0.70, 1.00)

    available = [x for x in (g, i, l, e) if x is not None]
    sig = float(np.mean(available)) if available else None

    return PPGBiophotonSignature(
        day=day, n_samples=n, n_minutes=len(grid),
        mean_bpm=td["mean_bpm"], std_bpm=td["std_bpm"], rmssd_bpm=td["rmssd_bpm"],
        lf_hf_ratio=fd["lf_hf_ratio"] if math.isfinite(fd["lf_hf_ratio"]) else None,
        spectral_centroid=fd["spectral_centroid"],
        sample_entropy_val=se, hurst=hu, spectral_slope=ss,
        g_stability=g, i_complexity=i, l_variability=l, e_environment=e,
        ppg_biophoton_signature=sig,
        note=f"computed from {len(grid)} 1-min bins ({len(available)}/4 GILE components available)"
    )


def compute_signatures_from_harvest(harvest_path: str) -> Dict[str, PPGBiophotonSignature]:
    """Load Oura harvest JSON → return dict day → biophoton-signature."""
    with open(harvest_path) as f:
        h = json.load(f)
    out: Dict[str, PPGBiophotonSignature] = {}
    for day, samples in h["heart_rate_samples"].items():
        out[day] = compute_signature_for_day(day, samples)
    return out


# ────────────────────────────────────────────────────────────────────────────
# CLI
# ────────────────────────────────────────────────────────────────────────────

def main():
    import argparse
    p = argparse.ArgumentParser()
    p.add_argument("--harvest", default=None,
                   help="Path to oura harvest JSON (default: latest in data/)")
    p.add_argument("--output", default=None,
                   help="Output path for signatures JSON (default: data/ppg_biophoton_signatures_<date>.json)")
    args = p.parse_args()

    if args.harvest is None:
        candidates = sorted(
            f for f in os.listdir("data")
            if f.startswith("oura_30day_harvest_") and f.endswith(".json")
        )
        if not candidates:
            print("❌ No harvest file found. Run oura_full_metrics_harvester.py first.")
            sys.exit(1)
        args.harvest = os.path.join("data", candidates[-1])
    print(f"Loading harvest: {args.harvest}")

    sigs = compute_signatures_from_harvest(args.harvest)

    print("\n━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━")
    print("PPG BIOPHOTON-SIGNATURE PROXY — per-day results")
    print("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━")
    print(f"{'day':12s} {'n':>5s} {'min':>5s} {'sig':>7s} {'G':>6s} {'I':>6s} {'L':>6s} {'E':>6s}  note")
    print("─" * 96)
    for day in sorted(sigs):
        s = sigs[day]
        def f(x): return f"{x:6.3f}" if x is not None else "  -   "
        sig_str = f"{s.ppg_biophoton_signature:7.4f}" if s.ppg_biophoton_signature is not None else "   -   "
        print(f"{s.day:12s} {s.n_samples:5d} {s.n_minutes:5d} {sig_str} "
              f"{f(s.g_stability)} {f(s.i_complexity)} {f(s.l_variability)} {f(s.e_environment)}  {s.note}")

    if args.output is None:
        args.output = os.path.join(
            "data", f"ppg_biophoton_signatures_{date.today().isoformat()}.json"
        )
    os.makedirs(os.path.dirname(args.output) or ".", exist_ok=True)
    payload = {
        "generated_at": datetime.utcnow().isoformat() + "Z",
        "source_harvest": args.harvest,
        "honest_scope": (
            "PPG biophoton-signature proxy is computed from Oura BPM samples "
            "(NOT raw PPG waveform; NOT actual photon emission). Components "
            "are autonomic-cardiovascular complexity features mapped to GILE. "
            "See ppg_biophoton_proxy.py module docstring for full caveats."
        ),
        "signatures": {day: asdict(s) for day, s in sigs.items()},
    }
    with open(args.output, "w") as f:
        json.dump(payload, f, indent=2, default=str)
    print(f"\n✅ Written: {args.output}")


if __name__ == "__main__":
    main()
