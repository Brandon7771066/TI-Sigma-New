"""
Pass 15 — Oura Ring empirical analysis (Brandon's recent harvest).

Tests we can run on the 12-day daily-records harvest + heart-rate
samples + sleep sessions, with N small but real:

  T1. Per-day HRV (rmssd) summary + day-to-day variability.
  T2. Sleep score lag-1 autocorrelation (LCC-style persistence).
  T3. Cross-correlation of sleep_score(d) -> readiness_score(d+1)
      (bidirectional LCC mini-test).
  T4. Heart-rate sample complexity (sample-entropy proxy = std of
      first differences) day-by-day.
  T5. Workout/session-day vs non-session-day HRV / readiness delta.

All claims with N=12 are exploratory — reported p-values are nominal,
not corrected. Per #69 this is descriptive, not confirmatory.

Source: data/oura_30day_harvest_2026-05-01.json
Seed: 20260509 (deterministic where applicable).
"""
import json
import math
from pathlib import Path

import numpy as np

np.random.seed(20260509)

DATA = Path("data/oura_30day_harvest_2026-05-01.json")
with DATA.open() as f:
    H = json.load(f)

print("=" * 70)
print("Pass 15 — Oura Ring empirical analysis")
print("=" * 70)
md = H["harvest_metadata"]
print(f"Harvest range: {md.get('start_date')} to {md.get('end_date')} "
      f"({md.get('days_requested')} days requested)")
print(f"Daily records: {len(H['daily_records'])}; sleep sessions: {len(H['sleep_sessions'])}; "
      f"workouts: {len(H['workouts'])}; sessions: {len(H['sessions'])}")

# ---------- T1: HRV per day ----------
print()
print("## T1 — Sleep HRV (rmssd) per day")
hrvs = []
for d in H["daily_records"]:
    rmssd = d.get("sleep_hrv_rmssd") or d.get("hrv_rmssd")
    hrvs.append((d.get("date"), rmssd))
have = [(dt, v) for dt, v in hrvs if v is not None]
print(f"  Days with HRV: {len(have)} / {len(hrvs)}")
if have:
    vals = np.array([v for _, v in have], dtype=float)
    print(f"  HRV mean {vals.mean():.1f} ms, std {vals.std(ddof=1):.1f} ms, "
          f"min {vals.min():.1f}, max {vals.max():.1f}")
else:
    # Try sleep_sessions instead
    hrvs2 = []
    for s in H["sleep_sessions"]:
        for k in ("average_hrv", "rmssd", "hrv_average", "average_rmssd"):
            if s.get(k) is not None:
                hrvs2.append((s.get("day"), s.get(k))); break
    print(f"  Falling back to sleep_sessions HRV: found {len(hrvs2)} entries.")
    if hrvs2:
        vals = np.array([v for _, v in hrvs2], dtype=float)
        print(f"  HRV mean {vals.mean():.1f} ms, std {vals.std(ddof=1):.1f} ms, "
              f"min {vals.min():.1f}, max {vals.max():.1f}")
    else:
        # last resort: peek sleep_session keys
        if H["sleep_sessions"]:
            print("  No HRV field found; sleep_session keys:",
                  sorted(H["sleep_sessions"][0].keys())[:25])

# ---------- T2: Sleep score lag-1 autocorrelation ----------
print()
print("## T2 — Sleep-score lag-1 autocorrelation (persistence)")
ss = [d.get("sleep_score") for d in H["daily_records"] if d.get("sleep_score") is not None]
print(f"  Days with sleep_score: {len(ss)}")
if len(ss) >= 5:
    arr = np.array(ss, dtype=float)
    if arr.std() > 0:
        ac1 = np.corrcoef(arr[:-1], arr[1:])[0, 1]
        print(f"  Lag-1 autocorr: r = {ac1:+.3f}  (N pairs = {len(arr)-1})")
        # Fisher-z 95% CI
        if abs(ac1) < 0.999:
            z = 0.5 * math.log((1+ac1)/(1-ac1))
            se = 1/math.sqrt(len(arr)-4) if len(arr) > 4 else float("inf")
            lo = math.tanh(z - 1.96*se); hi = math.tanh(z + 1.96*se)
            print(f"  Fisher-z 95% CI: [{lo:+.3f}, {hi:+.3f}]")
    else:
        print("  Sleep-score variance is zero; cannot compute autocorr.")

# ---------- T3: Sleep(d) -> Readiness(d+1) ----------
print()
print("## T3 — Sleep score(d) -> Readiness score(d+1) lag cross-correlation")
recs = sorted(H["daily_records"], key=lambda r: r.get("date") or "")
ss_seq, rd_seq = [], []
for r in recs:
    ss_seq.append(r.get("sleep_score"))
    rd_seq.append(r.get("readiness_score"))
pairs = [(s, r) for s, r in zip(ss_seq[:-1], rd_seq[1:]) if s is not None and r is not None]
print(f"  Aligned pairs: {len(pairs)}")
if len(pairs) >= 4:
    s_arr = np.array([p[0] for p in pairs], dtype=float)
    r_arr = np.array([p[1] for p in pairs], dtype=float)
    if s_arr.std() > 0 and r_arr.std() > 0:
        r = np.corrcoef(s_arr, r_arr)[0, 1]
        print(f"  Pearson r(sleep_d, readiness_d+1) = {r:+.3f}")

# ---------- T4: HR-sample complexity per day ----------
print()
print("## T4 — Heart-rate sample complexity (std of first differences)")
hrs = H.get("heart_rate_samples", {})
print(f"  Days with HR samples: {len(hrs)}")
day_complexity = []
for day, samples in sorted(hrs.items()):
    vals = []
    if isinstance(samples, list):
        for s in samples:
            if isinstance(s, dict):
                bpm = s.get("bpm") or s.get("value")
                if bpm is not None: vals.append(bpm)
            elif isinstance(s, (int, float)):
                vals.append(s)
    elif isinstance(samples, dict):
        for v in samples.values():
            if isinstance(v, (int, float)): vals.append(v)
    if len(vals) >= 30:
        a = np.array(vals, dtype=float)
        diff = np.diff(a)
        day_complexity.append((day, float(np.std(diff)), len(a)))
print(f"  Days with >=30 HR samples: {len(day_complexity)}")
for day, c, n in day_complexity[:8]:
    print(f"    {day}: std(diff) = {c:6.2f} bpm  (N samples = {n})")
if day_complexity:
    cs = np.array([c for _, c, _ in day_complexity])
    print(f"  Across-day complexity: mean {cs.mean():.2f}, std {cs.std(ddof=1):.2f}, "
          f"CV = {cs.std(ddof=1)/cs.mean():.3f}")

# ---------- T5: Activity-day vs no-activity-day comparison ----------
print()
print("## T5 — Activity-day vs no-activity-day deltas")
activity_days = {w.get("day") for w in H["workouts"]} | {s.get("day") for s in H["sessions"]}
print(f"  Activity-tagged days: {sorted(activity_days)}")
ss_active, ss_quiet = [], []
rd_active, rd_quiet = [], []
for d in H["daily_records"]:
    is_active = d.get("date") in activity_days
    if d.get("sleep_score") is not None:
        (ss_active if is_active else ss_quiet).append(d["sleep_score"])
    if d.get("readiness_score") is not None:
        (rd_active if is_active else rd_quiet).append(d["readiness_score"])
def _summary(label, arr):
    if arr:
        a = np.array(arr, dtype=float)
        print(f"  {label}: N={len(a):3d}  mean={a.mean():6.2f}  std={a.std(ddof=1) if len(a)>1 else 0:5.2f}")
    else:
        print(f"  {label}: N=0")
_summary("Sleep_score   active-days", ss_active)
_summary("Sleep_score   quiet-days ", ss_quiet)
_summary("Readiness     active-days", rd_active)
_summary("Readiness     quiet-days ", rd_quiet)

print()
print("## Honest #69 caveats")
print("  - N=12 daily records: power is poor; treat all numbers as exploratory.")
print("  - HRV fields may be sparse in this harvest window — null-counts shown.")
print("  - Lag-1 autocorr 95% CIs are Fisher-z, parametric; not bootstrap.")
print("  - Activity tagging conflates workouts with passive sessions.")
print("  - These are personal data on a single individual — no MBE-correction needed")
print("    here (the per-individual base-rate IS the unit of analysis).")
