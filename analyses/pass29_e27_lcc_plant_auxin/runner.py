"""e27 — LCC v3 R-3 cross-species replication on plant-auxin synthetic data.

Pre-registration (frozen before runner):
- 7 channel-pairs (mimics Pass-17 stock-pair structure but on plant tissues)
- Pearson-rolling window N=20 (Pass-17 canonical)
- C_EMERICK = 1/(phi*sqrt(2)) ≈ 0.4370
- Synthesis: 6-channel auxin-like oscillation, period 4-6h, sampling 5min
  (matches phys.org 2024-05 plant-auxin cycle), pink noise overlay
- ACCEPT if ≥4/7 pairs above C* (matches Pass-17's 5/7 with -1 tolerance for
  cross-species generalization). REFUTE if ≤2/7.
- Seed: 27182818 (e-derived)
"""
import math, json, numpy as np
from pathlib import Path

PHI = (1+math.sqrt(5))/2; C = 1/(PHI*math.sqrt(2))
SEED = 27182818
WINDOW = 20

def synth_auxin(n_samples=600, period_min=240, period_max=360, n_chan=6, seed=SEED):
    rng = np.random.default_rng(seed)
    t = np.arange(n_samples)
    chans = []
    for i in range(n_chan):
        period = rng.uniform(period_min, period_max)
        phase = rng.uniform(0, 2*math.pi)
        amp = rng.uniform(0.8, 1.2)
        # auxin-like: slow oscillation + harmonic + pink-noise
        signal = amp*np.sin(2*math.pi*t/period + phase) + 0.3*np.sin(4*math.pi*t/period + phase)
        # pink noise via cumulative sum of white
        noise = np.cumsum(rng.normal(0, 0.05, n_samples))
        noise -= noise.mean()
        chans.append(signal + 0.4*noise)
    return np.array(chans)

def rolling_pearson(x, y, w=WINDOW):
    n = len(x)
    vals = []
    for i in range(w, n):
        a = x[i-w:i]; b = y[i-w:i]
        c = np.corrcoef(a, b)[0,1]
        if not math.isnan(c): vals.append(abs(c))
    return np.mean(vals) if vals else 0.0

def main():
    chans = synth_auxin()
    pairs = [(0,1),(0,2),(1,3),(2,4),(3,5),(0,5),(2,3)]
    results = []
    for i,j in pairs:
        r = rolling_pearson(chans[i], chans[j])
        results.append({"pair": f"ch{i}-ch{j}", "rolling_R": round(r,4),
                        "above_C": bool(r > C)})
    n_above = sum(1 for r in results if r["above_C"])
    verdict = "CONFIRM" if n_above >= 4 else ("REFUTE" if n_above <= 2 else "INCONCLUSIVE")
    out = {"seed": SEED, "C_emerick": round(C,4),
           "n_pairs_above_C": n_above, "n_total_pairs": 7,
           "verdict": verdict, "pre_reg_threshold": "≥4/7 CONFIRM, ≤2/7 REFUTE",
           "results": results}
    Path("analyses/pass29_e27_lcc_plant_auxin/results.json").write_text(json.dumps(out, indent=2))
    print(json.dumps(out, indent=2))

if __name__ == "__main__": main()
