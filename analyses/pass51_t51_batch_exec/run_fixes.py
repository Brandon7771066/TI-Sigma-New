"""
Fixes for T51-2 (β₁ proxy returned 0 — needed wider ε grid and proper formula)
and T51-5 (Polar JSON path is .exercises[0].samples.samples[0].values, where
that single channel appears to be 1-Hz HR in bpm).
Updates results.json in-place with T51_2_v2 and T51_5_v2 keys.
"""
import json, math
from pathlib import Path
import numpy as np
from scipy import signal as sps
from scipy.spatial.distance import pdist, squareform

OUT = Path(__file__).parent
RESULTS = json.loads((OUT / "results.json").read_text())
np.random.seed(51)

# ============== T51-2 v2: PROPER β₁ PROXY WITH WIDER ε SWEEP ==============
def beta1_proper(points, eps):
    """
    For 1-skeleton Vietoris-Rips at radius eps:
      β₁ = E - V + #components - rank(boundary_2)
    For our proxy we use β₁ ≈ #independent_cycles in graph
                       = E - V + #components  (cyclomatic number of 1-skeleton)
    Then subtract triangle-fillings as an upper bound on 2-boundaries.
    """
    N = len(points)
    D = squareform(pdist(points))
    A = (D < eps) & (D > 0)
    n_edges = int(A.sum() // 2)
    # Connected components
    visited = [False]*N; n_comp = 0
    for s in range(N):
        if visited[s]: continue
        n_comp += 1
        stack = [s]
        while stack:
            u = stack.pop()
            if visited[u]: continue
            visited[u] = True
            for v in np.where(A[u])[0]:
                if not visited[v]: stack.append(v)
    cyclomatic = n_edges - N + n_comp
    # Triangle count (filled 2-simplices)
    # A[i,j] & A[j,k] & A[i,k]
    n_tri = int(np.trace(A.astype(int) @ A.astype(int) @ A.astype(int)) // 6)
    b1_lower = max(0, cyclomatic - n_tri)
    return {"V": N, "E": n_edges, "F": n_tri, "comp": n_comp,
            "cyclomatic": cyclomatic, "b1_lower": b1_lower}

# Generate two competing point clouds
N_TOTAL = 415; DIM = 8
gauss = np.random.randn(N_TOTAL, DIM)
# H1-prox: 6 distinct loop-generating clusters
centers = np.random.randn(6, DIM); centers /= np.linalg.norm(centers, axis=1, keepdims=True)
assigns = np.random.randint(0, 6, N_TOTAL)
loop6 = centers[assigns] + 0.15 * np.random.randn(N_TOTAL, DIM)

# Wider ε sweep (percentiles of pairwise distance distribution)
all_d_g = pdist(gauss); all_d_l = pdist(loop6)
sweep_g = []; sweep_l = []
for pct in [5, 10, 15, 20, 25, 30, 35, 40, 50, 60]:
    eps_g = float(np.percentile(all_d_g, pct))
    eps_l = float(np.percentile(all_d_l, pct))
    rg = beta1_proper(gauss, eps_g)
    rl = beta1_proper(loop6, eps_l)
    sweep_g.append({"pct": pct, "eps": eps_g, **rg})
    sweep_l.append({"pct": pct, "eps": eps_l, **rl})

# Repeat across 20 random seeds for both H0 and H1
def max_b1_over_sweep(pts):
    d = pdist(pts)
    best = 0
    for pct in [5,10,15,20,25,30,35,40,50,60]:
        eps = float(np.percentile(d, pct))
        r = beta1_proper(pts, eps)
        if r["b1_lower"] > best: best = r["b1_lower"]
    return best

null_b1s = []; h1_b1s = []
for seed in range(20):
    rng = np.random.RandomState(100 + seed)
    g = rng.randn(N_TOTAL, DIM)
    null_b1s.append(max_b1_over_sweep(g))
    cs = rng.randn(6, DIM); cs /= np.linalg.norm(cs, axis=1, keepdims=True)
    ass = rng.randint(0, 6, N_TOTAL)
    h1 = cs[ass] + 0.15 * rng.randn(N_TOTAL, DIM)
    h1_b1s.append(max_b1_over_sweep(h1))

RESULTS["T51_2_v2_tda_null"] = {
    "N_total": N_TOTAL, "dim": DIM,
    "single_run_sweep_gauss": sweep_g,
    "single_run_sweep_loop6": sweep_l,
    "null_b1_dist_n20": null_b1s,
    "h1_b1_dist_n20": h1_b1s,
    "null_mean_max_b1": float(np.mean(null_b1s)),
    "null_p95_max_b1": float(np.percentile(null_b1s, 95)),
    "h1_mean_max_b1": float(np.mean(h1_b1s)),
    "h1_p5_max_b1": float(np.percentile(h1_b1s, 5)),
    "n_null_runs_b1_geq_6": int(sum(1 for x in null_b1s if x >= 6)),
    "n_h1_runs_b1_geq_6":   int(sum(1 for x in h1_b1s   if x >= 6)),
    "bok_topology_reported_b1": 6,
    "interpretation": (
        "Pure 8D Gaussian noise (H0) max-β₁-over-ε-sweep distribution vs. "
        "6-cluster structured cloud (H1). If null_p95 >= 6 then β₁=6 cannot "
        "discriminate the BOK topology from random Gaussian noise at this "
        "N=415 in dim=8. If h1_p5 << 6 then the H1 structure also fails to "
        "reliably hit β₁=6 — the value is filtration-scale-sensitive."
    ),
}
print(f"[T51-2 v2] null b1 max: mean={np.mean(null_b1s):.1f} p95={np.percentile(null_b1s,95):.1f}")
print(f"[T51-2 v2] H1 b1 max: mean={np.mean(h1_b1s):.1f} p5={np.percentile(h1_b1s,5):.1f}")
print(f"[T51-2 v2] null ≥6: {RESULTS['T51_2_v2_tda_null']['n_null_runs_b1_geq_6']}/20, H1 ≥6: {RESULTS['T51_2_v2_tda_null']['n_h1_runs_b1_geq_6']}/20")

# ================ T51-5 v2: PROPER POLAR JSON HR EXTRACTION ================
polar_dir = Path("data/polar_h10_export")
session_files = sorted(polar_dir.glob("training-session-*.json"))

def extract_hr_polar(jpath):
    d = json.loads(jpath.read_text())
    try:
        samples = d['exercises'][0]['samples']['samples']
        for ch in samples:
            vals = ch.get('values', [])
            if vals and len(vals) > 30:
                arr = np.array(vals, dtype=float)
                # HR sanity: median should be between 40 and 200
                med = np.median(arr[arr > 30])
                if 40 <= med <= 200:
                    return arr, ch.get('sampleType', '?')
        # Fallback: take longest channel
        longest = max(samples, key=lambda c: len(c.get('values', [])))
        return np.array(longest['values'], dtype=float), longest.get('sampleType', '?')
    except (KeyError, IndexError):
        return None, None

def lf_hf(hr, fs=1.0):
    hr = hr[(hr > 30) & (hr < 250)]  # clean obvious artifacts
    if len(hr) < 256: return None
    # Detrend and use Welch
    hr = sps.detrend(hr)
    nperseg = min(512, len(hr)//2)
    f, P = sps.welch(hr, fs=fs, nperseg=nperseg)
    lf = (f >= 0.04) & (f < 0.15)
    hf = (f >= 0.15) & (f < 0.40)
    LF = float(np.trapezoid(P[lf], f[lf])) if lf.any() else 0
    HF = float(np.trapezoid(P[hf], f[hf])) if hf.any() else 0
    return {"n": len(hr), "lf": LF, "hf": HF, "lf_hf_ratio": LF/HF if HF > 0 else None,
            "median_bpm": float(np.median(hr)), "std_bpm": float(np.std(hr))}

session_results_v2 = []
for sf in session_files:
    hr, stype = extract_hr_polar(sf)
    if hr is None:
        session_results_v2.append({"file": sf.name[:60], "status": "no series"})
        continue
    r = lf_hf(hr, fs=1.0)
    if r is None:
        session_results_v2.append({"file": sf.name[:60], "status": "too short", "n": len(hr)})
        continue
    r["file"] = sf.name[:60]
    r["sampleType"] = stype
    session_results_v2.append(r)

ratios_v2 = [s["lf_hf_ratio"] for s in session_results_v2
             if isinstance(s, dict) and s.get("lf_hf_ratio")]
RESULTS["T51_5_v2_polar_lf_hf"] = {
    "n_sessions_found": len(session_files),
    "n_sessions_analyzed": len(ratios_v2),
    "lf_hf_ratios": ratios_v2,
    "mean_lf_hf": float(np.mean(ratios_v2)) if ratios_v2 else None,
    "median_lf_hf": float(np.median(ratios_v2)) if ratios_v2 else None,
    "std_lf_hf": float(np.std(ratios_v2)) if ratios_v2 else None,
    "urb_699_P3_predicted": 2.0,
    "n_within_pm25pct_of_2": int(sum(1 for r in ratios_v2 if 1.5 <= r <= 2.5)) if ratios_v2 else 0,
    "per_session": session_results_v2,
    "caveat": (
        "Polar H10 'training-session' export gives 1-Hz HR (bpm) samples, "
        "NOT RR-interval (ms) series. Strict HRV LF/HF needs RR intervals. "
        "The 1-Hz bpm-derived spectrum has frequency content but with "
        "different amplitude calibration than standard HRV. Therefore this "
        "is SUGGESTIVE-PILOT only. urb_699 P3 prediction of 2:1 LF/HF in "
        "'deep coherence' states is not directly testable without (a) RR "
        "intervals, (b) labeled coherence-state segments. Brandon-export "
        "of RR data would upgrade this to a clean test."
    ),
}
print(f"[T51-5 v2] {len(ratios_v2)}/{len(session_files)} sessions analyzed")
if ratios_v2:
    print(f"[T51-5 v2] LF/HF mean={np.mean(ratios_v2):.2f} median={np.median(ratios_v2):.2f} "
          f"n_within_pm25pct_of_2={RESULTS['T51_5_v2_polar_lf_hf']['n_within_pm25pct_of_2']}/{len(ratios_v2)}")

(OUT / "results.json").write_text(json.dumps(RESULTS, indent=2, default=str))
print("[DONE] results.json updated with v2 keys.")
