"""
Pass 26 — w25 discharge.
BOK Crystal centralization recomputed under THREE alternative edge-weight
schemes (Pass-25 §1 Reading 2):
  W1: ring-radius-weighted (inner rings more important)
  W2: inverse-ring-radius-weighted (outer rings more important)
  W3: golden-ratio-graded (radius * phi^(-r))
Goal: see if any natural weighting puts centralization back in the
Brandon-predicted 1/3 band [0.25, 0.42].
Per #69: report bare results; if all three remain out-of-band, the
1/3 hypothesis is robustly disconfirmed.
"""
import json, math
from pathlib import Path
import numpy as np

RING_RADII  = [0.0, 1/math.sqrt(2), 1.0, math.sqrt(2),
               (1+math.sqrt(5))/2, math.e, math.pi, 2*math.pi]
RING_COUNTS = [1, 6, 6, 8, 8, 10, 10, 8]
N = sum(RING_COUNTS); assert N == 57
PHI = (1 + math.sqrt(5)) / 2

ring_offsets = [0]
for n_r in RING_COUNTS:
    ring_offsets.append(ring_offsets[-1] + n_r)


def vidx(r, k): return ring_offsets[r] + k


def vertex_ring(i):
    for r in range(len(RING_COUNTS)):
        if i < ring_offsets[r + 1]:
            return r
    return len(RING_COUNTS) - 1


def build_weighted_A(weight_func):
    A = np.zeros((N, N))
    for r, n_r in enumerate(RING_COUNTS):
        if n_r < 2: continue
        for k in range(n_r):
            nbr = (k + 1) % n_r
            w = weight_func(r, r)
            A[vidx(r, k), vidx(r, nbr)] = w
            A[vidx(r, nbr), vidx(r, k)] = w
    for r in range(len(RING_COUNTS) - 1):
        n_r, n_r1 = RING_COUNTS[r], RING_COUNTS[r + 1]
        if n_r == 0 or n_r1 == 0: continue
        for k in range(n_r):
            theta_k = 2 * math.pi * k / max(n_r, 1)
            best, best_d = 0, 1e9
            for kk in range(n_r1):
                theta_kk = 2 * math.pi * kk / max(n_r1, 1)
                d = abs(((theta_k - theta_kk + math.pi) % (2 * math.pi)) - math.pi)
                if d < best_d:
                    best_d, best = d, kk
            w = weight_func(r, r + 1)
            A[vidx(r, k), vidx(r + 1, best)] = w
            A[vidx(r + 1, best), vidx(r, k)] = w
    for k in range(RING_COUNTS[1]):
        w = weight_func(0, 1)
        A[vidx(0, 0), vidx(1, k)] = w
        A[vidx(1, k), vidx(0, 0)] = w
    return A


def freeman_deg_centralization(A):
    """Freeman (1979) degree centralization, canonical normalization (N-1)(N-2).
    NOTE Pass 26 audit-fix: prior in-script formula used (N-1)*d_max which is
    wrong for weighted graphs and produced spurious in-band values; restored
    to canonical denominator matching Pass 25 §1 Reading 1."""
    deg = A.sum(axis=1); d_max = deg.max()
    return float((d_max - deg).sum() / ((N - 1) * (N - 2)))


def eig_centralization(A):
    eigvals, eigvecs = np.linalg.eigh(A)
    ec = np.abs(eigvecs[:, -1]); ec = ec / (ec.sum() + 1e-12)
    ec_max = ec.max()
    hub_star = 0.5; leaf_star = 1.0 / (2 * (N - 1))
    C_max = (N - 1) * (hub_star - leaf_star)
    return float((ec_max - ec).sum() / C_max)


def gini(A):
    deg = A.sum(axis=1)
    s = np.sort(deg); cum = s.cumsum()
    return float((2 * (np.arange(1, N + 1) * s).sum() - (N + 1) * cum[-1])
                 / (N * (cum[-1] + 1e-12)))


schemes = {
    "W0_unit_baseline":              lambda r1, r2: 1.0,
    "W1_radius_weighted":            lambda r1, r2: max(RING_RADII[r1], RING_RADII[r2]) + 1e-3,
    "W2_inverse_radius_weighted":    lambda r1, r2: 1.0 / (max(RING_RADII[r1], RING_RADII[r2]) + 0.5),
    "W3_golden_graded":              lambda r1, r2: (RING_RADII[r2] + 0.1) * (PHI ** (-max(r1, r2))),
}

print("=" * 72)
print("w25 — Weighted-centralization recompute on BOK Crystal (4 schemes)")
print("=" * 72)
print(f"{'Scheme':<28} {'C_deg':>8} {'C_eig':>8} {'gini':>8} {'in 1/3 band?':>14}")
results = {}
for name, wf in schemes.items():
    A = build_weighted_A(wf)
    C_d = freeman_deg_centralization(A)
    C_e = eig_centralization(A)
    g_d = gini(A)
    in_band = "YES" if any(0.25 <= v <= 0.42 for v in [C_d, C_e, g_d]) else "no"
    print(f"{name:<28} {C_d:>8.4f} {C_e:>8.4f} {g_d:>8.4f} {in_band:>14}")
    results[name] = {"C_deg": C_d, "C_eig": C_e, "gini": g_d, "in_band_1_3": in_band}

# Decision
any_in_band = any(r["in_band_1_3"] == "YES" for r in results.values())
verdict = ("PARTIAL_RESCUE — at least one weighting puts a metric in [0.25, 0.42]"
           if any_in_band else
           "ROBUSTLY_DISCONFIRMED — no natural weighting rescues the 1/3 prediction")
print(f"\nVerdict: {verdict}")

out = Path("analyses/pass26_w25_weighted_centralization")
out.mkdir(parents=True, exist_ok=True)
(out / "results.json").write_text(json.dumps({"per_scheme": results, "verdict": verdict}, indent=2))
print(f"Saved → {out/'results.json'}")
