"""
Pass 25 discharges:

  m24-A: BOK Crystal 57-node graph centralization (Freeman 1979 degree-
         centralization + eigenvector centralization). Pass-24 §3.3 / §3.4
         hypothesis: i-Cells (humans) ≈ 2/3 centralized; GM Network /
         BOK Crystal ≈ 1/3 centralized (FLIPPED).

  Pass-24 §1.3 falsifiability test:
         R_t (resonance) versus per-mapping AUC (retrieval accuracy)
         on the existing r20 K=100 mapping ensemble. R_t defined as
         entropy-discounted attention concentration on the softmax-
         transformed restricted-Hamiltonian energies.

Both are zero-cost numpy computations on already-built artifacts.

Per #69:
  - m24-A is a single-graph point estimate, not a population study;
    falsifies the FLIPPED prediction only if Crystal ≈ 2/3 (not 1/3).
  - R_t-vs-accuracy on K=100 already-collected mappings is a
    POST-HOC analysis; the proper next step (filed g25) is a fresh
    pre-registered run that logs R_t alongside accuracy. Reporting
    here is exploratory-quantitative.
"""
import json
import math
from pathlib import Path

import numpy as np

# ── 1. Rebuild BOK Crystal 57-node adjacency ──────────────────────
RING_RADII  = [0.0, 1/math.sqrt(2), 1.0, math.sqrt(2),
               (1+math.sqrt(5))/2, math.e, math.pi, 2*math.pi]
RING_COUNTS = [1, 6, 6, 8, 8, 10, 10, 8]
N = sum(RING_COUNTS)
assert N == 57

ring_offsets = [0]
for n_r in RING_COUNTS:
    ring_offsets.append(ring_offsets[-1] + n_r)


def vidx(r, k):
    return ring_offsets[r] + k


A = np.zeros((N, N))
for r, n_r in enumerate(RING_COUNTS):
    if n_r < 2:
        continue
    for k in range(n_r):
        nbr = (k + 1) % n_r
        A[vidx(r, k), vidx(r, nbr)] = 1
        A[vidx(r, nbr), vidx(r, k)] = 1
for r in range(len(RING_COUNTS) - 1):
    n_r, n_r1 = RING_COUNTS[r], RING_COUNTS[r + 1]
    if n_r == 0 or n_r1 == 0:
        continue
    for k in range(n_r):
        theta_k = 2 * math.pi * k / max(n_r, 1)
        best, best_d = 0, 1e9
        for kk in range(n_r1):
            theta_kk = 2 * math.pi * kk / max(n_r1, 1)
            d = abs(((theta_k - theta_kk + math.pi) % (2 * math.pi)) - math.pi)
            if d < best_d:
                best_d, best = d, kk
        A[vidx(r, k), vidx(r + 1, best)] = 1
        A[vidx(r + 1, best), vidx(r, k)] = 1
for k in range(RING_COUNTS[1]):
    A[vidx(0, 0), vidx(1, k)] = 1
    A[vidx(1, k), vidx(0, 0)] = 1


# ── 2. Centralization measures ────────────────────────────────────
deg = A.sum(axis=1)
d_max = deg.max()

# Freeman 1979 degree centralization (normalized to [0, 1]; 1 = star graph)
C_deg = (d_max - deg).sum() / ((N - 1) * (N - 2))

# Eigenvector centrality + Freeman-style normalization
eigvals, eigvecs = np.linalg.eigh(A)
ec = np.abs(eigvecs[:, -1])  # principal eigenvector
ec = ec / ec.sum()           # L1-normalize so it's a distribution
ec_max = ec.max()
# Normalization: max possible numerator achieved by a star graph
# = (1) − (1/(N−1)) × (N−1) summed over leaves; using the standard
# eigenvector-centralization formula (Freeman-style):
C_eig_raw = (ec_max - ec).sum()
# Theoretical max for a star graph of size N (compute analytically):
# star graph principal eigenvector after L1-norm: hub=1/2, leaves=1/(2(N-1))
hub_star = 0.5
leaf_star = 1.0 / (2 * (N - 1))
C_eig_max = (hub_star - hub_star) + (N - 1) * (hub_star - leaf_star)
C_eig = C_eig_raw / C_eig_max

# Hub-dominance ratio normalised by (N-1). NOTE: this is NOT scaled to [0, 1]
# with star-graph max = 1; for a star graph the value is ≈ 0.5 at large N, not 1.
# We keep it as a relative-magnitude diagnostic only; do not interpret as a
# Freeman-style centralization-fraction. Renamed to make the divergence obvious.
hub_dom_ratio_over_Nminus1 = ((d_max / deg.mean()) - 1.0) / (N - 1 - 1e-9)
hub_dom_norm = hub_dom_ratio_over_Nminus1  # alias kept for downstream compat

# Gini coefficient on degree (alt centralization; 0=uniform, ~1=star)
sorted_d = np.sort(deg)
cum = sorted_d.cumsum()
gini_deg = (2 * (np.arange(1, N + 1) * sorted_d).sum() - (N + 1) * cum[-1]) / (N * cum[-1])


print("=" * 72)
print("m24-A — BOK Crystal 57-node graph centralization")
print("=" * 72)
print(f"N = {N} ;  edges = {int(A.sum() / 2)} ;  d_max = {int(d_max)} ;  d_mean = {deg.mean():.3f}")
print(f"  Freeman degree centralization        C_deg     = {C_deg:.4f}")
print(f"  Freeman-normalised eigenvector cent. C_eig     = {C_eig:.4f}")
print(f"  Hub-dominance (normalised)           hub_dom_n = {hub_dom_norm:.4f}")
print(f"  Gini coefficient on degrees          gini_deg  = {gini_deg:.4f}")

print(f"\nBrandon's PREDICTION (Pass-24 §3): GM Network ≈ 1/3 centralised (FLIPPED).")
for name, v in [("C_deg", C_deg), ("C_eig", C_eig),
                ("hub_dom_n", hub_dom_norm), ("gini_deg", gini_deg)]:
    band = ("≈ 1/3 (PREDICTION MATCH)" if 0.25 <= v <= 0.42
            else "≈ 2/3 (PREDICTION FLIPPED — opposite)" if 0.58 <= v <= 0.75
            else "intermediate / out-of-band")
    print(f"  {name:<12} = {v:.4f}  →  {band}")


# ── 3. R_t-vs-accuracy regression on r20 ──────────────────────────
# Re-derive energies[i, k] from the already-pre-registered r20 protocol.
import sys
sys.path.insert(0, str(Path("analyses/tsc_h4_sat")))
from tsc_h4_sat_prototype import (  # noqa: E402
    build_tsc_hamiltonian, gen_3sat, is_sat, restricted_ground, roc_auc,
)

H_tsc, _ = build_tsc_hamiltonian()

import random  # noqa: E402

PRE_REG = json.loads(Path(
    "analyses/tsc_h4_sat_r20_replication/PRE_REGISTRATION.json").read_text())
d = PRE_REG["design"]
seed = d["instance_seed"]
M_target = d["n_instances"]
K = d["mappings_per_instance"]

rng = random.Random(seed)
instances = []
for _ in range(M_target):
    n_vars = rng.randint(d["min_vars"], d["max_vars"])
    ratio = d["clause_var_ratio_min"] + rng.random() * (
        d["clause_var_ratio_max"] - d["clause_var_ratio_min"])
    n_clauses = max(3, int(round(n_vars * ratio)))
    inst = gen_3sat(rng, n_vars, n_clauses)
    sat = is_sat(inst, n_vars)
    if n_vars + n_clauses <= 57:
        instances.append((n_vars, n_clauses, inst, sat))
M = len(instances)
print()
print("=" * 72)
print("Pass-24 §1.3 falsifiability — R_t versus per-mapping AUC")
print("=" * 72)
print(f"r20 corpus rebuilt: M={M} ; K={K} ; seed={seed}")

energies = np.zeros((M, K))
labels = np.array([0 if s else 1 for (_, _, _, s) in instances])
for i in range(M):
    n_vars, n_clauses, _, _ = instances[i]
    n_needed = n_vars + n_clauses
    for k in range(K):
        map_rng = random.Random((seed * 10007) + (i * 31337) + k)
        indices = map_rng.sample(range(57), n_needed)
        energies[i, k] = restricted_ground(H_tsc, indices)

# Per-mapping AUC (HIGHER-E ⇒ SAT = inverted reading)
per_map_auc = np.array([1.0 - roc_auc(energies[:, k].tolist(), labels.tolist())
                        for k in range(K)])

# Per-mapping resonance R_t = entropy-discounted attention concentration.
# For each mapping k, treat softmax(-energies[:, k] / T) as the attention
# distribution α^(k); R_t(k) = 1 - H(α^(k)) / log(M)  ∈ [0, 1].
# Pick T = mean(std(energies, axis=0)) so the softmax has comparable
# sharpness across mappings; this makes R_t depend on cross-instance
# energy DISCRIMINATION, not absolute scale.
T = float(energies.std(axis=0).mean())
alpha = np.exp(-(energies - energies.min(axis=0, keepdims=True)) / T)
alpha = alpha / alpha.sum(axis=0, keepdims=True)        # M × K
ent = -(alpha * np.log(alpha + 1e-30)).sum(axis=0)      # K
R_t = 1.0 - ent / math.log(M)                           # K, in [0, 1]


def pearson(x, y):
    x = np.asarray(x); y = np.asarray(y)
    xm, ym = x.mean(), y.mean()
    num = ((x - xm) * (y - ym)).sum()
    den = math.sqrt(((x - xm) ** 2).sum() * ((y - ym) ** 2).sum())
    return num / den if den > 0 else float('nan')


r_obs = pearson(R_t, per_map_auc)

# Permutation null
rng_p = np.random.RandomState(20260509)
n_perm = 10000
perm_r = np.empty(n_perm)
idx = np.arange(K)
for p in range(n_perm):
    rng_p.shuffle(idx)
    perm_r[p] = pearson(R_t, per_map_auc[idx])
p_two = (np.abs(perm_r) >= abs(r_obs)).mean()

print(f"  T (softmax temperature) = mean per-mapping std(energy) = {T:.4f}")
print(f"  R_t range: [{R_t.min():.4f}, {R_t.max():.4f}]   mean={R_t.mean():.4f}")
print(f"  per_map_auc range: [{per_map_auc.min():.4f}, {per_map_auc.max():.4f}]"
      f"   mean={per_map_auc.mean():.4f}")
print(f"  Pearson r(R_t, per_map_auc) = {r_obs:+.4f}")
print(f"  Permutation null (n={n_perm}): two-sided p = {p_two:.4f}")
print(f"  Permutation null mean = {perm_r.mean():+.4f} ;  std = {perm_r.std():.4f}")

# Decision per Pass-24 §1.3 spec: novel falsifiable prediction is
# R_t SHOULD be predictive of per-map accuracy. r > 0 with p < 0.05
# = WEAK CONFIRM; r ≤ 0 or p ≥ 0.05 = NULL (does not survive).
if r_obs > 0 and p_two < 0.05:
    decision = "WEAK CONFIRM (post-hoc; pre-registered fresh run filed g25)"
elif r_obs > 0:
    decision = "TREND-POSITIVE BUT NOT SIGNIFICANT"
else:
    decision = "NULL / NEGATIVE — R_t is not predictive of per-map AUC on r20"
print(f"  Decision (post-hoc): {decision}")

# ── 4. Save outputs ─────────────────────────────────────────────────
out_dir = Path("analyses/pass25_m24a_rt_regression")
out_dir.mkdir(parents=True, exist_ok=True)
results = {
    "m24a_BOK_Crystal_centralization": {
        "N": N, "edges": int(A.sum() / 2),
        "d_max": int(d_max), "d_mean": float(deg.mean()),
        "C_freeman_degree": float(C_deg),
        "C_freeman_eigenvector": float(C_eig),
        "hub_dominance_normalised": float(hub_dom_norm),
        "gini_degree": float(gini_deg),
        "prediction_band_one_third": [0.25, 0.42],
        "prediction_band_two_thirds": [0.58, 0.75],
    },
    "rt_vs_accuracy_regression_r20": {
        "M": int(M), "K": int(K), "seed": int(seed),
        "softmax_T": float(T),
        "R_t_min": float(R_t.min()), "R_t_max": float(R_t.max()),
        "R_t_mean": float(R_t.mean()),
        "per_map_auc_min": float(per_map_auc.min()),
        "per_map_auc_max": float(per_map_auc.max()),
        "per_map_auc_mean": float(per_map_auc.mean()),
        "pearson_r": float(r_obs),
        "permutation_p_two_sided": float(p_two),
        "permutation_n": n_perm,
        "permutation_null_mean": float(perm_r.mean()),
        "permutation_null_std": float(perm_r.std()),
        "decision": decision,
        "note": "POST-HOC on existing r20 K=100 mappings. Pre-registered "
                "fresh-corpus replication filed as g25.",
    },
}
(out_dir / "results.json").write_text(json.dumps(results, indent=2))
print(f"\nSaved → {out_dir/'results.json'}")
