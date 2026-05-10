"""
r25-COMPOSITE — pre-registered fresh-corpus run executing
analyses/pass25_r24_composite_prereg/PRE_REGISTRATION.json verbatim.

H_composite = H_TSC + lambda_P * H_Penrose_pinning + lambda_LCC * diag(LCC_static)

Honest substitutions (model-substitutions per #69, declared up-front):
  - H_Penrose_pinning: quasi-periodic on-site potential V_quasi(v) =
    cos(2π · ρ(r) · k / phi) where ρ(r) is ring radius and k is the
    angular index — captures the golden-angle aperiodicity of Penrose
    tilings without requiring a 5-fold-symmetric tiling embedding.
  - LCC_static: per-vertex local clustering coefficient C_local(v) ∈ [0, 1]
    (Watts-Strogatz 1998), the natural static analog of the temporal
    LCC_v3-rolling. Values are then pushed through the LCC_v3 Pearson-rolling
    threshold (C* = 1/(phi*sqrt(2)) = 0.4370) by subtracting C* so the
    diagonal entries are positive (above-threshold) or negative
    (below-threshold) — this is the closest static analog to the
    rolling-window mechanism.

Both substitutions are filed as openly-declared model-choices, NOT
ratified by Brandon. If r25-COMPOSITE confirms, the next-pass work
is to verify the substitutions don't dominate the result; if it
disconfirms, a closer-to-canonical Penrose+LCC implementation is
the natural next step before retiring the prediction.
"""
import json, math, random, sys
from pathlib import Path
import numpy as np

PRE = json.loads(Path(
    "analyses/pass25_r24_composite_prereg/PRE_REGISTRATION.json").read_text())
d = PRE["design"]; seed = d["instance_seed"]
M_target = d["n_instances"]; K = d["mappings_per_instance"]
LAMBDA_P = d["lambda_P"]; LAMBDA_LCC = d["lambda_LCC"]
PHI = (1 + math.sqrt(5)) / 2
C_STAR = 1 / (PHI * math.sqrt(2))

# Build the 57-vertex polytope + base H_TSC
RING_RADII  = [0.0, 1/math.sqrt(2), 1.0, math.sqrt(2),
               PHI, math.e, math.pi, 2*math.pi]
RING_COUNTS = [1, 6, 6, 8, 8, 10, 10, 8]
N = sum(RING_COUNTS); assert N == 57
ring_offsets = [0]
for n_r in RING_COUNTS:
    ring_offsets.append(ring_offsets[-1] + n_r)


def vidx(r, k): return ring_offsets[r] + k


vert_info = []  # (ring_index, angular_index)
for r, n_r in enumerate(RING_COUNTS):
    for k in range(n_r):
        vert_info.append((r, k))

A = np.zeros((N, N))
for r, n_r in enumerate(RING_COUNTS):
    if n_r < 2: continue
    for k in range(n_r):
        nbr = (k + 1) % n_r
        A[vidx(r, k), vidx(r, nbr)] = 1
        A[vidx(r, nbr), vidx(r, k)] = 1
for r in range(len(RING_COUNTS) - 1):
    n_r, n_r1 = RING_COUNTS[r], RING_COUNTS[r + 1]
    for k in range(n_r):
        theta_k = 2 * math.pi * k / max(n_r, 1)
        best, best_d = 0, 1e9
        for kk in range(n_r1):
            theta_kk = 2 * math.pi * kk / max(n_r1, 1)
            dist = abs(((theta_k - theta_kk + math.pi) % (2 * math.pi)) - math.pi)
            if dist < best_d: best_d, best = dist, kk
        A[vidx(r, k), vidx(r + 1, best)] = 1
        A[vidx(r + 1, best), vidx(r, k)] = 1
for k in range(RING_COUNTS[1]):
    A[vidx(0, 0), vidx(1, k)] = 1
    A[vidx(1, k), vidx(0, 0)] = 1

D = np.diag(A.sum(axis=1))
H_TSC = D - A

# Penrose pinning (quasi-periodic on-site)
V_quasi = np.array([math.cos(2 * math.pi * RING_RADII[r] * k / PHI)
                    for (r, k) in vert_info])
H_Penrose = np.diag(V_quasi)

# Static LCC: local clustering coefficient
def local_clustering(adj):
    n = adj.shape[0]
    out = np.zeros(n)
    for i in range(n):
        nbrs = np.where(adj[i] > 0)[0]
        deg = len(nbrs)
        if deg < 2: continue
        possible = deg * (deg - 1) / 2
        actual = 0
        for a in range(len(nbrs)):
            for b in range(a + 1, len(nbrs)):
                if adj[nbrs[a], nbrs[b]] > 0: actual += 1
        out[i] = actual / possible
    return out


C_local = local_clustering(A)
LCC_diag = np.diag(C_local - C_STAR)
H_composite = H_TSC + LAMBDA_P * H_Penrose + LAMBDA_LCC * LCC_diag

print(f"r25-COMPOSITE: M_target={M_target}, K={K}, seed={seed}")
print(f"  λ_P={LAMBDA_P}, λ_LCC={LAMBDA_LCC}, C*={C_STAR:.4f}")
print(f"  V_quasi range: [{V_quasi.min():.3f}, {V_quasi.max():.3f}]")
print(f"  C_local range: [{C_local.min():.3f}, {C_local.max():.3f}], mean={C_local.mean():.3f}")

# Reuse SAT primitives
sys.path.insert(0, str(Path("analyses/tsc_h4_sat")))
from tsc_h4_sat_prototype import gen_3sat, is_sat, roc_auc


def restricted_ground_local(H, indices):
    sub = H[np.ix_(indices, indices)]
    eigvals = np.linalg.eigvalsh(sub)
    return float(eigvals[0])


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
n_sat = sum(1 for x in instances if x[3]); n_unsat = M - n_sat
print(f"  corpus: M={M}, n_sat={n_sat}, n_unsat={n_unsat}")

if n_sat < 30 or n_unsat < 30:
    print("CORPUS_QUALITY_FAILURE per anti-HARK rule")
    Path("analyses/pass26_r25_composite/results.json").write_text(
        json.dumps({"verdict": "CORPUS_QUALITY_FAILURE", "n_sat": n_sat, "n_unsat": n_unsat}, indent=2))
    sys.exit(0)

energies = np.zeros((M, K))
labels = np.array([0 if x[3] else 1 for x in instances])
for i in range(M):
    n_vars, n_clauses, _, _ = instances[i]
    n_needed = n_vars + n_clauses
    for k in range(K):
        map_rng = random.Random((seed * 10007) + (i * 31337) + k)
        indices = map_rng.sample(range(57), n_needed)
        energies[i, k] = restricted_ground_local(H_composite, indices)
    if (i + 1) % 50 == 0:
        print(f"  ... {i+1}/{M} done")

mean_E = energies.mean(axis=1)
auc_lower = roc_auc(mean_E.tolist(), labels.tolist())
auc_inverted = 1.0 - auc_lower

per_map_auc = np.array([1.0 - roc_auc(energies[:, k].tolist(), labels.tolist())
                        for k in range(K)])

R20_BASELINE = 0.7318
delta = auc_inverted - R20_BASELINE

if 0.65 <= auc_inverted <= 0.78:
    verdict = "CONFIRM_composite"
elif (0.55 <= auc_inverted < 0.65) or (0.78 < auc_inverted <= 0.85):
    verdict = "PARTIAL_R_A_only"
else:
    verdict = "DISCONFIRM"

print(f"\nAveraged-energy AUC (inverted) = {auc_inverted:.4f}")
print(f"Per-mapping AUC mean = {per_map_auc.mean():.4f} ± {per_map_auc.std():.4f}")
print(f"Δ vs r20 baseline (0.7318) = {delta:+.4f}")
print(f"Verdict: {verdict}")

out = {
    "study_id": "r25_composite_2026-05-10", "M": int(M), "K": int(K), "seed": int(seed),
    "n_sat": int(n_sat), "n_unsat": int(n_unsat),
    "lambda_P": LAMBDA_P, "lambda_LCC": LAMBDA_LCC, "C_star": C_STAR,
    "averaged_energy_auc_inverted": float(auc_inverted),
    "per_map_auc_mean": float(per_map_auc.mean()),
    "per_map_auc_std": float(per_map_auc.std()),
    "delta_vs_r20_baseline": float(delta),
    "verdict": verdict,
    "model_substitutions_declared": [
        "H_Penrose_pinning = quasi-periodic on-site V(v) = cos(2π·ρ(r)·k/φ); not a literal Penrose-tiling embedding.",
        "LCC_static = Watts-Strogatz local clustering coefficient minus C*; static analog of temporal LCC_v3-rolling.",
    ],
    "pre_registration_path": "analyses/pass25_r24_composite_prereg/PRE_REGISTRATION.json",
}
Path("analyses/pass26_r25_composite/results.json").write_text(json.dumps(out, indent=2))
print("Saved → analyses/pass26_r25_composite/results.json")
