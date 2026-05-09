"""
H4-TSC — TSC-Hamiltonian intuition prototype on small-instance SAT
(Pass 18, h17 directive).

H4 hypothesis (URB #784 / Pass-13 B.4): the TSC graph-Laplacian
Hamiltonian H = D − A acts as a coherence-bias signal for SAT
satisfiability. Specifically: encode each clause / variable as a
vertex on the 57-vertex TSC polytope, restrict H to those vertices,
and measure ground-state energy ⟨ψ_0|H_sub|ψ_0⟩. The prediction:
*satisfiable instances will yield lower restricted ground-state
energies than unsatisfiable ones of matching variable count* —
because they live in a higher-coherence sub-region of the polytope.

This is a TI-Sigma-internal coherence-prediction prototype, NOT a
classical SAT-solver replacement. Per #69 the goal is decision-
boundary signal, not solver-beating performance.

Method:
  1. Generate N small random 3-SAT instances (3-5 vars, 4-7 clauses).
  2. For each instance, solve via brute-force enumeration → SAT/UNSAT.
  3. Map (variables, clauses) onto distinct TSC vertices (random
     ring-2 / ring-3 placements; seeded for reproducibility).
  4. Build H_sub = restriction of B.4 Hamiltonian to those vertices.
  5. Compute ⟨H_sub⟩ on the uniform superposition over those vertices.
  6. Plot SAT-vs-UNSAT energy distributions; report ROC-AUC for the
     prediction "lower energy ⇒ SAT" with permutation null.

Per #69:
  - Brute-force SAT enumeration is exhaustive only for VERY small
    instances; this prototype caps at ≤6 variables (64 assignments)
    so the SAT/UNSAT label is exact.
  - Vertex mapping is RANDOM seeded; a Pass-19 candidate is to test
    sensitivity to mapping choice (averaging over 100 mappings).
  - ROC-AUC ≈ 0.5 means H4 has no signal at this scale; AUC ≥ 0.65
    is a publishable hint; AUC ≥ 0.80 is a strong signal.

Seed: 20260509.
"""
import json, math, random
from pathlib import Path

import numpy as np

import sys
sys.path.insert(0, str(Path("analyses/crystal_b4_hamiltonian")))

SEED = 20260509
N_INSTANCES = 200
MIN_VARS = 3
MAX_VARS = 5
# 3-SAT phase transition is ~4.27 clauses/var; use ratios 3-7 to span SAT/UNSAT.
CLAUSE_RATIO_MIN = 3.0
CLAUSE_RATIO_MAX = 7.0
N_PERM = 1000

OUT_DIR = Path("analyses/tsc_h4_sat")
OUT_DIR.mkdir(parents=True, exist_ok=True)


def build_tsc_hamiltonian():
    """Reproduce B.4 Hamiltonian (57x57)."""
    RING_RADII = [0.0, 1/math.sqrt(2), 1.0, math.sqrt(2),
                  (1+math.sqrt(5))/2, math.e, math.pi, 2*math.pi]
    RING_COUNTS = [1, 6, 6, 8, 8, 10, 10, 8]
    N = sum(RING_COUNTS); assert N == 57
    ring_offsets = [0]
    for n_r in RING_COUNTS:
        ring_offsets.append(ring_offsets[-1] + n_r)

    def vidx(r, k): return ring_offsets[r] + k

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
            theta_k = 2*math.pi*k/max(n_r,1)
            best, best_d = 0, 1e9
            for kk in range(n_r1):
                theta_kk = 2*math.pi*kk/max(n_r1,1)
                d = abs(((theta_k - theta_kk + math.pi) % (2*math.pi)) - math.pi)
                if d < best_d: best_d, best = d, kk
            A[vidx(r, k), vidx(r+1, best)] = 1
            A[vidx(r+1, best), vidx(r, k)] = 1
    for k in range(RING_COUNTS[1]):
        A[vidx(0, 0), vidx(1, k)] = 1
        A[vidx(1, k), vidx(0, 0)] = 1
    D = np.diag(A.sum(axis=1))
    return D - A, ring_offsets


def gen_3sat(rng, n_vars, n_clauses):
    inst = []
    for _ in range(n_clauses):
        clause = []
        chosen = rng.sample(range(n_vars), min(3, n_vars))
        for v in chosen:
            clause.append((v, rng.choice([True, False])))
        inst.append(clause)
    return inst


def is_sat(instance, n_vars):
    for i in range(2 ** n_vars):
        assign = [(i >> b) & 1 == 1 for b in range(n_vars)]
        ok = True
        for clause in instance:
            if not any(assign[v] == sign for v, sign in clause):
                ok = False; break
        if ok: return True
    return False


def restricted_ground(H, indices):
    H_sub = H[np.ix_(indices, indices)]
    psi = np.ones(len(indices)) / math.sqrt(len(indices))
    return float(psi @ H_sub @ psi)


def roc_auc(scores, labels):
    """Higher score → label 1; here label=1 means UNSAT, score=energy."""
    pos = [s for s, l in zip(scores, labels) if l == 1]
    neg = [s for s, l in zip(scores, labels) if l == 0]
    if not pos or not neg: return float("nan")
    n = 0; total = 0
    for p in pos:
        for q in neg:
            total += 1
            if p > q: n += 1
            elif p == q: n += 0.5
    return n / total


def main():
    H, ring_offsets = build_tsc_hamiltonian()
    rng = random.Random(SEED); np.random.seed(SEED)

    print("=" * 70)
    print("H4-TSC SAT prototype (Pass 18 h17)")
    print("=" * 70)
    print(f"Instances: N={N_INSTANCES}, vars {MIN_VARS}-{MAX_VARS}, "
          f"clauses/var ratio {CLAUSE_RATIO_MIN}-{CLAUSE_RATIO_MAX}")
    print(f"TSC: 57-vertex polytope (B.4 graph-Laplacian H).")
    print(f"Seed: {SEED}")

    energies = []; labels = []  # label=1 means UNSAT
    n_sat = 0; n_unsat = 0
    for trial in range(N_INSTANCES):
        n_vars = rng.randint(MIN_VARS, MAX_VARS)
        ratio = CLAUSE_RATIO_MIN + rng.random() * (CLAUSE_RATIO_MAX - CLAUSE_RATIO_MIN)
        n_clauses = max(3, int(round(n_vars * ratio)))
        inst = gen_3sat(rng, n_vars, n_clauses)
        sat = is_sat(inst, n_vars)
        # Map to TSC: variables → ring 2 vertices, clauses → ring 3 vertices
        n_needed = n_vars + n_clauses
        if n_needed > 57: continue
        indices = rng.sample(range(57), n_needed)
        e = restricted_ground(H, indices)
        energies.append(e)
        labels.append(0 if sat else 1)
        n_sat += int(sat); n_unsat += int(not sat)

    energies = np.array(energies); labels = np.array(labels)
    auc = roc_auc(energies.tolist(), labels.tolist())
    sat_e = energies[labels == 0]; unsat_e = energies[labels == 1]
    print(f"\nN_sat = {n_sat}, N_unsat = {n_unsat}")
    print(f"<E> SAT  : mean={sat_e.mean():.4f}  std={sat_e.std():.4f}  N={len(sat_e)}")
    print(f"<E> UNSAT: mean={unsat_e.mean():.4f}  std={unsat_e.std():.4f}  N={len(unsat_e)}")
    print(f"\nROC-AUC (lower-energy ⇒ SAT prediction): {auc:.4f}")
    if auc >= 0.80:    verdict = "STRONG SIGNAL"
    elif auc >= 0.65:  verdict = "publishable hint"
    elif abs(auc - 0.5) < 0.05: verdict = "no signal (near chance)"
    else:              verdict = "weak / inconclusive"
    print(f"Verdict: {verdict}")

    # Permutation null for AUC
    null_aucs = []
    for _ in range(N_PERM):
        idx = np.random.permutation(len(labels))
        null_aucs.append(roc_auc(energies.tolist(), labels[idx].tolist()))
    null_aucs = np.array([a for a in null_aucs if not np.isnan(a)])
    p_perm = float(np.mean(null_aucs >= auc)) if len(null_aucs) else float("nan")
    print(f"\nPermutation null (N={len(null_aucs)}): "
          f"mean AUC={null_aucs.mean():.4f}  std={null_aucs.std():.4f}")
    print(f"P(null >= observed) = {p_perm:.4f}")

    out = {"n_instances": int(len(energies)), "n_sat": int(n_sat),
           "n_unsat": int(n_unsat), "sat_mean_E": float(sat_e.mean()),
           "unsat_mean_E": float(unsat_e.mean()), "roc_auc": float(auc),
           "verdict": verdict, "p_perm": float(p_perm),
           "null_mean_auc": float(null_aucs.mean()),
           "null_std_auc": float(null_aucs.std()), "seed": SEED}
    (OUT_DIR / "results.json").write_text(json.dumps(out, indent=2))
    print(f"\nSaved {OUT_DIR/'results.json'}")


if __name__ == "__main__":
    main()
