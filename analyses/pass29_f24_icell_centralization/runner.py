"""f24 — i-cell centralization vs determination empirical correlation scan.

Hypothesis: graph centralization (Freeman-degree) correlates with
"determination" (= 1 - normalized graph entropy of degree distribution).
Tests whether highly-centralized graphs are also highly-determined.

Pre-reg: 100 random graphs (varying density), measure (C_deg, D)
ACCEPT if |Pearson r| ≥ 0.5
REJECT if |r| ≤ 0.15
"""
import json, math, numpy as np
from pathlib import Path

SEED = 28284271  # 2√2-derived

def centralization_freeman(A):
    N = len(A)
    deg = A.sum(axis=1)
    max_deg = deg.max()
    return float((max_deg - deg).sum() / ((N-1)*(N-2))) if N > 2 else 0.0

def determination(A):
    deg = A.sum(axis=1)
    if deg.sum() == 0: return 0.0
    p = deg / deg.sum()
    p = p[p > 0]
    H = -(p * np.log(p)).sum()
    H_max = math.log(len(deg))
    return float(1 - H/H_max) if H_max > 0 else 0.0

def gen_graph(N, p_edge, seed):
    rng = np.random.default_rng(seed)
    A = (rng.random((N, N)) < p_edge).astype(float)
    A = np.triu(A, 1); A = A + A.T
    return A

def main():
    rng = np.random.default_rng(SEED)
    Cs, Ds = [], []
    for i in range(100):
        N = int(rng.integers(20, 80))
        p = float(rng.uniform(0.05, 0.5))
        # bias some toward star/hub structure
        A = gen_graph(N, p, int(rng.integers(1e9)))
        if i % 4 == 0:  # add hub structure
            A[0, :] = 1; A[:, 0] = 1; A[0,0] = 0
        Cs.append(centralization_freeman(A))
        Ds.append(determination(A))
    r = float(np.corrcoef(Cs, Ds)[0,1])
    verdict = ("CONFIRM" if abs(r) >= 0.5
               else "REJECT" if abs(r) <= 0.15
               else "PARTIAL")
    out = {"seed": SEED, "n_graphs": 100,
           "pearson_C_vs_D": round(r, 4),
           "C_mean": round(float(np.mean(Cs)),4),
           "D_mean": round(float(np.mean(Ds)),4),
           "verdict": verdict,
           "pre_reg": "CONFIRM |r|≥0.5, REJECT |r|≤0.15"}
    Path("analyses/pass29_f24_icell_centralization/results.json").write_text(json.dumps(out, indent=2))
    print(json.dumps(out, indent=2))

if __name__ == "__main__": main()
