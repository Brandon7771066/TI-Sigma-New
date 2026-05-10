"""u27 — UTFE U★ argmax vs LCC v3 above-C numerical correlation. (PATCHED)

Patch from v1: use phase-increment differences (Δθ_t = θ_t - θ_{t-1} - ω_mean)
to get K-discriminating signal (sin(θ) was near-coherent for all K>Kc).

Pre-reg unchanged: ACCEPT r ≥ 0.5, REJECT |r| ≤ 0.2, seed 31415926.
"""
import math, json, numpy as np
from pathlib import Path

PHI = (1+math.sqrt(5))/2; C = 1/(PHI*math.sqrt(2))
SEED = 31415926

def kuramoto_step(theta, omega, K, dt=0.01):
    N = len(theta)
    coupling = K/N * np.sum(np.sin(theta[None,:] - theta[:,None]), axis=1)
    return theta + dt*(omega + coupling)

def simulate(K, N=20, T=500, seed=0):
    rng = np.random.default_rng(seed)
    theta = rng.uniform(0, 2*math.pi, N)
    omega = rng.normal(1.0, 0.1, N)
    history = np.zeros((T, N))
    for t in range(T):
        theta = kuramoto_step(theta, omega, K)
        history[t] = theta
    return history, omega

def U_star_score(hist):
    R = np.abs(np.mean(np.exp(1j*hist), axis=1))
    return float(np.mean(R[100:]))

def lcc_above(hist, omega, w=20):
    # phase-increment residuals (subtract own-natural drift)
    sig = np.diff(hist[100:], axis=0) - 0.01*omega[None, :]
    pairs = [(0,1),(2,3),(4,5)]
    above = 0
    for i,j in pairs:
        n = len(sig)
        rs = []
        for t in range(w, n):
            a = sig[t-w:t,i]; b = sig[t-w:t,j]
            if a.std() < 1e-10 or b.std() < 1e-10: continue
            r = np.corrcoef(a, b)[0,1]
            if not math.isnan(r): rs.append(abs(r))
        if rs and np.mean(rs) > C: above += 1
    return above / len(pairs)

def main():
    rng = np.random.default_rng(SEED)
    Ks = np.linspace(0, 2.0, 200)
    U_scores, L_scores = [], []
    for K in Ks:
        hist, omega = simulate(K, seed=int(rng.integers(1e9)))
        U_scores.append(U_star_score(hist))
        L_scores.append(lcc_above(hist, omega))
    U_scores = np.array(U_scores); L_scores = np.array(L_scores)
    if L_scores.std() < 1e-10:
        r = float('nan'); verdict = "DEGENERATE"
    else:
        r = float(np.corrcoef(U_scores, L_scores)[0,1])
        verdict = "CONFIRM" if r >= 0.5 else ("REJECT" if abs(r) <= 0.2 else "PARTIAL")
    out = {"seed": SEED, "n_networks": 200,
           "pearson_U_vs_LCC": round(r,4) if not math.isnan(r) else None,
           "verdict": verdict,
           "pre_reg": "CONFIRM r≥0.5, REJECT |r|≤0.2",
           "U_mean": round(float(U_scores.mean()),4),
           "U_std": round(float(U_scores.std()),4),
           "LCC_mean": round(float(L_scores.mean()),4),
           "LCC_std": round(float(L_scores.std()),4),
           "interpretation": "Positive r means UTFE U★ optimum (synchrony) coincides with LCC above-C regime; negative r means UTFE peaks where LCC is below threshold."}
    Path("analyses/pass29_u27_utfe_lcc/results.json").write_text(json.dumps(out, indent=2))
    print(json.dumps(out, indent=2))

if __name__ == "__main__": main()
