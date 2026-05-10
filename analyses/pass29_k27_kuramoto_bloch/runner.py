"""k27 — Kuramoto Φ ↔ Bloch-equator AA numerical unification.

Hypothesis (Pass 27 §3): Kuramoto order parameter Φ_t (collective phase)
projects onto Bloch-sphere equator at angle equal to AA azimuth.

Test:
- Simulate N=50 Kuramoto oscillators in synchronized regime (K=2.0 > Kc)
- For each step t, compute Φ_t = arg(1/N Σ e^{iθ_j})
- Independently parametrize a Bloch-equator state |ψ_t⟩ = (|0⟩+e^{iφ}|1⟩)/√2
  with φ = Φ_t  → its Bloch azimuth angle should equal Φ_t exactly
- ACCEPT if RMS |φ_Bloch − Φ_t| < 1e-10 (numerically exact)
- (this is a "definitional" confirmation — establishes the mapping is
  consistent, not that it's a deep physical claim)
"""
import math, json, numpy as np
from pathlib import Path

SEED = 14142135  # √2-derived

def kuramoto_run(N=50, T=2000, K=2.0, seed=SEED):
    rng = np.random.default_rng(seed)
    theta = rng.uniform(0, 2*math.pi, N)
    omega = rng.normal(1.0, 0.05, N)
    Phis = np.zeros(T)
    for t in range(T):
        coupling = K/N * np.sum(np.sin(theta[None,:] - theta[:,None]), axis=1)
        theta = theta + 0.01*(omega + coupling)
        z = np.mean(np.exp(1j*theta))
        Phis[t] = math.atan2(z.imag, z.real)
    return Phis

def bloch_azimuth_from_state(phi):
    # |ψ⟩ = (|0⟩ + e^{iφ}|1⟩)/√2; Bloch vector = (cos φ, sin φ, 0)
    bx, by = math.cos(phi), math.sin(phi)
    return math.atan2(by, bx)

def main():
    Phis = kuramoto_run()
    bloch = np.array([bloch_azimuth_from_state(p) for p in Phis])
    # circular RMS
    diff = np.angle(np.exp(1j*(bloch - Phis)))
    rms = float(np.sqrt(np.mean(diff**2)))
    R_final = float(np.abs(np.mean(np.exp(1j*Phis[-100:]))))
    verdict = "CONFIRM" if rms < 1e-10 else "REJECT"
    out = {"seed": SEED, "N_oscillators": 50, "T_steps": 2000,
           "K_coupling": 2.0, "rms_phi_diff": rms,
           "kuramoto_R_final": round(R_final,4),
           "verdict": verdict,
           "interpretation": "Kuramoto Φ and Bloch-equator azimuth are definitionally identical when |ψ⟩=(|0⟩+e^{iΦ}|1⟩)/√2; this is an existence-of-mapping confirmation, NOT a physical claim."}
    Path("analyses/pass29_k27_kuramoto_bloch/results.json").write_text(json.dumps(out, indent=2))
    print(json.dumps(out, indent=2))

if __name__ == "__main__": main()
