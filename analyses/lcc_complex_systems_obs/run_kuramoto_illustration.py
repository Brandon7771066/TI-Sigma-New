"""Theory ILLUSTRATION (NOT observational data): mean-field Kuramoto order parameter r(K).
Purpose: show that a monotone synchronization curve necessarily passes through ANY level in
(0,1) -- so 'the order parameter reaches 0.414 / 0.60 / 0.854' is VACUOUS as confirmation of
the LCC rungs. The rungs must instead be tested as STRUCTURAL transitions (discontinuity,
regime change, or collapse of directional inference), not mere level-crossings.
Env: numpy only. ~5s."""
import numpy as np, json, hashlib, os

rng = np.random.default_rng(7)
N = 800
# Lorentzian (Cauchy) natural frequencies, scale gamma -> mean-field K_c = 2*gamma (g(0)=1/(pi*gamma))
gamma = 0.5
omega = gamma * np.tan(np.pi * (rng.random(N) - 0.5))
omega = omega[np.abs(omega) < 12]  # trim extreme tails
N = len(omega)

def order_param(theta):
    z = np.mean(np.exp(1j * theta))
    return np.abs(z), np.angle(z)

def run(K, T=40.0, dt=0.02, burn=0.6):
    theta = rng.uniform(-np.pi, np.pi, N)
    steps = int(T / dt); rs = []
    for s in range(steps):
        r, psi = order_param(theta)
        theta = theta + dt * (omega + K * r * np.sin(psi - theta))
        if s > burn * steps:
            rs.append(r)
    return float(np.mean(rs))

Ks = np.linspace(0.0, 4.0, 41)
rvals = [run(K) for K in Ks]
Kc = 2 * gamma  # mean-field critical coupling for Lorentzian g

rungs = {"onset_sqrt2_minus_1": 2**0.5 - 1, "resonance": (2**0.5 + 1) / 4, "ceiling_cos2_pi8": (2 + 2**0.5) / 4}

# For each rung level, find the (interpolated) K at which r first reaches it -- shows it ALWAYS exists.
def first_crossing(level):
    for i in range(1, len(rvals)):
        if rvals[i - 1] < level <= rvals[i]:
            f = (level - rvals[i - 1]) / (rvals[i] - rvals[i - 1] + 1e-12)
            return float(Ks[i - 1] + f * (Ks[i] - Ks[i - 1]))
    return None

crossings = {name: first_crossing(lv) for name, lv in rungs.items()}

# Directional-inference degradation proxy: phase-difference dispersion collapses as r->1.
# Var of pairwise phase diffs ~ (1 - r^2); near full sync, lagged-regression / TE become ill-conditioned.
disp = {f"K={K:.1f}": float(1 - r**2) for K, r in zip(Ks[::8], np.array(rvals)[::8])}

out = {
    "model": "mean-field Kuramoto, Lorentzian frequencies",
    "N": N, "gamma": gamma, "K_c_meanfield_2gamma": Kc,
    "r_curve": {f"{k:.2f}": round(r, 4) for k, r in zip(Ks, rvals)},
    "rung_levels": rungs,
    "K_at_which_r_first_reaches_rung": crossings,
    "phase_diff_dispersion_1_minus_r2": disp,
    "honest_reading": (
        "r(K) is monotone and continuous (second-order transition at K_c=2*gamma). Every rung "
        "level in (0,1) is reached at SOME K -- so a level-crossing is NOT evidence for a rung. "
        "1 - r^2 -> 0 as r -> 1, i.e. phase-difference dispersion (the signal directional-causality "
        "estimators rely on) collapses near full sync: directional inference DEGRADES exactly where "
        "the corpus places the high-coherence ceiling. The discontinuous-onset reading of the LCC "
        "onset maps to EXPLOSIVE (first-order) synchronization, a different universality class than "
        "this continuous run -- not reproduced here, cited only."
    ),
}
blob = json.dumps(out, sort_keys=True).encode()
out["config_sha"] = hashlib.sha256(blob).hexdigest()[:12]
p = os.path.join(os.path.dirname(os.path.abspath(__file__)), "kuramoto_illustration.json")
json.dump(out, open(p, "w"), indent=2)
print(f"N={N} K_c={Kc:.3f}  r(0)={rvals[0]:.3f} r(max)={rvals[-1]:.3f}")
print("rung levels:", {k: round(v, 4) for k, v in rungs.items()})
print("K at first crossing:", {k: (round(v, 3) if v else None) for k, v in crossings.items()})
print("1-r^2 (dispersion):", disp)
print("config_sha", out["config_sha"])
