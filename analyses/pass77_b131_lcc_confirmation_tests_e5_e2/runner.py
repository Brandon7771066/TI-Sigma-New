#!/usr/bin/env python3
"""
Pass-77 B131 -- LCC confirmation tests (continuation of B130/E3).
URB-620 Section 6 proposes a five-experiment programme (E1..E5). B130 executed E3
(dyad hyperscanning Granger asymmetry). This runner executes the next two most
natural LCC confirmation tests as pre-registration-grade METHOD-VALIDATION /
POWER simulations -- it uses NO human data.

  E5  LCC-Virus social-network propagation (URB-620 Section 6, E5).
      Claim: a high-GILE-L seed elevates LCC (HRV surrogate) across a social
      network with LOGISTIC (contagion, R0>1) spreading, not linear diffusion.
      Method-validation question: can the analysis tell TRUE social contagion
      from a SHARED-ENVIRONMENT confound that produces the SAME aggregate
      S-curve with no person-to-person transmission?

  E2  Emerick-Threshold neural phase transition (URB-620 Section 6, E2).
      Claim: value-guided coupling shifts DISCONTINUOUSLY at GILE = sqrt(2)-1
      ~= 0.4142 (a breakpoint), where the FEP predicts only smooth learning.
      Method-validation question: can change-point detection confirm a true
      breakpoint at 0.4142 (and recover it) WITHOUT being fooled by smooth
      curvature (a smooth nonlinear trend that has no breakpoint at all)?

#69 / Constructive-Honesty floor (applies to BOTH):
  This validates the experimental DESIGN + ANALYSIS (is it well-posed, adequately
  powered, and robust to the obvious confound?). It is NECESSARY, not SUFFICIENT:
  it is NOT evidence that the LCC Virus propagates in real humans, nor that a
  real neural phase transition exists. Those require the pre-registered human
  studies (E5/E2-SIM-F3). The headline lesson in each test is the SAME as E3:
  the naive statistic is confoundable; only a properly-controlled statistic
  (time-stratification in E5; beat-the-smooth-curve in E2) isolates the claim.
"""

import json
import hashlib
import time
import numpy as np

# ----------------------------------------------------------------------------- 
# Shared helpers
# ----------------------------------------------------------------------------- 

def aic_from_ssr(ssr, n, k):
    """Gaussian AIC up to an additive constant; k = # fitted params incl. variance."""
    ssr = max(ssr, 1e-12)
    return n * np.log(ssr / n) + 2.0 * k


def ols_ssr(X, y):
    """SSR of an OLS fit via least squares."""
    beta, _, _, _ = np.linalg.lstsq(X, y, rcond=None)
    resid = y - X @ beta
    return float(resid @ resid), beta


def wilson_ci(k, n, z=1.96):
    if n == 0:
        return (0.0, 0.0)
    p = k / n
    d = 1 + z * z / n
    c = p + z * z / (2 * n)
    h = z * np.sqrt(p * (1 - p) / n + z * z / (4 * n * n))
    return float((c - h) / d), float((c + h) / d)


# ============================================================================= 
# E5  --  LCC-Virus social-network propagation
# ============================================================================= 
#
# Three data-generating conditions on a random social graph (N nodes):
#   contagion     : TRUE susceptible->infected (SI) spread; a node's activation
#                   hazard rises with its number of already-activated NEIGHBOURS.
#   common_trend  : CONFOUND -- every node activates on an INDEPENDENT logistic
#                   schedule (shared calming environment / homophily). NO
#                   person-to-person transmission, yet the AGGREGATE curve is the
#                   same S-shape as contagion.
#   no_spread     : NULL -- tiny constant independent hazard, no S-curve.
#
# Three nested analyses, increasing in rigour:
#   A1 aggregate  : logistic vs linear growth fit to cumulative-activated
#                   fraction (Delta-AIC). This is the naive "is it logistic?" test.
#   A2 naive net  : pooled risk-set -- activation rate when >=1 neighbour active
#                   vs 0 neighbours active (one 2x2 table over ALL time).
#   A3 CMH        : the SAME neighbour test but Cochran-Mantel-Haenszel
#                   STRATIFIED BY TIME (controls the shared global trend).
#
# Expected, and the whole point: A1 fires for BOTH contagion AND common_trend
# (both are S-curves). A2 ALSO fires for common_trend, because late in time both
# baseline hazard AND neighbour-count rise together (a pure time confound). Only
# A3 (time-stratified) isolates true contagion -- exactly the E3 lesson (you must
# control the shared driver) transposed to a network.

def _er_graph(n, p, rng):
    A = (rng.random((n, n)) < p).astype(np.int8)
    A = np.triu(A, 1)
    A = A + A.T
    return A


def _logistic_curve_fit(t, frac):
    """Fit 3-param logistic L/(1+exp(-k(t-t0))) by coarse grid + linear inner solve.
    Returns SSR. Robust and cheap (no scipy optimiser needed)."""
    best = np.inf
    L_grid = [frac.max() * s for s in (0.9, 1.0, 1.1)]
    k_grid = np.linspace(0.05, 1.2, 16)
    t0_grid = np.linspace(t.min(), t.max(), 16)
    for L in L_grid:
        L = min(max(L, 1e-3), 1.5)
        for k in k_grid:
            for t0 in t0_grid:
                pred = L / (1.0 + np.exp(-k * (t - t0)))
                ssr = float(np.sum((frac - pred) ** 2))
                if ssr < best:
                    best = ssr
    return best


def simulate_e5_once(condition, rng, n=30, p_edge=0.15, T=60,
                     beta=0.07, base_hazard=0.004):
    A = _er_graph(n, p_edge, rng)
    infected = np.zeros(n, dtype=bool)
    act_time = np.full(n, -1)

    # risk-set accumulators for the neighbour test, per time stratum:
    # for each t: counts a=act&nbr>=1, b=noact&nbr>=1, c=act&nbr0, d=noact&nbr0
    strata = []
    cum_frac = np.zeros(T)

    if condition == "common_trend":
        # independent logistic activation schedule (no graph transmission)
        mid = T * 0.45
        s = T * 0.12
        u = rng.random(n)
        sched = mid + s * np.log(u / (1 - u))      # logistic-distributed times
        sched = np.clip(np.round(sched), 1, T - 1).astype(int)

    seed = rng.integers(n)
    infected[seed] = True
    act_time[seed] = 0
    cum_frac[0] = infected.mean()   # align trajectory with the seeded process

    for t in range(1, T):
        nbr_inf = A @ infected.astype(np.int8)      # infected-neighbour count
        susceptible = ~infected
        if condition == "contagion":
            hz = 1.0 - (1.0 - beta) ** nbr_inf      # rises with infected nbrs
            hz = hz + base_hazard
        elif condition == "common_trend":
            hz = (sched == t).astype(float)         # deterministic-ish schedule
            hz = np.clip(hz, 0, 1)
        else:  # no_spread
            hz = np.full(n, base_hazard)
        hz = np.clip(hz, 0, 1)

        draw = rng.random(n)
        newly = susceptible & (draw < hz)

        # build the 2x2 table for this stratum over the CURRENT risk set
        rs = susceptible
        has_nbr = nbr_inf >= 1
        a = int(np.sum(rs & has_nbr & newly))
        b = int(np.sum(rs & has_nbr & ~newly))
        c = int(np.sum(rs & ~has_nbr & newly))
        d = int(np.sum(rs & ~has_nbr & ~newly))
        if (a + b) > 0 and (c + d) > 0 and (a + c) >= 0:
            strata.append((a, b, c, d))

        infected[newly] = True
        act_time[newly] = t
        cum_frac[t] = infected.mean()

    t_axis = np.arange(T, dtype=float)

    # --- A1 aggregate: logistic vs linear on cumulative fraction ---
    ssr_log = _logistic_curve_fit(t_axis, cum_frac)
    X_lin = np.column_stack([np.ones(T), t_axis])
    ssr_lin, _ = ols_ssr(X_lin, cum_frac)
    aic_log = aic_from_ssr(ssr_log, T, 4)   # L,k,t0,var
    aic_lin = aic_from_ssr(ssr_lin, T, 3)
    a1_prefers_logistic = (aic_lin - aic_log) > 2.0

    # --- A2 naive pooled neighbour test (2x2 over all strata summed) ---
    A2 = np.sum([s[0] for s in strata]) if strata else 0
    B2 = np.sum([s[1] for s in strata]) if strata else 0
    C2 = np.sum([s[2] for s in strata]) if strata else 0
    D2 = np.sum([s[3] for s in strata]) if strata else 0
    a2_z = _two_prop_z(A2, A2 + B2, C2, C2 + D2)

    # --- A3 CMH stratified by time ---
    a3_z = _cmh_z(strata)

    return {
        "a1_prefers_logistic": bool(a1_prefers_logistic),
        "a2_z": float(a2_z),
        "a3_z": float(a3_z),
        "final_frac": float(cum_frac[-1]),
    }


def _two_prop_z(x1, n1, x2, n2):
    if n1 == 0 or n2 == 0:
        return 0.0
    p1, p2 = x1 / n1, x2 / n2
    p = (x1 + x2) / (n1 + n2)
    se = np.sqrt(p * (1 - p) * (1 / n1 + 1 / n2))
    if se == 0:
        return 0.0
    return (p1 - p2) / se      # one-sided: contagion => p1 (has-nbr) > p2


def _cmh_z(strata):
    """Cochran-Mantel-Haenszel one-sided z; strata = list of (a,b,c,d).
    a=act&nbr>=1, b=noact&nbr>=1, c=act&nbr0, d=noact&nbr0."""
    num = 0.0
    var = 0.0
    for (a, b, c, d) in strata:
        n = a + b + c + d
        if n < 2:
            continue
        r1 = a + b           # nbr>=1 row
        r2 = c + d           # nbr0 row
        col1 = a + c         # activated col
        col2 = b + d
        if r1 == 0 or r2 == 0 or col1 == 0 or col2 == 0:
            continue
        ea = r1 * col1 / n
        va = r1 * r2 * col1 * col2 / (n * n * (n - 1))
        num += (a - ea)
        var += va
    if var <= 0:
        return 0.0
    return num / np.sqrt(var)


def run_e5(cfg, z_crit=1.645):
    reps, seed0 = cfg["reps"], cfg["seed0"]
    conds = ["contagion", "common_trend", "no_spread"]
    out = {}
    for ci, cond in enumerate(conds):
        a1 = a2 = a3 = 0
        zs_a3 = []
        for r in range(reps):
            rng = np.random.default_rng(seed0 + 1000 * ci + r)
            res = simulate_e5_once(cond, rng, n=cfg["n_nodes"],
                                   p_edge=cfg["p_edge"], T=cfg["T"],
                                   beta=cfg["beta"], base_hazard=cfg["base_hazard"])
            a1 += int(res["a1_prefers_logistic"])
            a2 += int(res["a2_z"] > z_crit)
            a3 += int(res["a3_z"] > z_crit)
            zs_a3.append(res["a3_z"])
        out[cond] = {
            "n": reps,
            "A1_logistic_rate": a1 / reps,
            "A1_ci": wilson_ci(a1, reps),
            "A2_naive_net_rate": a2 / reps,
            "A2_ci": wilson_ci(a2, reps),
            "A3_cmh_rate": a3 / reps,
            "A3_ci": wilson_ci(a3, reps),
            "A3_z_mean": float(np.mean(zs_a3)),
        }
    return out


# ============================================================================= 
# E2  --  Emerick-Threshold phase transition (change-point detection)
# ============================================================================= 
#
# x = GILE composite ~ U(0,1); y = a connectivity/behaviour readout.
# Conditions:
#   threshold     : TRUE phase transition -- a DISCONTINUOUS jump at
#                   theta0 = sqrt(2)-1 ~= 0.4142 (the Emerick Threshold). This is
#                   what "phase transition / non-linear discontinuity" means;
#                   a smooth polynomial cannot reproduce a genuine step.
#   linear        : NULL -- straight line.
#   quad_curve    : CONFOUND-A -- pure quadratic curvature, no breakpoint.
#   smooth_curve  : CONFOUND-B -- a smooth logistic bend, no breakpoint. A
#                   breakpoint model beats a straight LINE on these too, so
#                   "beats a line" is NOT enough.
#
# Smooth alternatives (OLS): linear [1,x]; quadratic [1,x,x^2]; cubic
# [1,x,x^2,x^3]. Discontinuous breakpoint model: [1, x, 1(x>=theta), (x-theta)+]
# with theta grid-searched (a jump AND a slope change).
#   NAIVE test  : breakpoint beats LINEAR by Delta-AIC > 4 -> "threshold!"
#                 (fooled by any curvature).
#   PROPER test : breakpoint beats the BEST SMOOTH model (min AIC over
#                 lin/quad/cubic) by Delta-AIC > 4. This is the Davies-test
#                 analogue: a discontinuity NO smooth polynomial can capture.
#                 Also recover theta_hat and check it ~= 0.4142.

THETA0 = np.sqrt(2.0) - 1.0     # 0.41421356...


def _fit_breakpoint(x, y, grid):
    """Discontinuous segmented fit: intercept jump + slope change at theta."""
    best_ssr = np.inf
    best_theta = np.nan
    for th in grid:
        step = (x >= th).astype(float)
        Xs = np.column_stack([np.ones_like(x), x, step, np.clip(x - th, 0, None)])
        ssr, _ = ols_ssr(Xs, y)
        if ssr < best_ssr:
            best_ssr = ssr
            best_theta = th
    return best_ssr, best_theta


def _best_smooth_aic(x, y, n):
    """Best AIC over linear / quadratic / cubic smooth models."""
    aics = {}
    X_lin = np.column_stack([np.ones(n), x])
    X_quad = np.column_stack([np.ones(n), x, x ** 2])
    X_cub = np.column_stack([np.ones(n), x, x ** 2, x ** 3])
    aics["lin"] = aic_from_ssr(ols_ssr(X_lin, y)[0], n, 3)
    aics["quad"] = aic_from_ssr(ols_ssr(X_quad, y)[0], n, 4)
    aics["cub"] = aic_from_ssr(ols_ssr(X_cub, y)[0], n, 5)
    return aics


def _gen_e2(condition, rng, n, noise, jump=1.4):
    x = rng.uniform(0, 1, n)
    if condition == "threshold":
        y = 0.4 * x + jump * (x >= THETA0).astype(float)   # genuine jump
    elif condition == "linear":
        y = 1.2 * x
    elif condition == "quad_curve":
        y = 2.0 * (x - 0.15) ** 2
    else:  # smooth_curve : logistic bend, no breakpoint
        y = 1.6 / (1.0 + np.exp(-5.0 * (x - 0.5)))
    y = y - y.mean() + rng.normal(0, noise, n)
    return x, y


def simulate_e2_once(condition, rng, n=60, noise=0.45):
    x, y = _gen_e2(condition, rng, n, noise)
    aics = _best_smooth_aic(x, y, n)
    best_smooth = min(aics.values())
    grid = np.linspace(0.15, 0.85, 25)
    ssr_bp, theta_hat = _fit_breakpoint(x, y, grid)
    aic_bp = aic_from_ssr(ssr_bp, n, 6)        # 4 coef + theta(grid-searched) + var
    naive = (aics["lin"] - aic_bp) > 4.0
    proper = (best_smooth - aic_bp) > 4.0
    return {
        "naive": bool(naive),
        "proper": bool(proper),
        "theta_hat": float(theta_hat),
        "d_bp_vs_bestsmooth": float(best_smooth - aic_bp),
    }


def run_e2(cfg):
    reps, seed0, noise = cfg["reps"], cfg["seed0"], cfg["noise"]
    conds = ["threshold", "linear", "quad_curve", "smooth_curve"]
    out = {}
    for ci, cond in enumerate(conds):
        naive = proper = 0
        thetas = []
        for r in range(reps):
            rng = np.random.default_rng(seed0 + 7000 * ci + r)
            res = simulate_e2_once(cond, rng, n=cfg["n"], noise=noise)
            naive += int(res["naive"])
            proper += int(res["proper"])
            if res["proper"]:
                thetas.append(res["theta_hat"])
        rec = {
            "n": reps,
            "naive_detect_rate": naive / reps,
            "naive_ci": wilson_ci(naive, reps),
            "proper_detect_rate": proper / reps,
            "proper_ci": wilson_ci(proper, reps),
        }
        if thetas:
            rec["theta_hat_mean"] = float(np.mean(thetas))
            rec["theta_hat_sd"] = float(np.std(thetas))
            rec["theta_bias_vs_0p4142"] = float(np.mean(thetas) - THETA0)
        out[cond] = rec
    return out


def run_e2_power_curve(reps, seed0):
    """Power of the PROPER test on the threshold condition vs jump size."""
    curve = []
    for di, jump in enumerate([0.0, 0.4, 0.8, 1.2, 1.6, 2.0]):
        hits = 0
        for r in range(reps):
            rng = np.random.default_rng(seed0 + 13000 * di + r)
            x = rng.uniform(0, 1, 60)
            y = 0.4 * x + jump * (x >= THETA0).astype(float)
            y = y - y.mean() + rng.normal(0, 0.45, 60)
            aics = _best_smooth_aic(x, y, 60)
            ssr_bp, _ = _fit_breakpoint(x, y, np.linspace(0.15, 0.85, 25))
            d = min(aics.values()) - aic_from_ssr(ssr_bp, 60, 6)
            hits += int(d > 4.0)
        curve.append({"jump_size": jump, "power": hits / reps})
    return curve


# ----------------------------------------------------------------------------- 
def main():
    t0 = time.time()
    config = {
        "E5": {"n_nodes": 30, "p_edge": 0.15, "T": 60, "beta": 0.07,
               "base_hazard": 0.004, "reps": 400, "z_crit": 1.645, "seed0": 4131},
        "E2": {"n": 60, "noise": 0.45, "theta0": float(THETA0),
               "grid": "0.15..0.85 x25", "bp_params_k": 6, "reps": 600,
               "seed0": 9131},
        "honesty": "method-validation only; NO human data; necessary-not-sufficient",
    }
    config_sha = hashlib.sha256(
        json.dumps(config, sort_keys=True).encode()).hexdigest()[:12]

    print("=" * 72)
    print("B131  LCC confirmation tests  (E5 network propagation, E2 threshold)")
    print("config_sha", config_sha)
    print("=" * 72)

    e5 = run_e5(config["E5"], z_crit=config["E5"]["z_crit"])
    print("\n--- E5: LCC-Virus network propagation ---")
    print(f"{'condition':<14}{'A1 logistic':>14}{'A2 naive-net':>14}{'A3 CMH(time)':>14}")
    for c in ["contagion", "common_trend", "no_spread"]:
        r = e5[c]
        print(f"{c:<14}{r['A1_logistic_rate']:>14.3f}"
              f"{r['A2_naive_net_rate']:>14.3f}{r['A3_cmh_rate']:>14.3f}")

    e2 = run_e2(config["E2"])
    print("\n--- E2: Emerick-Threshold change-point detection ---")
    print(f"{'condition':<14}{'naive>lin':>12}{'proper':>10}{'theta_hat':>12}")
    for c in ["threshold", "linear", "quad_curve", "smooth_curve"]:
        r = e2[c]
        th = r.get("theta_hat_mean", float("nan"))
        print(f"{c:<14}{r['naive_detect_rate']:>12.3f}"
              f"{r['proper_detect_rate']:>10.3f}{th:>12.4f}")
    e2_curve = run_e2_power_curve(300, config["E2"]["seed0"] + 1)
    print("\n  E2 proper-test power vs jump size:")
    for pt in e2_curve:
        print(f"    jump={pt['jump_size']:.1f}  power={pt['power']:.3f}")

    runtime = time.time() - t0
    results = {
        "batch": "pass77_b131",
        "config": config,
        "config_sha": config_sha,
        "theta0_emerick": float(THETA0),
        "E5_network_propagation": e5,
        "E2_threshold_detection": e2,
        "E2_power_curve": e2_curve,
        "runtime_sec": round(runtime, 1),
        "honesty_floor": (
            "Method-validation/power sims only; NO human data. Confirms the E5/E2 "
            "DESIGNS are well-posed, adequately powered, and -- crucially -- that "
            "only a confound-controlled statistic (time-stratified CMH for E5; "
            "beat-the-smooth-curve for E2) isolates the claim. NECESSARY, not "
            "sufficient: not evidence the LCC Virus propagates in humans nor that "
            "a real neural phase transition exists (E5/E2-SIM-F3 = the human study)."
        ),
    }
    with open("analyses/pass77_b131_lcc_confirmation_tests_e5_e2/results.json", "w") as f:
        json.dump(results, f, indent=2)
    print(f"\nruntime {runtime:.1f}s -> results.json written")


if __name__ == "__main__":
    main()
