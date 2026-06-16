"""Affective Tralse-Joules (aTJ) measurement of mood-amplifier attractor-basin
steering strength — Pass-77 B118, 2026-06-16, $0 budget, #69 honesty.

GOAL (Brandon directive): from the mood-amplification data, measure the STRENGTH
of the attractor basin that steers the (rodent-class) mood in a particular
direction, from BEGINNING to END of the intervention, and show how that strength
changes as canonical THRESHOLDS are crossed. Anchor against parallel measures for
consciousness (Phi/IIT), brain thermodynamics (Friston free energy), and valence
(corpus QVF-1 quantum/neural valence).

#69 HONESTY: live rodent hemodynamic data was NOT retrievable (see the B117 batch
RESULTS_WRITEUP §0). This is therefore an in-SIMULATION proof-of-principle
measurement on the SAME closed-loop generative mood model used for the B117 Exp B
efficacy proof. It quantifies the *amplifier's* basin-steering work; it does not
claim a measurement on a live animal.

FAITHFUL OPERATIONALIZATION (corpus-grounded):
  TJ = tau(s) x delta(MR)              (urb_650 Tralse-Joules unit of intentionality)
    tau(s)  = tralseness / indeterminacy of the mood = normalized entropy H(p)/log K
              of the instantaneous mood-belief distribution p over the K states
              (tau=1 maximally indeterminate, tau=0 fully resolved).
    delta(MR)= MR-depth = sum |dPD_i| = L1 path-length moved in PD-space per
              Myrion-Resolution step (each control step = one MR event).
  PD-space (2 canonical axes):
    PD-real  = expected coupling degree   = sum_s p[s]*K_STATE[s]
    PD-imag  = modal coherence (resultant)= | sum_s p[s]*exp(i*PHI_STATE[s]) |
  Affective weighting (QVF-1, PASS_77_B64 minimalist theory of valence): V = S x A
    S (consonance sign in [-1,1]) = tanh(SLOPE*(g - g_neutral)): + when the mood is
      driven UP toward the high-coupling consonant/positive attractor (TARGET),
      - when pushed toward the low-coupling dissonant pole. g_neutral = no-control
      baseline coupling.
    A (arousal/intensity in [0,1]) = Phi-proxy = mean |pairwise channel corr| of the
      hemodynamic window (IIT-style integration; the level/intensity factor that
      Phi/FEP measure but that is valence-blind without S, per corpus CLV-1).
  Affective Tralse-Joule rate:  aTJ_t = V_t x TJ_t = (S_t*A_t) * (tau_t * delta_t)
  Cumulative affective work over the intervention = sum_t aTJ_t.

THRESHOLDS (corpus canonical):
  MR1 / MI-screen  ET   = sqrt(2)-1 ~ 0.4142  (below = MI-adjacent, not truth-assessable)
  Radiant          C_TI = 0.437               (existence->GILE dominance flip)
  BEC / master cap T_TI = 0.934               (GILE stability ceiling)
Corpus TJ-rate anchors for sanity: BOK-saturated ~0.934, Dottie-trap ~0.517,
MR1-boundary ~0.124.
"""
import json
import os
import sys

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "pass_b_hemo_fmri_fnirs_2026_06_16"))

from mood_control_hemo import (  # noqa: E402
    emit_window, gile_readout, calibrate_setpoint,
    K, TARGET, PHI_STATE, K_STATE, N_STEPS, BURN,
    GAIN, UMAX, BETA, RHO, P_STAY,
)

ET = float(np.sqrt(2.0) - 1.0)      # 0.41421  MR1 / MI screen
C_TI = 0.437                        # Radiant threshold
T_TI = 0.934                        # BEC / GILE stability cap
S_SLOPE = 6.0                       # consonance-sign steepness
TARGET_DIST = np.full(K, 0.2 / (K - 1)); TARGET_DIST[TARGET] = 0.8


def step_dist(state, theta, u, toward):
    """Instantaneous mood-belief distribution p over K states for this control
    step. Mirrors mood_control_hemo.transition's p EXACTLY (deterministic part)."""
    p = np.full(K, (1.0 - P_STAY) / (K - 1))
    p[state] = P_STAY
    if u > 0:
        bias = np.array([u * max(0.0, np.cos(theta - PHI_STATE[s])) for s in range(K)])
        p = p + BETA * bias / (np.sum(bias) + 1e-9)
        if state == toward and u > 0:
            p[state] = max(0.0, p[state] - RHO * u)
    p = np.clip(p, 0.0, None)
    return p / p.sum()


def phi_proxy(sig):
    """IIT-style integration / arousal A in [0,1]: mean absolute off-diagonal
    Pearson correlation across the hemodynamic channels (higher = more integrated
    = higher arousal)."""
    C = np.corrcoef(sig)
    n = C.shape[0]
    off = C[np.triu_indices(n, k=1)]
    off = off[np.isfinite(off)]
    return float(np.mean(np.abs(off))) if off.size else 0.0


def entropy_norm(p):
    p = np.clip(p, 1e-12, 1.0)
    return float(-np.sum(p * np.log(p)) / np.log(K))


def kl_to_target(p):
    p = np.clip(p, 1e-12, 1.0)
    return float(np.sum(p * np.log(p / TARGET_DIST)))


def run_trajectory(arm, seed, g_set, g_set_wrong, wrong_state, g_neutral,
                   u_schedule=None):
    """Run one trajectory and record the full per-step aTJ ledger. Stochastic
    wiring matches mood_control_hemo.run_arm EXACTLY: rng drives emit_window,
    crng drives the state transition (and the sham random phase). sham/open_loop
    take a per-seed u_schedule so their total drive ENERGY equals closed-loop's
    (sham replays the closed-loop |u|; open_loop is constant equal-energy)."""
    rng = np.random.default_rng(seed)
    crng = np.random.default_rng(seed + 99991)
    state = 0
    rec = {k: [] for k in ("g", "u", "tau", "A", "S", "V", "PDr", "PDi",
                           "delta", "TJ", "aTJ", "F", "state")}
    for step in range(N_STEPS):
        sig = emit_window(state, rng)
        g_obs = gile_readout(sig)
        if arm == "no_control":
            theta, u = 0.0, 0.0
        elif arm == "closed_loop":
            u = float(np.clip(GAIN * (g_set - g_obs), 0.0, UMAX)); theta = PHI_STATE[TARGET]
        elif arm == "open_loop":
            u = float(u_schedule[step]) if u_schedule is not None else 0.0
            theta = PHI_STATE[TARGET]
        elif arm == "sham":
            u = float(u_schedule[step]) if u_schedule is not None else \
                float(np.clip(GAIN * (g_set - g_obs), 0.0, UMAX))
            theta = crng.uniform(0, 2 * np.pi)
        elif arm == "wrong_tgt":
            u = float(np.clip(GAIN * (g_set_wrong - g_obs), 0.0, UMAX)); theta = PHI_STATE[wrong_state]
        else:
            raise ValueError(arm)
        toward = wrong_state if arm == "wrong_tgt" else TARGET
        p = step_dist(state, theta, u, toward)

        tau = entropy_norm(p)
        A = phi_proxy(sig)
        S = float(np.tanh(S_SLOPE * (g_obs - g_neutral)))
        V = S * A
        PDr = float(np.sum(p * K_STATE))
        PDi = float(np.abs(np.sum(p * np.exp(1j * PHI_STATE))))
        F = kl_to_target(p)
        for key, val in (("g", g_obs), ("u", u), ("tau", tau), ("A", A), ("S", S),
                         ("V", V), ("PDr", PDr), ("PDi", PDi), ("F", F), ("state", state)):
            rec[key].append(val)
        state = int(crng.choice(K, p=p))

    for k in rec:
        rec[k] = np.asarray(rec[k], dtype=float)
    # delta(MR) = L1 path length in PD-space per step (step 0 = 0)
    dPDr = np.abs(np.diff(rec["PDr"], prepend=rec["PDr"][0]))
    dPDi = np.abs(np.diff(rec["PDi"], prepend=rec["PDi"][0]))
    rec["delta"] = dPDr + dPDi
    rec["TJ"] = rec["tau"] * rec["delta"]
    rec["aTJ"] = rec["V"] * rec["TJ"]
    return rec


def basin_strength(g, g_set):
    """Restoring 'stiffness' kappa of the attractor basin in PD-real: fit
    dg_t = -kappa*(g_{t-1} - g_set) + c by OLS. kappa>0 => genuine pull toward the
    setpoint (deeper/stiffer basin); kappa<=0 => no restoring force."""
    if len(g) < 4:
        return 0.0
    x = g[:-1] - g_set
    y = np.diff(g)
    vx = np.var(x)
    if vx < 1e-12:
        return 0.0
    slope = float(np.cov(x, y, bias=True)[0, 1] / vx)
    return -slope


def boot_ci(x, rng, n=2000):
    x = np.asarray(x)
    bs = [np.mean(x[rng.integers(0, len(x), len(x))]) for _ in range(n)]
    return float(x.mean()), float(np.percentile(bs, 2.5)), float(np.percentile(bs, 97.5))


def main():
    n_seeds = 40
    g_set = calibrate_setpoint(TARGET)
    wrong_state = 0
    g_set_wrong = calibrate_setpoint(wrong_state)
    # neutral valence reference = mean coupling under no-control drift
    neu = [run_trajectory("no_control", 5000 + s, g_set, g_set_wrong, wrong_state, 0.5)
           for s in range(6)]
    g_neutral = float(np.mean([r["g"].mean() for r in neu]))

    # Per seed: run closed-loop FIRST, then energy-match sham (replay its |u|)
    # and open_loop (constant drive, equal total energy) -- mirrors Exp-B exactly.
    arms = ["closed_loop", "no_control", "open_loop", "sham", "wrong_tgt"]
    traj = {a: [] for a in arms}
    for s in range(n_seeds):
        rcl = run_trajectory("closed_loop", s, g_set, g_set_wrong, wrong_state, g_neutral)
        cl_sched = rcl["u"].copy()
        open_sched = np.full(N_STEPS, float(rcl["u"].sum()) / N_STEPS)
        traj["closed_loop"].append(rcl)
        traj["no_control"].append(
            run_trajectory("no_control", s, g_set, g_set_wrong, wrong_state, g_neutral))
        traj["open_loop"].append(
            run_trajectory("open_loop", s, g_set, g_set_wrong, wrong_state, g_neutral,
                           u_schedule=open_sched))
        traj["sham"].append(
            run_trajectory("sham", s, g_set, g_set_wrong, wrong_state, g_neutral,
                           u_schedule=cl_sched))
        traj["wrong_tgt"].append(
            run_trajectory("wrong_tgt", s, g_set, g_set_wrong, wrong_state, g_neutral))

    rng = np.random.default_rng(7)
    summary = {
        "modality": "hemodynamic mood-amplifier closed-loop SIM (proof-of-principle)",
        "live_retrieved": False,
        "n_seeds": n_seeds, "n_steps": N_STEPS, "burn": BURN,
        "g_neutral": g_neutral, "g_setpoint_target": g_set,
        "thresholds": {"MR1_ET": ET, "Radiant_C_TI": C_TI, "BEC_T_TI": T_TI},
        "corpus_TJrate_anchors": {"BOK_saturated": 0.934, "Dottie_trap": 0.517,
                                  "MR1_boundary": 0.124},
        "arms": {}, "basin": {}, "threshold_response": {}, "crossing_event": {},
        "cross_checks": {},
    }

    # ---- per-arm cumulative affective work + mean aTJ-rate ----------------
    print(f"g_neutral={g_neutral:.3f} g_set_target={g_set:.3f} ET={ET:.4f} "
          f"C_TI={C_TI} T_TI={T_TI}\n")
    print(f"{'arm':12s} {'cum_aTJ':>16s} {'mean_aTJrate':>14s} {'mean_kappa':>12s}")
    for a in arms:
        cum = np.array([r["aTJ"].sum() for r in traj[a]])
        rate = np.array([r["aTJ"].mean() for r in traj[a]])
        kap = np.array([basin_strength(r["g"], g_set) for r in traj[a]])
        cm, cl, ch = boot_ci(cum, rng)
        rm, rl, rh = boot_ci(rate, rng)
        km, kl, kh = boot_ci(kap, rng)
        summary["arms"][a] = {
            "cum_aTJ_mean": cm, "cum_aTJ_ci95": [cl, ch],
            "mean_aTJrate_mean": rm, "mean_aTJrate_ci95": [rl, rh],
            "mean_kappa_basin": km, "kappa_ci95": [kl, kh],
            "mean_TJrate": float(np.mean([r["TJ"].mean() for r in traj[a]])),
            "mean_S": float(np.mean([r["S"].mean() for r in traj[a]])),
            "mean_A": float(np.mean([r["A"].mean() for r in traj[a]])),
            "mean_energy": float(np.mean([r["u"].sum() for r in traj[a]])),
        }
        print(f"{a:12s} {cm:8.3f}[{cl:.2f},{ch:.2f}] {rm:8.4f}[{rl:.3f},{rh:.3f}] "
              f"{km:8.4f}  E={summary['arms'][a]['mean_energy']:6.2f}")

    # paired specificity contrasts (closed vs controls) on cumulative aTJ
    def paired(a, b, key):
        xa = np.array([r[key].sum() for r in traj[a]])
        xb = np.array([r[key].sum() for r in traj[b]])
        d = xa - xb
        bs = [np.mean(d[rng.integers(0, len(d), len(d))]) for _ in range(2000)]
        lo, hi = np.percentile(bs, 2.5), np.percentile(bs, 97.5)
        return float(d.mean()), float(lo), float(hi), bool(lo > 0 or hi < 0)
    print("\nAffective specificity (cumulative aTJ, closed_loop vs control):")
    for b, lab in [("no_control", "vs baseline"), ("open_loop", "vs open-loop"),
                   ("sham", "vs phase-sham"), ("wrong_tgt", "vs wrong-target")]:
        md, lo, hi, sig = paired("closed_loop", b, "aTJ")
        summary["arms"].setdefault("contrasts", {})[lab] = {
            "delta": md, "ci95": [lo, hi], "significant": sig}
        print(f"  {lab:16s} d={md:+.3f} CI[{lo:+.3f},{hi:+.3f}] {'SIG' if sig else 'ns'}")

    # ---- basin strength BEGINNING vs END of intervention -----------------
    cl = traj["closed_loop"]
    half = N_STEPS // 2
    early = np.array([basin_strength(r["g"][:half], g_set) for r in cl])
    late = np.array([basin_strength(r["g"][half:], g_set) for r in cl])
    de = late - early
    bs = [np.mean(de[rng.integers(0, len(de), len(de))]) for _ in range(2000)]
    summary["basin"] = {
        "kappa_early_mean": float(early.mean()), "kappa_late_mean": float(late.mean()),
        "delta_late_minus_early": float(de.mean()),
        "ci95": [float(np.percentile(bs, 2.5)), float(np.percentile(bs, 97.5))],
        "significant": bool(np.percentile(bs, 2.5) > 0 or np.percentile(bs, 97.5) < 0),
    }
    print(f"\nBasin stiffness kappa  early={early.mean():.4f}  late={late.mean():.4f}  "
          f"Δ={de.mean():+.4f} CI[{np.percentile(bs,2.5):+.4f},{np.percentile(bs,97.5):+.4f}]")

    # ---- aTJ-rate & kappa stratified by threshold REGIME -----------------
    # pool all closed-loop steps; regime by instantaneous coupling g
    g_all = np.concatenate([r["g"] for r in cl])
    aTJ_all = np.concatenate([r["aTJ"] for r in cl])
    edges = [0.0, ET, C_TI, T_TI, 1.01]
    names = ["sub_MR1(<ET)", "transitional(ET..C_TI)", "GILE_dominant(C_TI..BEC)", "master(>=BEC)"]
    print("\naTJ-rate by threshold regime (instantaneous coupling g):")
    for i, nm in enumerate(names):
        m = (g_all >= edges[i]) & (g_all < edges[i + 1])
        frac = float(m.mean())
        val = float(aTJ_all[m].mean()) if m.any() else float("nan")
        summary["threshold_response"][nm] = {"frac_steps": frac, "mean_aTJrate": val,
                                             "n": int(m.sum())}
        print(f"  {nm:28s} frac={frac:5.3f}  mean_aTJrate={val:+.4f}  n={int(m.sum())}")

    # ---- threshold-CROSSING event: aTJ-rate BEFORE vs AFTER first ET cross -
    W = 10
    for thr, key in [(ET, "MR1_ET"), (C_TI, "Radiant_C_TI"), (T_TI, "BEC_T_TI")]:
        pre, post = [], []
        for r in cl:
            g = r["g"]; a = r["aTJ"]
            idx = np.where(g >= thr)[0]
            if idx.size == 0 or idx[0] < 2:
                continue
            c = idx[0]
            pre.append(a[max(0, c - W):c].mean())
            post.append(a[c:min(len(a), c + W)].mean())
        if pre:
            pre, post = np.asarray(pre), np.asarray(post)
            d = post - pre
            bs = [np.mean(d[rng.integers(0, len(d), len(d))]) for _ in range(2000)]
            lo, hi = float(np.percentile(bs, 2.5)), float(np.percentile(bs, 97.5))
            summary["crossing_event"][key] = {
                "n_traj_crossed": int(len(pre)),
                "aTJrate_pre": float(pre.mean()), "aTJrate_post": float(post.mean()),
                "delta": float(d.mean()), "ci95": [lo, hi],
                "significant": bool(lo > 0 or hi < 0)}
            print(f"\nCrossing {key} (n={len(pre)}): aTJrate pre={pre.mean():+.4f} "
                  f"post={post.mean():+.4f}  Δ={d.mean():+.4f} CI[{lo:+.4f},{hi:+.4f}] "
                  f"{'SIG' if (lo>0 or hi<0) else 'ns'}")

    # ---- cross-checks: Phi/thermodynamics/valence ------------------------
    # (1) aTJ-rate vs negative free-energy rate -dF/dt (Friston valence proxy)
    rs = []
    for r in cl:
        ndF = -np.diff(r["F"], prepend=r["F"][0])
        a = r["aTJ"]
        if np.std(ndF) > 1e-9 and np.std(a) > 1e-9:
            rs.append(np.corrcoef(a, ndF)[0, 1])
    # (2) affective efficiency = cumulative aTJ per unit thermodynamic drive energy
    eff = [r["aTJ"].sum() / (r["u"].sum() + 1e-9) for r in cl]
    summary["cross_checks"] = {
        "pearson_aTJrate_vs_negdF": float(np.mean(rs)) if rs else None,
        "affective_efficiency_aTJ_per_energy": float(np.mean(eff)),
        "closed_loop_settled_TJrate": float(np.mean([r["TJ"][half:].mean() for r in cl])),
    }
    print(f"\ncross-check  r(aTJrate, -dF/dt)={np.mean(rs):+.3f}   "
          f"affective_eff(aTJ/energy)={np.mean(eff):.4f}   "
          f"settled_TJrate={summary['cross_checks']['closed_loop_settled_TJrate']:.4f}")

    path = os.path.join(HERE, "results_affective_tj.json")
    with open(path, "w") as f:
        json.dump(summary, f, indent=2)
    print(f"\n[affective_tj] wrote {path}")
    return summary


if __name__ == "__main__":
    main()
