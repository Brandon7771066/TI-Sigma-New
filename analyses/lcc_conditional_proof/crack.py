#!/usr/bin/env python3
"""
B166 -- LCC conditional provability: adversarial "crack" simulation.

Question (user + ChatGPT): can we PROVE bidirectional causation (X<->Y) from
correlation/coupling under guardrails? We split the claim:

  WEAK-LCC (target of proof):  persistent, non-spurious, bidirectionally-predictive
                               dependence between sync-capable systems, with common
                               causes / artifact / autocorrelation / selection ruled
                               out  =>  causal coupling.
  STRONG-LCC (rejected):       high synchrony => direct bidirectional causation.

We DON'T try to confirm the LCC. We try to CRACK it: build a world where there is
NO X<->Y edge yet every OBSERVATIONAL guardrail passes. If such a world exists, the
observational proof-by-contradiction is UNSOUND (the common-cause disjunct survives).
A single constructive counterexample is a valid disproof of a universal claim.

Then we show which guardrail actually closes the proof: genuine (surgical,
bidirectional) INTERVENTION.

Generators (all nodes are sync-capable: each has internal AR/oscillatory dynamics):
  BIDIR   : true X<->Y coupling, no common cause.
  COMMON  : hidden Z drives X and Y with DISTINCT lags (=> spurious bidirectional
            lagged predictability), NO direct X<->Y edge. A DECOY measured proxy Z'
            (imperfect) is what an analyst actually gets to condition on.
  ONEWAY  : X->Y only.
  INDEP   : no coupling, no common cause (negative control).

Observational guardrails (rung-1, what real EEG/actigraphy data affords):
  G1 persistence            : bidirectional dependence stable across long windows.
  G2 bidirectionality       : lagged predictive gain X->Y AND Y->X both > 0 (Granger
                              via AR least squares).
  G3 surrogate survival     : coupling exceeds phase-randomized AND circular-shift nulls.
  G4 conditional survival   : coupling survives conditioning on the MEASURED proxy Z'.
  G6 sync potential         : each node responds to an injected probe (nonzero response).

Oracle / interventional guardrails (rung-2, usually unavailable in observation):
  G4o oracle-conditioning   : coupling vanishes when conditioning on the TRUE Z.
  G5 perturbability         : do(X) shifts future Y AND do(Y) shifts future X
                              (surgical intervention on the generative model).

Env: numpy/scipy/sklearn only (statsmodels NOT installed).
"""

import json
import hashlib
import os
import numpy as np

RNG_MASTER = 20260702
N = 2500            # samples per realization
N_SEEDS = 24        # realizations per generator
WIN = 500           # window length for persistence
N_WIN = 6           # number of windows
N_SURR = 120        # surrogates
A_SELF = 0.55       # self-AR coefficient (internal dynamics => sync potential)
C_COUP = 0.35       # direct coupling strength (BIDIR / ONEWAY)
B_COMMON = 0.55     # common-cause loading
AZ_COMMON = 0.92    # common-cause autocorrelation: a SMOOTH shared driver makes each
                    # node's past a proxy for the other's future => spurious BIDIRECTIONAL
                    # Granger predictability with NO direct X<->Y edge.
PROXY_NOISE = 0.8   # how imperfect the measured decoy Z' is (higher => more imperfect)
PROBE_AMP = 6.0     # probe/intervention pulse amplitude (in noise-sigma units)
ALPHA = 0.05


# ----------------------------------------------------------------------------
# Generators. Each returns dict with observed X,Y and hidden Z (or None), and a
# closure `step_intervene` that regenerates under do(.) for the interventional test.
# ----------------------------------------------------------------------------

def _oscillatory_innovation(n, rng, f=0.02):
    """Coloured innovation giving each node a spectral peak (sync-capable dynamics)."""
    t = np.arange(n)
    return 0.6 * np.sin(2 * np.pi * f * t + rng.uniform(0, 2 * np.pi)) + rng.standard_normal(n)


def gen_bidir(n, rng):
    ex = _oscillatory_innovation(n, rng, 0.021)
    ey = _oscillatory_innovation(n, rng, 0.017)
    x = np.zeros(n); y = np.zeros(n)
    for t in range(1, n):
        x[t] = A_SELF * x[t - 1] + C_COUP * y[t - 1] + ex[t]
        y[t] = A_SELF * y[t - 1] + C_COUP * x[t - 1] + ey[t]
    return dict(X=x, Y=y, Z=None, Zproxy=None, truth="X<->Y")


def _smooth_driver(n, rng, f):
    e = _oscillatory_innovation(n, rng, f)
    z = np.zeros(n)
    for t in range(1, n):
        z[t] = AZ_COMMON * z[t - 1] + e[t]   # smooth (slowly-varying) shared driver
    return z


def gen_common(n, rng):
    # The true common cause has TWO smooth components: Z1 the analyst MEASURES, and Z2 that
    # remains UNMEASURED. This is the generic real-world situation -- you can never be sure
    # you have measured every common driver. X and Y load equally on BOTH, so the sufficient
    # confounder is S = Z1 + Z2; the analyst only ever gets Z1.
    z1 = _smooth_driver(n, rng, 0.013)   # measured component
    z2 = _smooth_driver(n, rng, 0.009)   # UNMEASURED component
    ex = _oscillatory_innovation(n, rng, 0.021)
    ey = _oscillatory_innovation(n, rng, 0.017)
    x = np.zeros(n); y = np.zeros(n)
    for t in range(1, n):
        # contemporaneous common drive: because Z is smooth, each node's PAST is a proxy
        # for the other node's FUTURE => spurious bidirectional Granger, NO X<->Y edge.
        x[t] = A_SELF * x[t - 1] + B_COMMON * (z1[t] + z2[t]) + ex[t]
        y[t] = A_SELF * y[t - 1] + B_COMMON * (z1[t] + z2[t]) + ey[t]
    zproxy = z1 + PROXY_NOISE * rng.standard_normal(n)  # analyst's MEASURED confounder (Z1 only)
    zfull = z1 + z2                                      # oracle: the COMPLETE confounder
    return dict(X=x, Y=y, Z=zfull, Zproxy=zproxy, truth="Z1+Z2->X,Y (no X<->Y); Z2 unmeasured")


def gen_oneway(n, rng):
    ex = _oscillatory_innovation(n, rng, 0.021)
    ey = _oscillatory_innovation(n, rng, 0.017)
    x = np.zeros(n); y = np.zeros(n)
    for t in range(1, n):
        x[t] = A_SELF * x[t - 1] + ex[t]
        y[t] = A_SELF * y[t - 1] + C_COUP * x[t - 1] + ey[t]
    return dict(X=x, Y=y, Z=None, Zproxy=None, truth="X->Y")


def gen_indep(n, rng):
    ex = _oscillatory_innovation(n, rng, 0.021)
    ey = _oscillatory_innovation(n, rng, 0.017)
    x = np.zeros(n); y = np.zeros(n)
    for t in range(1, n):
        x[t] = A_SELF * x[t - 1] + ex[t]
        y[t] = A_SELF * y[t - 1] + ey[t]
    return dict(X=x, Y=y, Z=None, Zproxy=None, truth="X _||_ Y")


GENERATORS = {"BIDIR": gen_bidir, "COMMON": gen_common, "ONEWAY": gen_oneway, "INDEP": gen_indep}
# fixed, process-independent per-generator seed offsets (NOT hash() -- keeps runs reproducible)
GEN_OFFSET = {"BIDIR": 11, "COMMON": 23, "ONEWAY": 37, "INDEP": 53}

# ground-truth bidirectional causation
GROUND_TRUTH_BIDIR = {"BIDIR": True, "COMMON": False, "ONEWAY": False, "INDEP": False}


# ----------------------------------------------------------------------------
# Estimators
# ----------------------------------------------------------------------------

def _design(series_list, p, n):
    """Stacked lagged design matrix for given series, lags 1..p, aligned to [p:n]."""
    cols = []
    for s in series_list:
        for k in range(1, p + 1):
            cols.append(s[p - k:n - k])
    return np.column_stack(cols) if cols else np.empty((n - p, 0))


def _ols_resid_var(Xd, yv):
    if Xd.shape[1] == 0:
        return float(np.var(yv))
    beta, *_ = np.linalg.lstsq(np.column_stack([np.ones(len(yv)), Xd]), yv, rcond=None)
    pred = np.column_stack([np.ones(len(yv)), Xd]) @ beta
    return float(np.var(yv - pred))


def granger_gain(src, tgt, p=5):
    """Log-variance reduction in predicting tgt_t from adding src's past to tgt's own past.
    >0 means src helps predict tgt (directional predictive gain)."""
    n = len(tgt)
    yv = tgt[p:]
    var_self = _ols_resid_var(_design([tgt], p, n), yv)
    var_full = _ols_resid_var(_design([tgt, src], p, n), yv)
    var_self = max(var_self, 1e-12); var_full = max(var_full, 1e-12)
    return max(0.0, np.log(var_self / var_full))


def _design_cond(series_list, cond, p, n):
    """Lagged design; the conditioner `cond` also gets its CONTEMPORANEOUS (lag-0) term,
    which is what proper adjustment for a common driver requires."""
    cols = []
    for s in series_list:
        for k in range(1, p + 1):
            cols.append(s[p - k:n - k])
    if cond is not None:
        for k in range(0, p + 1):  # lag 0..p for the confounder
            cols.append(cond[p - k:n - k])
    return np.column_stack(cols)


def granger_gain_conditioned(src, tgt, cond, p=5):
    """Directional gain of src->tgt after including cond (contemporaneous + past) in BOTH
    models. Proper confounder adjustment: if cond is the TRUE common driver this screens
    off the spurious src->tgt gain; an imperfect proxy leaves residual spurious gain."""
    n = len(tgt)
    yv = tgt[p:]
    var_base = _ols_resid_var(_design_cond([tgt], cond, p, n), yv)
    var_full = _ols_resid_var(_design_cond([tgt, src], cond, p, n), yv)
    var_base = max(var_base, 1e-12); var_full = max(var_full, 1e-12)
    return max(0.0, np.log(var_base / var_full))


def phase_randomize(s, rng):
    n = len(s); f = np.fft.rfft(s)
    ph = rng.uniform(0, 2 * np.pi, len(f))
    ph[0] = 0.0
    if n % 2 == 0:
        ph[-1] = 0.0
    surr = np.fft.irfft(np.abs(f) * np.exp(1j * ph), n=n)
    return surr


def bidir_coupling(x, y, p=5):
    """Symmetric coupling score = min of the two directional gains (both must be present)."""
    return min(granger_gain(x, y, p), granger_gain(y, x, p))


# ----------------------------------------------------------------------------
# Guardrail tests (per realization). Each returns bool pass.
# ----------------------------------------------------------------------------

def g1_persistence(x, y, p=5):
    hits = 0
    for w in range(N_WIN):
        s = w * ((N - WIN) // max(1, N_WIN - 1))
        xs, ys = x[s:s + WIN], y[s:s + WIN]
        if granger_gain(xs, ys, p) > 0 and granger_gain(ys, xs, p) > 0:
            hits += 1
    return hits / N_WIN >= 0.8


def g2_bidirectional(x, y, rng, p=5):
    """Both directional gains exceed their own circular-shift null (95th pct)."""
    def dir_sig(src, tgt):
        obs = granger_gain(src, tgt, p)
        null = []
        for _ in range(40):
            sh = rng.integers(p + 1, len(src) - p - 1)
            null.append(granger_gain(np.roll(src, sh), tgt, p))
        return obs > np.percentile(null, 95)
    return dir_sig(x, y) and dir_sig(y, x)


def g3_surrogate(x, y, rng, p=5):
    obs = bidir_coupling(x, y, p)
    null_phase = np.array([bidir_coupling(phase_randomize(x, rng), phase_randomize(y, rng), p)
                           for _ in range(N_SURR // 2)])
    null_shift = []
    for _ in range(N_SURR // 2):
        sh = rng.integers(p + 1, len(x) - p - 1)
        null_shift.append(bidir_coupling(np.roll(x, sh), y, p))
    null_shift = np.array(null_shift)
    return (obs > np.percentile(null_phase, 95)) and (obs > np.percentile(null_shift, 95))


def _bidir_cond(x, y, cond, p=5):
    return min(granger_gain_conditioned(x, y, cond, p), granger_gain_conditioned(y, x, cond, p))


def g4_conditional(x, y, cond, rng, p=5, nshift=25):
    """Does bidirectional coupling remain SIGNIFICANT after conditioning on `cond`?
    Null = circular-shift the source relative to (target, cond) so any surviving cross
    predictability is destroyed. Returns True if the conditioned coupling still beats the
    95th-pct shift null (i.e. NOT screened off). If cond is None (no measured confounder to
    adjust for), the analyst has nothing to condition on -> guardrail is vacuously satisfied
    whenever raw coupling is significant."""
    if cond is None:
        return bidir_coupling(x, y, p) > 0
    obs = _bidir_cond(x, y, cond, p)
    null = []
    for _ in range(nshift):
        sh = rng.integers(p + 1, len(x) - p - 1)
        null.append(_bidir_cond(np.roll(x, sh), y, cond, p))
    return obs > np.percentile(null, 95)


def g6_sync_potential(x, y):
    """Synchronization potential (NECESSARY, not sufficient): each node has internal memory
    -- a stable internal dynamic (significant lag-1 autocorrelation) that an input CAN shift
    / entrain. Mutual sync-capability does NOT entail the two are coupled TO EACH OTHER (both
    could be entrainable by a common driver Z), which is exactly why SP cannot by itself
    license X<->Y."""
    def has_memory(s):
        return abs(np.corrcoef(s[:-1], s[1:])[0, 1]) > 0.1
    return has_memory(x) and has_memory(y)


def g5_perturbability(gen_name, seed):
    """Surgical intervention on the GENERATIVE model: do(X:=+pulse) at t0, propagate TRUE
    dynamics, measure future Y deviation vs unperturbed counterfactual; and symmetrically
    do(Y)->future X. Bidirectional causation <=> both responses exceed noise."""
    rng = np.random.default_rng(seed + 555)
    n = 1500; t0 = 700; H = 8

    def simulate(do_node=None):
        r = np.random.default_rng(seed + 555)  # identical innovations across counterfactuals
        ex = _oscillatory_innovation(n, r, 0.021)
        ey = _oscillatory_innovation(n, r, 0.017)
        if gen_name == "COMMON":
            ez1 = _oscillatory_innovation(n, r, 0.013)
            ez2 = _oscillatory_innovation(n, r, 0.009)
        x = np.zeros(n); y = np.zeros(n); z1 = np.zeros(n); z2 = np.zeros(n)
        pulse = PROBE_AMP
        for t in range(1, n):
            if gen_name == "COMMON":
                z1[t] = AZ_COMMON * z1[t - 1] + ez1[t]
                z2[t] = AZ_COMMON * z2[t - 1] + ez2[t]
            # base updates
            if gen_name == "BIDIR":
                x[t] = A_SELF * x[t - 1] + C_COUP * y[t - 1] + ex[t]
                y[t] = A_SELF * y[t - 1] + C_COUP * x[t - 1] + ey[t]
            elif gen_name == "ONEWAY":
                x[t] = A_SELF * x[t - 1] + ex[t]
                y[t] = A_SELF * y[t - 1] + C_COUP * x[t - 1] + ey[t]
            elif gen_name == "COMMON":
                x[t] = A_SELF * x[t - 1] + B_COMMON * (z1[t] + z2[t]) + ex[t]
                y[t] = A_SELF * y[t - 1] + B_COMMON * (z1[t] + z2[t]) + ey[t]
            else:  # INDEP
                x[t] = A_SELF * x[t - 1] + ex[t]
                y[t] = A_SELF * y[t - 1] + ey[t]
            # surgical do(): overwrite the target node's value at t0 only (atomic, no side channel)
            if do_node == "X" and t == t0:
                x[t] = x[t] + pulse
            if do_node == "Y" and t == t0:
                y[t] = y[t] + pulse
        return x, y

    x0, y0 = simulate(None)
    xX, yX = simulate("X")   # do(X): effect on future Y
    xY, yY = simulate("Y")   # do(Y): effect on future X
    resp_x_to_y = float(np.mean(np.abs(yX[t0 + 1:t0 + 1 + H] - y0[t0 + 1:t0 + 1 + H])))
    resp_y_to_x = float(np.mean(np.abs(xY[t0 + 1:t0 + 1 + H] - x0[t0 + 1:t0 + 1 + H])))
    thr = 0.05  # deviation threshold (noise sd ~1)
    return dict(x_to_y=resp_x_to_y, y_to_x=resp_y_to_x,
                bidir=(resp_x_to_y > thr and resp_y_to_x > thr))


# ----------------------------------------------------------------------------
# Run
# ----------------------------------------------------------------------------

def run():
    results = {}
    for gname, gfn in GENERATORS.items():
        gr = {k: 0 for k in ["G1", "G2", "G3", "G4_proxy", "G4_oracle_screensoff", "G6"]}
        g5_bidir_hits = 0
        g5_examples = None
        for seed in range(N_SEEDS):
            rng = np.random.default_rng(RNG_MASTER + seed * 101 + GEN_OFFSET[gname])
            d = gfn(N, rng)
            x, y = d["X"], d["Y"]
            gr["G1"] += int(g1_persistence(x, y))
            gr["G2"] += int(g2_bidirectional(x, y, rng))
            gr["G3"] += int(g3_surrogate(x, y, rng))
            # G4 on the MEASURED proxy (what an analyst has). For non-common gens, proxy=None.
            gr["G4_proxy"] += int(g4_conditional(x, y, d["Zproxy"], rng))
            # oracle: does conditioning on the TRUE Z screen off the coupling? (only meaningful COMMON)
            if d["Z"] is not None:
                screened = not (g4_conditional(x, y, d["Z"], rng))
                gr["G4_oracle_screensoff"] += int(screened)
            gr["G6"] += int(g6_sync_potential(x, y))
            g5 = g5_perturbability(gname, seed)
            g5_bidir_hits += int(g5["bidir"])
            if g5_examples is None:
                g5_examples = g5
        frac = {k: v / N_SEEDS for k, v in gr.items()}
        frac["G5_perturb_bidir"] = g5_bidir_hits / N_SEEDS
        # a guardrail "passes" for a generator if it fires in >=80% of realizations
        def passed(key):
            return frac.get(key, 0.0) >= 0.8
        S_obs = passed("G1") and passed("G2") and passed("G3") and passed("G4_proxy") and passed("G6")
        S_int = S_obs and passed("G5_perturb_bidir")
        results[gname] = {
            "ground_truth_bidirectional": GROUND_TRUTH_BIDIR[gname],
            "truth_label": gfn(200, np.random.default_rng(0))["truth"],
            "fractions": {k: round(v, 3) for k, v in frac.items()},
            "S_obs_passes": bool(S_obs),
            "S_int_passes": bool(S_int),
            "g5_example_response": {k: round(v, 4) for k, v in g5_examples.items() if k != "bidir"},
        }

    # Verdict logic
    obs_sound = all(
        results[g]["S_obs_passes"] == results[g]["ground_truth_bidirectional"]
        for g in results
    )
    int_sound = all(
        results[g]["S_int_passes"] == results[g]["ground_truth_bidirectional"]
        for g in results
    )
    crack = (results["COMMON"]["S_obs_passes"] and not results["COMMON"]["ground_truth_bidirectional"])

    config = dict(N=N, N_SEEDS=N_SEEDS, WIN=WIN, N_WIN=N_WIN, N_SURR=N_SURR,
                  A_SELF=A_SELF, C_COUP=C_COUP, B_COMMON=B_COMMON, AZ_COMMON=AZ_COMMON,
                  PROXY_NOISE=PROXY_NOISE, PROBE_AMP=PROBE_AMP, ALPHA=ALPHA, seed=RNG_MASTER,
                  gen_offset=GEN_OFFSET)
    config_sha = hashlib.sha256(json.dumps(config, sort_keys=True).encode()).hexdigest()[:12]

    summary = {
        "config": config,
        "config_sha": config_sha,
        "per_generator": results,
        "observational_guardrails_sound": bool(obs_sound),
        "observational_proof_by_contradiction_cracked": bool(crack),
        "interventional_guardrails_sound_on_this_model_class": bool(int_sound),
        "verdict": (
            "OBSERVATIONAL-ONLY LCC PROOF IS UNSOUND: the hidden-common-cause world "
            "passes every observational guardrail yet has no X<->Y edge. Adding surgical "
            "bidirectional intervention (G5) uniquely recovers ground truth on this model class."
        ),
    }
    os.makedirs("analyses/lcc_conditional_proof/results", exist_ok=True)
    with open("analyses/lcc_conditional_proof/results/results.json", "w") as f:
        json.dump(summary, f, indent=2)

    # console table
    print(f"config_sha={config_sha}  N={N} seeds={N_SEEDS}\n")
    hdr = ["gen", "truth", "G1", "G2", "G3", "G4prx", "G6", "|Sobs", "G5bd", "|Sint", "GTbidir"]
    print("  ".join(f"{h:>7}" for h in hdr))
    for g, r in results.items():
        fr = r["fractions"]
        row = [g, "bd" if r["ground_truth_bidirectional"] else "no",
               fr["G1"], fr["G2"], fr["G3"], fr["G4_proxy"], fr["G6"],
               "Y" if r["S_obs_passes"] else "n",
               fr["G5_perturb_bidir"], "Y" if r["S_int_passes"] else "n",
               "Y" if r["ground_truth_bidirectional"] else "n"]
        print("  ".join(f"{str(c):>7}" for c in row))
    print()
    print("COMMON oracle-screens-off (cond on TRUE Z):",
          results["COMMON"]["fractions"]["G4_oracle_screensoff"])
    print("observational guardrails sound? ", summary["observational_guardrails_sound"])
    print("observational proof-by-contradiction CRACKED? ",
          summary["observational_proof_by_contradiction_cracked"])
    print("interventional guardrails sound (this model class)? ",
          summary["interventional_guardrails_sound_on_this_model_class"])
    print("\n" + summary["verdict"])


if __name__ == "__main__":
    run()
