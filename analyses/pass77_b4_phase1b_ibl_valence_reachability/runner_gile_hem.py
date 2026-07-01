"""
Pass-77-B4 Phase-1B HEM-GILE — IBL Valence-Reachability re-tested with the canonical
UOP "Truth */+ Existence" tradeoff instead of the legacy M_r = L*E.

WHY THIS RUNNER:
Per Brandon's directive, retire the legacy multiplicative M_r = L*E and re-run the
Phase-1B reachability tests on the canonical HEM-GILE Unified Optimization Principle
(UOP) J-score, identical to the operationalization already used in Phase-1A
(pass77_b4_phase1a_rodent_mood_trajectory/runner_v2.py:compute_J_window):

    Truth axis  G = mean gamma-PLV (30-80Hz) across channel pairs, in [0,1]; cap G*=0.93.
    Exist axis  H = theta / (theta + delta), in [0,1], NO cap.
    f(G) = ln(1+G)                              for G <= 0.93
         = ln(1+0.93) - alpha*(G-0.93)^2        for G  > 0.93   (alpha=10)
    g(H) = ln(1+H)

    THE CANONICAL DUAL "*/+" OPERATOR (Truth */+ Existence; APERIODIC_DUAL / B83 lineage):
    Reality = alpha*(L x E) + beta*(L + E) -- the Einstein-tiling dual where BOTH the
    multiplicative (hyperconnection) and additive (existence) modes are combined. Mapping
    the two operands to our neural axes T_bound=f(G) (Truth) and E_bound=g(H) (Existence):

      J_mult = T_bound * E_bound      # L x E HYPERCONNECTION GATE: fires only when BOTH
                                      #   truth-coherence AND existence-arousal are present;
                                      #   zero in either factor annihilates the product.
      J_add  = T_bound + E_bound      # L + E EXISTENCE (substitutable; survives if one axis
                                      #   is zero). This is the legacy additive-only J.
      J_dual = J_mult + J_add         # literal "*/+" = (T x E) + (T + E). PRIMARY metric.

    Earlier additive-only runs used J_add alone -- literally half the operator -- which is
    why activating Existence DILUTED rather than GATED the signal. The multiplicative term
    is the component that detects a genuinely *reached* mood state (reward co-activating
    gamma-coherence AND theta-arousal together). dJ is reported for ALL THREE modes per test
    so we can see which mode carries the signal; J_dual is the pre-registered primary.

WHY VISUAL CORTEX (not CA1):
The CA1 HEM-GILE run would be uninformative for the EXISTENCE axis: in hippocampus
theta is so dominant that H -> ~1 saturates (the legacy E term hit its cap on 100% of
windows). Neocortex (Primary visual area, 118ch on this same sub-NR-0028 probe) is the
natural place where theta/delta is NOT saturated, so the H/Existence term actually
carries variance and the FULL Truth+Existence instrument is exercised.

METHODOLOGY (sound, #69):
  * Same anatomically-valid session sub-NR-0028, chosen before any J result.
  * Channels restricted to a single neocortical region family ("Primary visual area",
    substring match across cortical layers), 'void' excluded.
  * Exact event-locked segments (M_r/J computed DIRECTLY on the raw [-1.5,-0.5]s baseline
    and [0,+1]s response segments per event) -- no sliding-grid center-time leakage.
  * SAME pre-registered effect-size thresholds as the M_r runs (Cohen's d, Kruskal
    epsilon^2 are scale-invariant, so they transfer across the metric change).

PRE-REGISTERED (thresholds identical to the M_r runners):
  F-PHASE1B-1c (stimulus reaction): per stim-onset, dJ = mean(J[0,+1]s)-mean(J[-1.5,-0.5]s).
    Cohen's d over events + bootstrap-95%-CI. PASS d>0.30 & CI excl 0;
    INCONCLUSIVE |d| in [0.15,0.30]; else REFUTED.
  F-PHASE1B-2c (valence proxy): feedback-locked dJ, rewarded vs error.
    Mann-Whitney + Kruskal + epsilon^2. PASS p<0.01 & eps2>0.06; INCONCLUSIVE p<0.05;
    else REFUTED. Gated on >=5 events per outcome.

#69 SCOPE (unchanged): pre-recorded => reachability necessary-condition ONLY; single
session => cross-animal DEFERRED; valence co-varies with licking/arousal => correlate
not pure code.

DATASET: DANDI:000409, session sub-NR-0028 ses-f56194bc.
Overridable via env: SESSION, TARGET_REGION, REGION_MATCH(exact|contains), OFFSET_SEC,
MAX_DURATION_SEC, MAX_CHANNELS, RUN_TAG.
"""
import json, math, os, time, traceback, warnings
from pathlib import Path
import numpy as np

warnings.filterwarnings("ignore")
OUT_DIR = Path(__file__).parent
_TAG = os.environ.get("RUN_TAG", "")
OUT = OUT_DIR / (f"results_gilehem{('_'+_TAG) if _TAG else ''}.json")
LOG = OUT_DIR / (f"runner_gile_hem{('_'+_TAG) if _TAG else ''}.log")


def log(m):
    line = f"[{time.strftime('%H:%M:%S')}] {m}"
    print(line, flush=True)
    with open(LOG, "a") as f:
        f.write(line + "\n")


DANDISET = "000409"
SESSION = os.environ.get("SESSION", "sub-NR-0028/sub-NR-0028_ses-f56194bc-8215-4ae8-bc6a-89781ad8e050")
PROC_PATH = f"{SESSION}_desc-processed_behavior+ecephys.nwb"
RAW_PATH = f"{SESSION}_desc-raw_ecephys.nwb"
TARGET_REGION = os.environ.get("TARGET_REGION", "Primary visual area")
REGION_MATCH = os.environ.get("REGION_MATCH", "contains")  # 'exact' | 'contains'
SEED = 27182818
np.random.seed(SEED)

GAMMA_LO, GAMMA_HI = 30.0, 80.0
THETA_LO, THETA_HI = 6.0, 10.0
DELTA_LO, DELTA_HI = 1.0, 4.0
WINDOW_SEC = 1.0
STEP_SEC = 0.5
BASELINE = (-1.5, -0.5)
RESPONSE = (0.0, 1.0)
MAX_CHANNELS = int(os.environ.get("MAX_CHANNELS", "6"))
OFFSET_SEC = int(os.environ.get("OFFSET_SEC", "10"))
MAX_DURATION_SEC = int(os.environ.get("MAX_DURATION_SEC", "300"))
LF_RATE_DEFAULT = 2500.0

G_STAR = 0.93
ALPHA_J = 10.0
D_PASS = 0.30
D_INCONCLUSIVE_LO = 0.15
KW_P_PASS = 0.01
ETA2_PASS = 0.06


def bandpower(x, fs, lo, hi):
    from scipy.signal import welch
    # CANONICAL resolution: match Phase-1A compute_J_window (nperseg = fs*1.0 => df~=1Hz).
    # fs*0.5 (df~=2Hz) undersamples the 1-4Hz delta band and spuriously zeroes it out.
    nperseg = min(int(fs * 1.0), len(x))
    if nperseg < 16:
        return 0.0
    f, Pxx = welch(x, fs=fs, nperseg=nperseg)
    mask = (f >= lo) & (f <= hi)
    return float(np.trapz(Pxx[mask], f[mask])) if mask.any() else 0.0


def gamma_plv(x1, x2, fs):
    from scipy.signal import butter, filtfilt, hilbert
    if len(x1) < int(fs * 0.3):
        return 0.0
    nyq = fs / 2.0
    lo, hi = GAMMA_LO / nyq, min(GAMMA_HI / nyq, 0.99)
    if hi <= lo:
        return 0.0
    try:
        b, a = butter(4, [lo, hi], btype="band")
        s1 = filtfilt(b, a, x1); s2 = filtfilt(b, a, x2)
        p1 = np.angle(hilbert(s1)); p2 = np.angle(hilbert(s2))
        return float(np.abs(np.mean(np.exp(1j * (p1 - p2)))))
    except Exception:
        return 0.0


def f_G(g, alpha=ALPHA_J):
    if g <= G_STAR:
        return math.log(1.0 + g)
    return math.log(1.0 + G_STAR) - alpha * (g - G_STAR) ** 2


def g_H(h):
    return math.log(1.0 + max(float(h), 0.0))


MODES = ("add", "mult", "dual")


def J_modes(T_bound, E_bound):
    """The canonical dual */+ operator over the two per-axis bounds.
    add  = T+E (L+E existence); mult = T*E (LxE hyperconnection gate);
    dual = T*E + T+E (literal '*/+', primary)."""
    j_add = T_bound + E_bound
    j_mult = T_bound * E_bound
    return {"add": j_add, "mult": j_mult, "dual": j_mult + j_add}


def compute_J(seg, fs, pairs):
    """Canonical HEM-GILE UOP dual operator (Phase-1A compute_J_window axes, B83 dual */+).
    G = mean gamma-PLV (truth axis, cap 0.93); H = theta/(theta+delta) (existence axis).
    Returns (modes_dict, G, H) where modes_dict has add/mult/dual J values."""
    plvs = [gamma_plv(seg[i], seg[j], fs) for i, j in pairs]
    G = float(np.mean(plvs)) if plvs else 0.0
    avg = np.mean(seg, axis=0)
    theta = bandpower(avg, fs, THETA_LO, THETA_HI)
    delta = bandpower(avg, fs, DELTA_LO, DELTA_HI)
    H = float(theta / (theta + delta + 1e-12))
    return J_modes(f_G(G), g_H(H)), G, H


def cohens_d(arr):
    arr = np.asarray(arr, dtype=float)
    if len(arr) < 2 or np.std(arr, ddof=1) == 0:
        return 0.0
    return float(np.mean(arr) / np.std(arr, ddof=1))


def bootstrap_ci(arr, n=2000, alpha=0.05):
    arr = np.asarray(arr)
    if len(arr) < 2:
        return (0.0, 0.0)
    rng = np.random.default_rng(SEED)
    means = [np.mean(rng.choice(arr, size=len(arr), replace=True)) for _ in range(n)]
    return (float(np.quantile(means, alpha / 2)), float(np.quantile(means, 1 - alpha / 2)))


def find_lf_series(hr):
    acq = hr["acquisition"]
    def ndt(g):
        v = g.attrs.get("neurodata_type", b"")
        return v.decode() if isinstance(v, bytes) else str(v)
    cands = [k for k in acq.keys() if "LF" in k and "data" in acq[k]
             and getattr(acq[k]["data"], "ndim", 0) == 2 and ndt(acq[k]) == "ElectricalSeries"]
    if not cands:
        cands = [k for k in acq.keys() if "Electrical" in k and "data" in acq[k]
                 and getattr(acq[k]["data"], "ndim", 0) == 2]
    if not cands:
        raise RuntimeError("no LF ElectricalSeries found")
    return sorted(cands)[0], acq[sorted(cands)[0]]


def lf_timing(g):
    try:
        if "starting_time" in g:
            st = g["starting_time"]
            return float(np.asarray(st)), float(st.attrs.get("rate", LF_RATE_DEFAULT))
    except Exception:
        pass
    try:
        if "timestamps" in g and g["timestamps"].shape[0] >= 2:
            ts = g["timestamps"]; t0 = float(ts[0]); tN = float(ts[-1]); N = ts.shape[0]
            return t0, ((N - 1) / (tN - t0) if tN > t0 else LF_RATE_DEFAULT)
    except Exception:
        pass
    return 0.0, LF_RATE_DEFAULT


def region_channels(hr, target, match=REGION_MATCH):
    """Channel indices for the target region. match='exact' requires location==target;
    match='contains' takes all gray-matter layers whose label contains target (e.g. all
    'Primary visual area layer N'). 'void' is never returned and is rejected as a target."""
    if target == "void":
        raise ValueError("target region 'void' is out-of-brain; choose gray matter")
    et = hr["general/extracellular_ephys/electrodes"]
    loc = np.asarray(et["location"][:])
    loc = [v.decode() if isinstance(v, bytes) else str(v) for v in loc]
    if match == "contains":
        idx = [i for i, l in enumerate(loc) if target.lower() in l.lower() and l != "void"]
    else:
        idx = [i for i, l in enumerate(loc) if l == target and l != "void"]
    return idx, loc


def _seg_J(data, fs, pairs, lo_samp, hi_samp):
    """Returns the per-mode J dict {add,mult,dual} for the segment, or None if invalid."""
    if lo_samp < 0 or hi_samp > data.shape[1] or (hi_samp - lo_samp) < int(0.3 * fs):
        return None
    modes, _, _ = compute_J(data[:, lo_samp:hi_samp], fs, pairs)
    return modes


def event_delta_direct(data, fs, pairs, i_lo, t_off, t_ev):
    """Exact event-locked dJ = J(response segment) - J(baseline segment), per mode.
    Returns {add,mult,dual} of deltas, or None if either segment is invalid."""
    def s(t):
        return int(round((t - t_off) * fs)) - i_lo
    jb = _seg_J(data, fs, pairs, s(t_ev + BASELINE[0]), s(t_ev + BASELINE[1]))
    jr = _seg_J(data, fs, pairs, s(t_ev + RESPONSE[0]), s(t_ev + RESPONSE[1]))
    if jb is None or jr is None:
        return None
    return {m: jr[m] - jb[m] for m in MODES}


def main():
    results = {
        "pass": "77-B4", "phase": "1B-HEM-GILE", "dandiset": DANDISET, "session": SESSION,
        "target_region": TARGET_REGION, "region_match": REGION_MATCH,
        "seed": SEED, "prereg_locked": True,
        "instrument_canonical": "HEM-GILE UOP J = f(G)+g(H); G=gamma-PLV(cap0.93), H=theta/(theta+delta)",
        "supersedes_metric": "legacy M_r = L*E (multiplicative)",
        "scope_limits": [
            "pre-recorded => reachability necessary-condition ONLY",
            "single session => cross-animal DEFERRED",
            "valence co-varies with licking/arousal => correlate not pure code",
        ],
        "config": {"window_sec": WINDOW_SEC, "step_sec": STEP_SEC,
                   "baseline_s": BASELINE, "response_s": RESPONSE, "G_star": G_STAR,
                   "alpha_J": ALPHA_J, "max_channels": MAX_CHANNELS, "offset_sec": OFFSET_SEC,
                   "max_duration_sec": MAX_DURATION_SEC},
        "stages": {},
    }
    t0 = time.time()
    try:
        log("Stage 1: open IBL processed & raw NWB via remfile")
        from dandi.dandiapi import DandiAPIClient
        import h5py, remfile
        with DandiAPIClient() as client:
            ds = client.get_dandiset(DANDISET, "draft")
            purl = ds.get_asset_by_path(PROC_PATH).get_content_url(follow_redirects=1, strip_query=True)
            rurl = ds.get_asset_by_path(RAW_PATH).get_content_url(follow_redirects=1, strip_query=True)
        hp = h5py.File(remfile.File(url=purl), "r")
        hr = h5py.File(remfile.File(url=rurl), "r")
        log(f"   opened in {time.time()-t0:.1f}s")
    except Exception as e:
        log(traceback.format_exc()); results["aggregate_verdict"] = f"BLOCKED_S1: {e!r}"
        json.dump(results, open(OUT, "w"), indent=2, default=str); return

    try:
        log("Stage 2: trials + region channel selection")
        tg = hp["intervals/trials"]
        stim = np.asarray(tg["gabor_stimulus_onset_time"][:], dtype=float)
        fb = np.asarray(tg["feedback_time"][:], dtype=float)
        if "is_mouse_rewarded" in tg:
            rewarded = np.asarray(tg["is_mouse_rewarded"][:]).astype(float)
        else:
            rewarded = (np.asarray(tg["reward_volume_uL"][:], dtype=float) > 0).astype(float)
        ridx, loc = region_channels(hr, TARGET_REGION)
        results["stages"]["s2"] = {
            "n_trials": len(stim), "n_rewarded": int(np.nansum(rewarded == 1)),
            "n_error": int(np.nansum(rewarded == 0)),
            "n_region_channels": len(ridx), "target_region": TARGET_REGION,
            "region_match": REGION_MATCH,
        }
        log(f"   {len(stim)} trials; rew={int(np.nansum(rewarded==1))} err={int(np.nansum(rewarded==0))}; "
            f"'{TARGET_REGION}' ({REGION_MATCH}) has {len(ridx)} channels")
        if len(ridx) < 2:
            raise RuntimeError(f"region '{TARGET_REGION}' has <2 channels")
    except Exception as e:
        log(traceback.format_exc()); results["aggregate_verdict"] = f"BLOCKED_S2: {e!r}"
        json.dump(results, open(OUT, "w"), indent=2, default=str); return

    try:
        log("Stage 3: stream LF snippet (region channels) + HEM-GILE J(t) diagnostics")
        lf_name, es = find_lf_series(hr)
        data_ds = es["data"]; n_total, n_ch_total = data_ds.shape
        t_off, fs = lf_timing(es)
        sel = np.array(ridx)[np.linspace(0, len(ridx) - 1, min(MAX_CHANNELS, len(ridx)), dtype=int)]
        sel = sorted(int(c) for c in sel)
        i_lo = max(0, int((OFFSET_SEC - t_off) * fs))
        i_hi = min(n_total, int((OFFSET_SEC + MAX_DURATION_SEC - t_off) * fs))
        win_n = int(WINDOW_SEC * fs); step_n = int(STEP_SEC * fs)
        if i_hi - i_lo < win_n:
            raise RuntimeError(f"INVALID_WINDOW i_lo={i_lo} i_hi={i_hi}")
        log(f"   LF '{lf_name}' fs={fs:.1f} t0={t_off:.3f}; channels {sel} (of region {len(ridx)})")
        raw = data_ds[i_lo:i_hi, sel]
        data = np.asarray(raw, dtype=np.float32).T
        log(f"   loaded {data.shape} in {time.time()-t0:.1f}s")
        pairs = [(i, j) for i in range(data.shape[0]) for j in range(i + 1, data.shape[0])][:10]
        Jv = {m: [] for m in MODES}; G_arr, H_arr = [], []
        w = 0
        while w + win_n <= data.shape[1]:
            modes, G, H = compute_J(data[:, w:w + win_n], fs, pairs)
            for m in MODES:
                Jv[m].append(modes[m])
            G_arr.append(G); H_arr.append(H)
            w += step_n
        Jv = {m: np.asarray(v) for m, v in Jv.items()}
        G_arr = np.asarray(G_arr); H_arr = np.asarray(H_arr)
        results["stages"]["s3"] = {
            "fs_hz": fs, "n_channels_used": len(sel), "n_windows": len(Jv["dual"]),
            "J_dual_mean": float(np.mean(Jv["dual"])), "J_dual_std": float(np.std(Jv["dual"])),
            "J_mult_mean": float(np.mean(Jv["mult"])), "J_mult_std": float(np.std(Jv["mult"])),
            "J_add_mean": float(np.mean(Jv["add"])), "J_add_std": float(np.std(Jv["add"])),
            "G_mean": float(np.mean(G_arr)), "G_std": float(np.std(G_arr)),
            "G_cap_hit_fraction": float(np.mean(G_arr >= G_STAR)),
            "H_mean": float(np.mean(H_arr)), "H_std": float(np.std(H_arr)),
            "H_ceiling_fraction": float(np.mean(H_arr >= 0.999)),
        }
        log(f"   J_dual mean={np.mean(Jv['dual']):.4f} (mult={np.mean(Jv['mult']):.4f} "
            f"add={np.mean(Jv['add']):.4f}) | G={np.mean(G_arr):.3f} "
            f"(cap_hit={np.mean(G_arr>=G_STAR):.1%}) | H={np.mean(H_arr):.3f}+-{np.std(H_arr):.3f} "
            f"(ceil={np.mean(H_arr>=0.999):.1%}) over {len(Jv['dual'])} windows")
    except Exception as e:
        log(traceback.format_exc()); results["aggregate_verdict"] = f"BLOCKED_S3: {e!r}"
        json.dump(results, open(OUT, "w"), indent=2, default=str); return

    span_lo = t_off + (i_lo + win_n / 2) / fs
    span_hi = t_off + (i_hi - win_n / 2) / fs

    def _stim_verdict(arr):
        d = cohens_d(arr); lo, hi = bootstrap_ci(arr)
        ci_excl = (lo > 0) or (hi < 0); ad = abs(d)
        verdict = ("PASS" if (ad >= D_PASS and ci_excl)
                   else "INCONCLUSIVE_GRAY_ZONE" if ad >= D_INCONCLUSIVE_LO else "REFUTED")
        return {"cohens_d": d, "abs_d": ad, "delta_mean": float(np.mean(arr)),
                "bootstrap_95ci": [lo, hi], "ci_excludes_zero": ci_excl, "verdict": verdict}

    def _valence_verdict(rew_d, err_d):
        from scipy.stats import mannwhitneyu, kruskal
        U, p_mw = mannwhitneyu(rew_d, err_d, alternative="two-sided")
        n1, n2 = len(rew_d), len(err_d)
        rb = (2.0 * U) / (n1 * n2) - 1.0
        Hs, p_kw = kruskal(rew_d, err_d); N = n1 + n2
        eps2 = max(0.0, float((Hs - 1) / (N - 2)))
        # Pre-registered hypothesis is DIRECTIONAL: reward should RAISE J vs error.
        # Use the RANK-based sign (rank-biserial > 0) to stay consistent with the
        # rank-based Kruskal/MWU significance test (robust to skew/outliers, unlike
        # the raw mean). A two-sided "significant" result in the WRONG sign
        # CONTRADICTS the hypothesis -> it is NOT a pass.
        correct_sign = (rb > 0.0)
        sig = (p_kw < KW_P_PASS and eps2 > ETA2_PASS)
        if sig and correct_sign:
            verdict = "PASS"
        elif sig and not correct_sign:
            verdict = "REFUTED_WRONG_SIGN"
        elif p_kw < 0.05:
            verdict = "INCONCLUSIVE_GRAY_ZONE"
        else:
            verdict = "REFUTED"
        return {"n_rewarded": n1, "n_error": n2,
                "rewarded_mean_dJ": float(np.mean(rew_d)), "error_mean_dJ": float(np.mean(err_d)),
                "p_mannwhitney": float(p_mw), "rank_biserial_rewarded_minus_error": float(rb),
                "kruskal_H": float(Hs), "p_kruskal": float(p_kw),
                "eta_squared": eps2, "verdict": verdict}

    # F-PHASE1B-1c : stimulus-onset reaction (per dual */+ mode)
    try:
        log("Stage 4: F-PHASE1B-1c stimulus reaction (event-locked, dJ; add/mult/dual)")
        deltas = {m: [] for m in MODES}
        for t_ev in stim:
            if span_lo - BASELINE[0] <= t_ev <= span_hi - RESPONSE[1]:
                d = event_delta_direct(data, fs, pairs, i_lo, t_off, float(t_ev))
                if d is not None:
                    for m in MODES:
                        deltas[m].append(d[m])
        n_ev = len(deltas["dual"])
        if n_ev >= 5:
            per_mode = {m: _stim_verdict(deltas[m]) for m in MODES}
            results["F_PHASE1B_1c"] = {"n_events": n_ev, "primary_mode": "dual",
                                       "verdict": per_mode["dual"]["verdict"],
                                       "by_mode": per_mode}
        else:
            results["F_PHASE1B_1c"] = {"n_events": n_ev, "verdict": "INSUFFICIENT_EVENTS"}
        log(f"   F1c: n={n_ev} -> " + " | ".join(
            f"{m}={results['F_PHASE1B_1c'].get('by_mode',{}).get(m,{}).get('verdict','-')}"
            f"(d={results['F_PHASE1B_1c'].get('by_mode',{}).get(m,{}).get('cohens_d',float('nan')):.3f})"
            for m in MODES) if n_ev >= 5 else f"   F1c: {results['F_PHASE1B_1c']}")
    except Exception as e:
        log(traceback.format_exc()); results["F_PHASE1B_1c"] = {"error": repr(e)}

    # F-PHASE1B-2c : valence (reward vs error), feedback-locked (per dual */+ mode)
    try:
        log("Stage 5: F-PHASE1B-2c valence (feedback-locked, dJ; add/mult/dual)")
        rew_d = {m: [] for m in MODES}; err_d = {m: [] for m in MODES}
        for tf, rw in zip(fb, rewarded):
            if np.isnan(tf) or np.isnan(rw):
                continue
            if span_lo - BASELINE[0] <= tf <= span_hi - RESPONSE[1]:
                d = event_delta_direct(data, fs, pairs, i_lo, t_off, float(tf))
                if d is not None:
                    tgt = rew_d if rw == 1 else err_d
                    for m in MODES:
                        tgt[m].append(d[m])
        n1, n2 = len(rew_d["dual"]), len(err_d["dual"])
        if n1 >= 5 and n2 >= 5:
            per_mode = {m: _valence_verdict(rew_d[m], err_d[m]) for m in MODES}
            results["F_PHASE1B_2c"] = {"n_rewarded": n1, "n_error": n2, "primary_mode": "dual",
                                       "verdict": per_mode["dual"]["verdict"],
                                       "by_mode": per_mode}
        else:
            results["F_PHASE1B_2c"] = {"n_rewarded": n1, "n_error": n2,
                                       "verdict": "INSUFFICIENT_OUTCOME_GROUPS"}
        log(f"   F2c: rew={n1} err={n2} -> " + " | ".join(
            f"{m}={results['F_PHASE1B_2c'].get('by_mode',{}).get(m,{}).get('verdict','-')}"
            f"(p={results['F_PHASE1B_2c'].get('by_mode',{}).get(m,{}).get('p_kruskal',float('nan')):.3g})"
            for m in MODES) if (n1 >= 5 and n2 >= 5) else f"   F2c: {results['F_PHASE1B_2c']}")
    except Exception as e:
        log(traceback.format_exc()); results["F_PHASE1B_2c"] = {"error": repr(e)}

    v1 = results.get("F_PHASE1B_1c", {}).get("verdict", "?")
    v2 = results.get("F_PHASE1B_2c", {}).get("verdict", "?")
    results["aggregate_verdict"] = f"[dual */+ primary] F1c(stim)={v1} | F2c(valence)={v2}"
    results["total_elapsed_s"] = round(time.time() - t0, 2)
    json.dump(results, open(OUT, "w"), indent=2, default=str)
    log(f"DONE in {time.time()-t0:.1f}s — {results['aggregate_verdict']}")


if __name__ == "__main__":
    main()
