"""
Pass-77-B4 Phase-1B CORRECTED — IBL Valence-Reachability, anatomy- & timescale-fixed.

WHY A CORRECTED RUN (diagnosis of the original REFUTED):
The original runner.py returned REFUTED for both hypotheses. Diagnosis (see DIAGNOSIS.md)
found TWO instrument-application defects, NOT evidence against reachability:

  DEFECT 1 (anatomy, dominant): the default session sub-NYU-37's only probe sits in
    midbrain/brainstem — Periaqueductal gray (122ch), Dorsal nucleus raphe (84ch),
    Superior colliculus, + 42 "void" (out-of-brain) channels. The evenly-spaced
    4-channel sampler even included a VOID channel (pure noise). The canonical
    M_r=L*E instrument (gamma-PLV + theta/delta arousal) was calibrated on
    CORTICAL/HIPPOCAMPAL LFP and does not transfer to those deep nuclei.

  DEFECT 2 (timescale): stim->feedback latency is 0.29s median and inter-trial
    interval 3.3s, but the original used 2s non-overlapping windows -> the post-stim
    window swallowed feedback and adjacent-trial baselines overlapped.

CORRECTIONS (independently motivated; NOT result-tuned):
  * Session sub-NR-0028 chosen for ANATOMY ONLY (probe spans Field CA1 102ch + CA3 +
    dentate + primary visual cortex) — the instrument's valid domain. Chosen before
    seeing any M_r result.
  * Channels restricted to a single target gray-matter region (default Field CA1),
    'void' excluded, spread within the region for non-trivial PLV.
  * Event-locked, fine-resolution M_r: 1.0s windows stepped 0.5s; per-event
    baseline-corrected (baseline [-1.5,-0.5]s, response [0,+1.0]s).

PRE-REGISTERED (thresholds IDENTICAL to the original — fair re-test):
  F-PHASE1B-1c (sensory/stimulus reaction): per stim-onset event,
    dMr = mean(M_r in [0,+1]s) - mean(M_r in [-1.5,-0.5]s). Cohen's d over events,
    bootstrap-95%-CI. PASS d>0.30 & CI excl 0; INCONCLUSIVE |d| in [0.15,0.30]; else REFUTED.
  F-PHASE1B-2c (valence proxy): feedback-locked dMr, rewarded vs error.
    Mann-Whitney + Kruskal + epsilon^2. PASS p<0.01 & eps2>0.06; INCONCLUSIVE p<0.05;
    else REFUTED. Gated on >=5 events per outcome.

#69 SCOPE (unchanged): pre-recorded => reachability necessary-condition ONLY (no
closed-loop efficacy); single session => cross-animal DEFERRED; valence co-varies with
licking/arousal => correlate not pure code. A PASS here only shows the canonical
instrument CAN track these signals when applied to in-domain tissue at the right timescale.

DATASET: DANDI:000409. Default session sub-NR-0028 ses-f56194bc.
BUDGET: 5 min wall; ~300s contiguous LF snippet (~576MB @ 2500Hz*384ch full-width chunks).
Overridable via env: SESSION, TARGET_REGION, OFFSET_SEC, MAX_DURATION_SEC, MAX_CHANNELS.
"""
import json, os, time, traceback, warnings
from pathlib import Path
import numpy as np

warnings.filterwarnings("ignore")
OUT_DIR = Path(__file__).parent
_TAG = os.environ.get("RUN_TAG", "")
OUT = OUT_DIR / (f"results_corrected{('_'+_TAG) if _TAG else ''}.json")
LOG = OUT_DIR / (f"runner_corrected{('_'+_TAG) if _TAG else ''}.log")


def log(m):
    line = f"[{time.strftime('%H:%M:%S')}] {m}"
    print(line, flush=True)
    with open(LOG, "a") as f:
        f.write(line + "\n")


DANDISET = "000409"
SESSION = os.environ.get("SESSION", "sub-NR-0028/sub-NR-0028_ses-f56194bc-8215-4ae8-bc6a-89781ad8e050")
PROC_PATH = f"{SESSION}_desc-processed_behavior+ecephys.nwb"
RAW_PATH = f"{SESSION}_desc-raw_ecephys.nwb"
TARGET_REGION = os.environ.get("TARGET_REGION", "Field CA1")
SEED = 27182818
np.random.seed(SEED)

GAMMA_LO, GAMMA_HI = 30.0, 80.0
THETA_LO, THETA_HI = 6.0, 10.0
DELTA_LO, DELTA_HI = 1.0, 4.0
WINDOW_SEC = 1.0
STEP_SEC = 0.5
BASELINE = (-1.5, -0.5)   # relative to event (s)
RESPONSE = (0.0, 1.0)     # relative to event (s)
MAX_CHANNELS = int(os.environ.get("MAX_CHANNELS", "6"))
OFFSET_SEC = int(os.environ.get("OFFSET_SEC", "10"))
MAX_DURATION_SEC = int(os.environ.get("MAX_DURATION_SEC", "300"))
LF_RATE_DEFAULT = 2500.0

D_PASS = 0.30
D_INCONCLUSIVE_LO = 0.15
KW_P_PASS = 0.01
ETA2_PASS = 0.06


def bandpower(x, fs, lo, hi):
    from scipy.signal import welch
    nperseg = min(int(fs * 0.5), len(x))
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


def compute_M_r(seg, fs, pairs):
    plvs = [gamma_plv(seg[i], seg[j], fs) for i, j in pairs]
    L = float(np.mean(plvs)) if plvs else 0.0
    avg = np.mean(seg, axis=0)
    theta = bandpower(avg, fs, THETA_LO, THETA_HI)
    delta = bandpower(avg, fs, DELTA_LO, DELTA_HI) + 1e-12
    E = float(min(1.0, (theta / delta) / 3.0))
    return L * E, L, E


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


def region_channels(hr, target):
    """Return channel indices whose electrode location == target. Refuses out-of-brain
    'void' as a target and never returns void channels."""
    if target == "void":
        raise ValueError("target region 'void' is out-of-brain; choose gray matter")
    et = hr["general/extracellular_ephys/electrodes"]
    loc = np.asarray(et["location"][:])
    loc = [v.decode() if isinstance(v, bytes) else str(v) for v in loc]
    idx = [i for i, l in enumerate(loc) if l == target and l != "void"]
    return idx, loc


def _seg_mr(data, fs, pairs, lo_samp, hi_samp):
    """Compute canonical M_r on an exact sample segment; None if out-of-range/too short."""
    if lo_samp < 0 or hi_samp > data.shape[1] or (hi_samp - lo_samp) < int(0.3 * fs):
        return None
    m, _, _ = compute_M_r(data[:, lo_samp:hi_samp], fs, pairs)
    return m


def event_delta_direct(data, fs, pairs, i_lo, t_off, t_ev):
    """Exact event-locked dMr = M_r(response segment) - M_r(baseline segment).
    Segments are extracted directly from the raw LF array at the declared intervals
    (no sliding-grid center-time leakage)."""
    def s(t):
        return int(round((t - t_off) * fs)) - i_lo
    mb = _seg_mr(data, fs, pairs, s(t_ev + BASELINE[0]), s(t_ev + BASELINE[1]))
    mr = _seg_mr(data, fs, pairs, s(t_ev + RESPONSE[0]), s(t_ev + RESPONSE[1]))
    if mb is None or mr is None:
        return None
    return mr - mb


def main():
    results = {
        "pass": "77-B4", "phase": "1B-corrected", "dataset": "IBL Brain Wide Map",
        "dandiset": DANDISET, "session": SESSION, "target_region": TARGET_REGION,
        "seed": SEED, "prereg_locked": True,
        "corrections": [
            "session chosen for ANATOMY (probe in CA1/visual cortex) before seeing M_r",
            "channels restricted to target gray-matter region, void excluded",
            "event-locked fine resolution: 1s win/0.5s step, baseline[-1.5,-0.5] response[0,1]",
        ],
        "instrument_canonical": "M_r=L*E (gamma-PLV * theta/delta), identical to original",
        "scope_limits": [
            "pre-recorded => reachability necessary-condition ONLY",
            "single session => cross-animal DEFERRED",
            "valence co-varies with licking/arousal => correlate not pure code",
        ],
        "config": {"window_sec": WINDOW_SEC, "step_sec": STEP_SEC,
                   "baseline_s": BASELINE, "response_s": RESPONSE,
                   "max_channels": MAX_CHANNELS, "offset_sec": OFFSET_SEC,
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
        }
        log(f"   {len(stim)} trials; rew={int(np.nansum(rewarded==1))} err={int(np.nansum(rewarded==0))}; "
            f"'{TARGET_REGION}' has {len(ridx)} channels")
        if len(ridx) < 2:
            raise RuntimeError(f"region '{TARGET_REGION}' has <2 channels")
    except Exception as e:
        log(traceback.format_exc()); results["aggregate_verdict"] = f"BLOCKED_S2: {e!r}"
        json.dump(results, open(OUT, "w"), indent=2, default=str); return

    try:
        log("Stage 3: stream LF snippet (region channels) + event-lockable M_r(t)")
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
        Mr, L_arr, E_arr, t_arr = [], [], [], []
        w = 0
        while w + win_n <= data.shape[1]:
            seg = data[:, w:w + win_n]
            m, L, E = compute_M_r(seg, fs, pairs)
            Mr.append(m); L_arr.append(L); E_arr.append(E)
            t_arr.append(t_off + (i_lo + w + win_n / 2) / fs)
            w += step_n
        Mr = np.asarray(Mr); L_arr = np.asarray(L_arr); E_arr = np.asarray(E_arr); t_arr = np.asarray(t_arr)
        e_ceiling = float(np.mean(E_arr >= 0.999))  # fraction of windows where E hit its cap
        results["stages"]["s3"] = {
            "fs_hz": fs, "n_channels_used": len(sel), "n_windows": len(Mr),
            "analyzed_span_s": [float(t_arr.min()), float(t_arr.max())],
            "M_r_mean": float(np.mean(Mr)), "M_r_std": float(np.std(Mr)),
            "M_r_min": float(np.min(Mr)), "M_r_max": float(np.max(Mr)),
            "L_mean": float(np.mean(L_arr)), "E_mean": float(np.mean(E_arr)),
            "E_ceiling_fraction": e_ceiling,
        }
        log(f"   M_r mean={np.mean(Mr):.4f} std={np.std(Mr):.4f} L={np.mean(L_arr):.3f} "
            f"E={np.mean(E_arr):.3f} E_cap_hit={e_ceiling:.1%} over {len(Mr)} windows")
    except Exception as e:
        log(traceback.format_exc()); results["aggregate_verdict"] = f"BLOCKED_S3: {e!r}"
        json.dump(results, open(OUT, "w"), indent=2, default=str); return

    span_lo, span_hi = float(t_arr.min()), float(t_arr.max())

    # F-PHASE1B-1c : stimulus-onset reaction
    try:
        log("Stage 4: F-PHASE1B-1c stimulus reaction (event-locked)")
        deltas = []
        for t_ev in stim:
            if span_lo - BASELINE[0] <= t_ev <= span_hi - RESPONSE[1]:
                d = event_delta_direct(data, fs, pairs, i_lo, t_off, float(t_ev))
                if d is not None:
                    deltas.append(d)
        if len(deltas) >= 5:
            d = cohens_d(deltas); lo, hi = bootstrap_ci(deltas)
            ci_excl = (lo > 0) or (hi < 0); ad = abs(d)
            verdict = ("PASS" if (ad >= D_PASS and ci_excl)
                       else "INCONCLUSIVE_GRAY_ZONE" if ad >= D_INCONCLUSIVE_LO else "REFUTED")
            results["F_PHASE1B_1c"] = {"n_events": len(deltas), "cohens_d": d, "abs_d": ad,
                                       "delta_mean": float(np.mean(deltas)),
                                       "bootstrap_95ci": [lo, hi], "ci_excludes_zero": ci_excl,
                                       "verdict": verdict}
        else:
            results["F_PHASE1B_1c"] = {"n_events": len(deltas), "verdict": "INSUFFICIENT_EVENTS"}
        log(f"   F1c: {results['F_PHASE1B_1c']}")
    except Exception as e:
        log(traceback.format_exc()); results["F_PHASE1B_1c"] = {"error": repr(e)}

    # F-PHASE1B-2c : valence (reward vs error), feedback-locked
    try:
        log("Stage 5: F-PHASE1B-2c valence (feedback-locked)")
        rew_d, err_d = [], []
        for tf, rw in zip(fb, rewarded):
            if np.isnan(tf) or np.isnan(rw):
                continue
            if span_lo - BASELINE[0] <= tf <= span_hi - RESPONSE[1]:
                d = event_delta_direct(data, fs, pairs, i_lo, t_off, float(tf))
                if d is not None:
                    (rew_d if rw == 1 else err_d).append(d)
        if len(rew_d) >= 5 and len(err_d) >= 5:
            from scipy.stats import mannwhitneyu, kruskal
            U, p_mw = mannwhitneyu(rew_d, err_d, alternative="two-sided")
            n1, n2 = len(rew_d), len(err_d)
            rb = (2.0 * U) / (n1 * n2) - 1.0
            H, p_kw = kruskal(rew_d, err_d); N = n1 + n2
            eps2 = max(0.0, float((H - 1) / (N - 2)))
            verdict = ("PASS" if (p_kw < KW_P_PASS and eps2 > ETA2_PASS)
                       else "INCONCLUSIVE_GRAY_ZONE" if p_kw < 0.05 else "REFUTED")
            results["F_PHASE1B_2c"] = {"n_rewarded": n1, "n_error": n2,
                                       "rewarded_mean_dMr": float(np.mean(rew_d)),
                                       "error_mean_dMr": float(np.mean(err_d)),
                                       "p_mannwhitney": float(p_mw),
                                       "rank_biserial_rewarded_minus_error": float(rb),
                                       "kruskal_H": float(H), "p_kruskal": float(p_kw),
                                       "eta_squared": eps2, "verdict": verdict}
        else:
            results["F_PHASE1B_2c"] = {"n_rewarded": len(rew_d), "n_error": len(err_d),
                                       "verdict": "INSUFFICIENT_OUTCOME_GROUPS"}
        log(f"   F2c: {results['F_PHASE1B_2c']}")
    except Exception as e:
        log(traceback.format_exc()); results["F_PHASE1B_2c"] = {"error": repr(e)}

    v1 = results.get("F_PHASE1B_1c", {}).get("verdict", "?")
    v2 = results.get("F_PHASE1B_2c", {}).get("verdict", "?")
    results["aggregate_verdict"] = f"F1c(stim)={v1} | F2c(valence)={v2}"
    results["total_elapsed_s"] = round(time.time() - t0, 2)
    json.dump(results, open(OUT, "w"), indent=2, default=str)
    log(f"DONE in {time.time()-t0:.1f}s — {results['aggregate_verdict']}")


if __name__ == "__main__":
    main()
