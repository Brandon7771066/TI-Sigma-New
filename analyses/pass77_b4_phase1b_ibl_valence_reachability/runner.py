"""
Pass-77-B4 Phase-1B — IBL Mouse Valence-Reachability Pipeline Validation on DANDI

Sibling to Phase-1A (pass77_b4_phase1a_rodent_mood_trajectory). Phase-1A validated
the canonical M_r=L*E instrument on Buzsaki rodent hippocampal LFP (sleep states +
PulseStim). Phase-1B ports the SAME canonical instrument to the International Brain
Laboratory (IBL) Brain-Wide-Map mouse Neuropixels cohort, streamed in NWB form from
DANDI:000409. IBL adds what the Buzsaki sleep data lacks: a rich trial structure with
an explicit reward/error outcome -> the cleanest publicly available VALENCE PROXY.

WHY THIS DATASET (per task: animal brain-activity, cloud-streamable):
  IBL Brain Wide Map is mirrored on DANDI as NWB and streamable via remfile+h5py
  (no full download; same machinery as Phase-1A). 459 sessions, mouse, Neuropixels,
  12 labs, CC-BY. Each session ships TWO NWB files sharing one session clock:
    * desc-processed_behavior+ecephys.nwb (~400MB): /intervals/trials + /units
    * desc-raw_ecephys.nwb (50-150GB): ElectricalSeriesProbe00LF (LF band, 2.5kHz)
  We stream a bounded LF snippet from the raw file and read trials from the processed
  file; both align on the same master clock.

PRE-REGISTERED HYPOTHESES (locked before execution per per-pass anti-HARK):

F-PHASE1B-1: M_r(t) reacts coherently to visual stimulus onset (salience reaction).
  Operationalization: for each gabor_stimulus_onset_time t_i in the analyzed window,
    Delta = mean(M_r in [t_i, t_i+2s]) - mean(M_r in [t_i-2s, t_i])
  Aggregate across N events; test |mean(Delta)| effect-size Cohen's d > 0.3 with
  bootstrap-95%-CI excluding zero.
  PASS if d > 0.3 and CI excludes 0. INCONCLUSIVE if |d| in [0.15,0.3]. Else REFUTED.

F-PHASE1B-2 (VALENCE PROXY — the new value over Phase-1A):
  M_r discriminates rewarded vs unrewarded (error) trials.
  Operationalization: per trial, take mean(M_r in [feedback_time, feedback_time+2s]);
  group by is_mouse_rewarded (1 vs 0). Test Mann-Whitney U two-sided + rank-biserial
  effect size; also Kruskal-Wallis H + eta^2.
  PASS if p < 0.01 and eta^2 > 0.06 (medium). INCONCLUSIVE if p<0.05. Else REFUTED.
  GATED on >=5 trials in EACH outcome group within the analyzed window.

INSTRUMENT (identical to Phase-1A canonical, per eeg_bci_system.py / TLC-1 Pass-74):
  L = mean gamma(30-80Hz)-band PLV across sampled channel pairs (Love/Connection).
  E = rodent/mouse-arousal-analog = min(1, theta(6-10Hz)/delta(1-4Hz) / 3.0).
  M_r(t) = L(t) * E(t).
  (LF int16 raw is used directly; PLV is phase-based and theta/delta is a ratio, so no
   uV gain conversion is required.)

#69 HONESTY / SCOPE LIMITS (load-bearing, NOT hedging):
  * PRE-RECORDED data => this is a REACHABILITY NECESSARY-CONDITION test only. A pass
    shows the canonical instrument *can* track a stimulus/valence signal in mouse LFP;
    it says NOTHING about closed-loop Mood-Amplifier efficacy (no feedback was applied).
  * SINGLE session/probe => Phase-1B is single-subject; cross-animal reliability is
    DEFERRED to a multi-session cohort (as Phase-1A deferred F3 to B5).
  * CONFOUND DISCLOSURE for F-PHASE1B-2: reward vs error co-varies with licking,
    wheel-stilling, and arousal. A positive result is a valence-CORRELATE, not proof of
    a pure-valence code. Reported as a correlate, deliberately not over-claimed.

DATASET: DANDI:000409 (IBL - Brain Wide Map). Default matched pair:
  sub-NYU-37 ses-21d21fc3-4201-4edc-802a-c67b61952548 (raw 53GB + processed 385MB).

BUDGET: 5 min hard wall; bounded LF snippet (default 150s ~= 288MB @ 2500Hz*384ch).
  Overridable via env: SESSION, OFFSET_SEC, MAX_DURATION_SEC, MAX_CHANNELS.
"""
import json, os, time, traceback, warnings
from pathlib import Path
import numpy as np

warnings.filterwarnings("ignore")

OUT_DIR = Path(__file__).parent
OUT = OUT_DIR / "results.json"
LOG = OUT_DIR / "runner.log"


def log(m):
    line = f"[{time.strftime('%H:%M:%S')}] {m}"
    print(line, flush=True)
    with open(LOG, "a") as f:
        f.write(line + "\n")


DANDISET = "000409"
SESSION = os.environ.get("SESSION", "sub-NYU-37/sub-NYU-37_ses-21d21fc3-4201-4edc-802a-c67b61952548")
PROC_PATH = f"{SESSION}_desc-processed_behavior+ecephys.nwb"
RAW_PATH = f"{SESSION}_desc-raw_ecephys.nwb"
SEED = 27182818
np.random.seed(SEED)

# Frequency bands per canonical neuroscience + eeg_bci_system.py (identical to Phase-1A)
GAMMA_LO, GAMMA_HI = 30.0, 80.0
THETA_LO, THETA_HI = 6.0, 10.0
DELTA_LO, DELTA_HI = 1.0, 4.0
WINDOW_SEC = 2.0
MAX_CHANNELS = int(os.environ.get("MAX_CHANNELS", "4"))
OFFSET_SEC = int(os.environ.get("OFFSET_SEC", "10"))
MAX_DURATION_SEC = int(os.environ.get("MAX_DURATION_SEC", "150"))
LF_RATE_DEFAULT = 2500.0  # IBL Neuropixels LF band canonical

# Decision thresholds (pre-reg locked; identical to Phase-1A)
D_PASS = 0.30
D_INCONCLUSIVE_LO = 0.15
KW_P_PASS = 0.01
ETA2_PASS = 0.06
WALL_BUDGET_SEC = 300.0


def bandpower(x, fs, lo, hi):
    from scipy.signal import welch
    nperseg = min(int(fs * 1.0), len(x))
    if nperseg < 16:
        return 0.0
    f, Pxx = welch(x, fs=fs, nperseg=nperseg)
    mask = (f >= lo) & (f <= hi)
    return float(np.trapz(Pxx[mask], f[mask])) if mask.any() else 0.0


def gamma_plv(x1, x2, fs):
    from scipy.signal import butter, filtfilt, hilbert
    if len(x1) < int(fs * 0.5):
        return 0.0
    nyq = fs / 2.0
    lo, hi = GAMMA_LO / nyq, min(GAMMA_HI / nyq, 0.99)
    if hi <= lo:
        return 0.0
    try:
        b, a = butter(4, [lo, hi], btype="band")
        s1 = filtfilt(b, a, x1)
        s2 = filtfilt(b, a, x2)
        p1 = np.angle(hilbert(s1))
        p2 = np.angle(hilbert(s2))
        return float(np.abs(np.mean(np.exp(1j * (p1 - p2)))))
    except Exception:
        return 0.0


def compute_M_r_window(lfp_window, fs, channel_pairs):
    """L * E per canonical TI Sigma TLC-1 (identical to Phase-1A)."""
    plvs = [gamma_plv(lfp_window[i], lfp_window[j], fs) for i, j in channel_pairs]
    L = float(np.mean(plvs)) if plvs else 0.0
    avg = np.mean(lfp_window, axis=0)
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
    """Deterministically locate the LF-band ElectricalSeries in acquisition/.
    Portable across IBL sessions whose probe naming differs (e.g. Probe01LF).
    Prefers neurodata_type==ElectricalSeries with 'LF' in the name; falls back to
    any 2D Electrical* series; raises if none found."""
    acq = hr["acquisition"]
    def ndt(g):
        v = g.attrs.get("neurodata_type", b"")
        return v.decode() if isinstance(v, bytes) else str(v)
    cands = [k for k in acq.keys()
             if "LF" in k and "data" in acq[k]
             and getattr(acq[k]["data"], "ndim", 0) == 2
             and ndt(acq[k]) == "ElectricalSeries"]
    if not cands:
        cands = [k for k in acq.keys()
                 if "Electrical" in k and "data" in acq[k]
                 and getattr(acq[k]["data"], "ndim", 0) == 2]
    if not cands:
        raise RuntimeError("no LF ElectricalSeries found in acquisition/")
    name = sorted(cands)[0]
    return name, acq[name]


def lf_timing(g):
    """Robustly resolve (t0_offset_seconds, sample_rate_hz) for an ElectricalSeries.
    Tries starting_time(+rate attr), then a 2-point read of timestamps, then default."""
    try:
        if "starting_time" in g:
            st = g["starting_time"]
            rate = float(st.attrs.get("rate", LF_RATE_DEFAULT))
            return float(np.asarray(st)), rate
    except Exception:
        pass
    try:
        if "timestamps" in g and g["timestamps"].shape[0] >= 2:
            ts = g["timestamps"]
            t0 = float(ts[0]); tN = float(ts[-1]); N = ts.shape[0]
            rate = (N - 1) / (tN - t0) if tN > t0 else LF_RATE_DEFAULT
            return t0, rate
    except Exception:
        pass
    return 0.0, LF_RATE_DEFAULT


def main():
    results = {
        "pass": "77-B4", "phase": "1B", "dataset": "IBL Brain Wide Map",
        "dandiset": DANDISET, "session": SESSION,
        "seed": SEED, "prereg_locked": True,
        "instrument_canonical": "L=gamma-PLV, E=theta/delta normalized, M_r=L*E (TLC-1 Pass-74); identical to Phase-1A",
        "scope_limits": [
            "pre-recorded => reachability necessary-condition ONLY (not closed-loop efficacy)",
            "single session/probe => cross-animal reliability DEFERRED",
            "F2 reward/error co-varies with licking/wheel/arousal => valence-CORRELATE not pure code",
        ],
        "config": {
            "gamma_band_hz": [GAMMA_LO, GAMMA_HI], "theta_band_hz": [THETA_LO, THETA_HI],
            "delta_band_hz": [DELTA_LO, DELTA_HI], "window_sec": WINDOW_SEC,
            "max_channels": MAX_CHANNELS, "offset_sec": OFFSET_SEC,
            "max_duration_sec": MAX_DURATION_SEC,
        },
        "stages": {},
    }
    t0 = time.time()

    # Stage 1: open both NWB assets via DANDI stream
    try:
        log("Stage 1: resolve + open IBL processed & raw NWB via remfile")
        from dandi.dandiapi import DandiAPIClient
        import h5py, remfile
        with DandiAPIClient() as client:
            ds = client.get_dandiset(DANDISET, "draft")
            purl = ds.get_asset_by_path(PROC_PATH).get_content_url(follow_redirects=1, strip_query=True)
            rurl = ds.get_asset_by_path(RAW_PATH).get_content_url(follow_redirects=1, strip_query=True)
        hp = h5py.File(remfile.File(url=purl), "r")
        hr = h5py.File(remfile.File(url=rurl), "r")
        results["stages"]["s1_open"] = {"ok": True, "elapsed_s": round(time.time() - t0, 2)}
        log(f"   opened both in {time.time()-t0:.1f}s")
    except Exception as e:
        log(f"   FAIL: {traceback.format_exc()}")
        results["stages"]["s1_open"] = {"ok": False, "error": repr(e)}
        results["aggregate_verdict"] = "BLOCKED_S1_OPEN"
        with open(OUT, "w") as f:
            json.dump(results, f, indent=2, default=str)
        return

    # Stage 2: read trials from processed file
    try:
        log("Stage 2: read trials table from processed NWB")
        import h5py  # noqa
        tg = hp["intervals/trials"]
        cols = list(tg.keys())
        stim = np.asarray(tg["gabor_stimulus_onset_time"][:], dtype=float)
        fb = np.asarray(tg["feedback_time"][:], dtype=float)
        # valence proxy: is_mouse_rewarded (fallback to reward_volume_uL>0)
        if "is_mouse_rewarded" in tg:
            rewarded = np.asarray(tg["is_mouse_rewarded"][:]).astype(float)
        elif "reward_volume_uL" in tg:
            rewarded = (np.asarray(tg["reward_volume_uL"][:], dtype=float) > 0).astype(float)
        else:
            rewarded = np.full(len(fb), np.nan)
        n_trials = len(stim)
        n_rew = int(np.nansum(rewarded == 1)); n_err = int(np.nansum(rewarded == 0))
        results["stages"]["s2_trials"] = {
            "n_trials": n_trials, "trial_cols": cols,
            "n_rewarded": n_rew, "n_error": n_err,
            "stim_range_s": [float(np.nanmin(stim)), float(np.nanmax(stim))],
        }
        log(f"   {n_trials} trials; rewarded={n_rew} error={n_err}; stim in "
            f"[{np.nanmin(stim):.1f},{np.nanmax(stim):.1f}]s")
    except Exception as e:
        log(f"   FAIL: {traceback.format_exc()}")
        results["stages"]["s2_trials"] = {"ok": False, "error": repr(e)}
        results["aggregate_verdict"] = "BLOCKED_S2_TRIALS"
        with open(OUT, "w") as f:
            json.dump(results, f, indent=2, default=str)
        return

    # Stage 3: stream bounded LF snippet + compute M_r(t)
    try:
        log("Stage 3: stream LF snippet + compute M_r(t)")
        lf_name, es = find_lf_series(hr)
        data_ds = es["data"]
        n_total, n_ch_total = data_ds.shape  # (samples, channels)
        t_off, fs = lf_timing(es)
        log(f"   LF '{lf_name}' shape={list(data_ds.shape)} fs={fs:.1f}Hz t0_offset={t_off:.3f}s")
        # session-time window -> sample indices
        win_lo_s = OFFSET_SEC
        win_hi_s = OFFSET_SEC + MAX_DURATION_SEC
        i_lo = max(0, int((win_lo_s - t_off) * fs))
        i_hi = min(n_total, int((win_hi_s - t_off) * fs))
        win_samples = int(WINDOW_SEC * fs)
        if i_hi - i_lo < win_samples:
            raise RuntimeError(f"INVALID_WINDOW: i_lo={i_lo} i_hi={i_hi} < one window "
                               f"({win_samples}); check OFFSET_SEC/MAX_DURATION_SEC vs t0={t_off:.2f}")
        ch_idx = np.linspace(0, n_ch_total - 1, min(MAX_CHANNELS, n_ch_total), dtype=int)
        log(f"   reading samples [{i_lo}:{i_hi}] ({(i_hi-i_lo)/fs:.1f}s) x {len(ch_idx)} of {n_ch_total} ch")
        raw = data_ds[i_lo:i_hi, list(ch_idx)]            # full-width chunks pulled, then subselect
        data = np.asarray(raw, dtype=np.float32).T        # -> (channels, samples)
        log(f"   loaded LF array shape={data.shape} in {time.time()-t0:.1f}s")

        n_windows = data.shape[1] // win_samples
        if n_windows < 1:
            raise RuntimeError("INVALID_WINDOW: zero full windows in analyzed span")
        pairs = [(i, j) for i in range(data.shape[0]) for j in range(i + 1, data.shape[0])][:8]
        Mr, L_arr, E_arr, t_arr = [], [], [], []
        for w in range(n_windows):
            seg = data[:, w * win_samples:(w + 1) * win_samples]
            m, L, E = compute_M_r_window(seg, fs, pairs)
            Mr.append(m); L_arr.append(L); E_arr.append(E)
            # window-center session time
            t_arr.append(t_off + (i_lo + (w + 0.5) * win_samples) / fs)
        Mr = np.asarray(Mr); L_arr = np.asarray(L_arr); E_arr = np.asarray(E_arr); t_arr = np.asarray(t_arr)
        results["stages"]["s3_mr"] = {
            "fs_hz": fs, "t0_offset_s": t_off, "n_channels_used": int(len(ch_idx)),
            "n_windows": int(n_windows), "window_sec": WINDOW_SEC,
            "analyzed_span_s": [float(t_arr.min()), float(t_arr.max())] if n_windows else None,
            "M_r_mean": float(np.mean(Mr)), "M_r_std": float(np.std(Mr)),
            "M_r_min": float(np.min(Mr)), "M_r_max": float(np.max(Mr)),
            "L_mean": float(np.mean(L_arr)), "E_mean": float(np.mean(E_arr)),
        }
        log(f"   M_r mean={np.mean(Mr):.4f} std={np.std(Mr):.4f} "
            f"range=[{np.min(Mr):.4f},{np.max(Mr):.4f}] over {n_windows} windows")
    except Exception as e:
        log(f"   FAIL: {traceback.format_exc()}")
        results["stages"]["s3_mr"] = {"ok": False, "error": repr(e)}
        results["aggregate_verdict"] = "BLOCKED_S3_MR"
        with open(OUT, "w") as f:
            json.dump(results, f, indent=2, default=str)
        return

    span_lo, span_hi = float(t_arr.min()), float(t_arr.max())

    # Stage 4: F-PHASE1B-1 — stimulus-onset reaction
    try:
        log("Stage 4: F-PHASE1B-1 stimulus-onset reaction")
        ev = [float(t) for t in stim if span_lo + 2 * WINDOW_SEC <= t <= span_hi - 2 * WINDOW_SEC]
        deltas = []
        for t_ev in ev:
            pre = (t_arr >= t_ev - 2 * WINDOW_SEC) & (t_arr < t_ev)
            post = (t_arr >= t_ev) & (t_arr < t_ev + 2 * WINDOW_SEC)
            if pre.sum() >= 1 and post.sum() >= 1:
                deltas.append(float(np.mean(Mr[post]) - np.mean(Mr[pre])))
        if len(deltas) >= 5:
            d = cohens_d(deltas)
            ci_lo, ci_hi = bootstrap_ci(deltas)
            ci_excl = (ci_lo > 0) or (ci_hi < 0)
            abs_d = abs(d)
            verdict = ("PASS" if (abs_d >= D_PASS and ci_excl)
                       else "INCONCLUSIVE_GRAY_ZONE" if abs_d >= D_INCONCLUSIVE_LO else "REFUTED")
            results["F_PHASE1B_1"] = {
                "n_events": len(deltas), "cohens_d": d, "abs_d": abs_d,
                "delta_mean": float(np.mean(deltas)), "delta_std": float(np.std(deltas, ddof=1)),
                "bootstrap_95ci": [ci_lo, ci_hi], "ci_excludes_zero": ci_excl,
                "threshold_d_pass": D_PASS, "verdict": verdict,
            }
        else:
            results["F_PHASE1B_1"] = {"n_events": len(deltas), "verdict": "INSUFFICIENT_EVENTS"}
        log(f"   F-PHASE1B-1: {results['F_PHASE1B_1']}")
    except Exception as e:
        log(f"   FAIL: {traceback.format_exc()}")
        results["F_PHASE1B_1"] = {"ok": False, "error": repr(e)}

    # Stage 5: F-PHASE1B-2 — reward/error valence discrimination
    try:
        log("Stage 5: F-PHASE1B-2 reward/error valence discrimination")
        rew_vals, err_vals = [], []
        for tf, rw in zip(fb, rewarded):
            if np.isnan(tf) or np.isnan(rw):
                continue
            if not (span_lo <= tf <= span_hi - 2 * WINDOW_SEC):
                continue
            post = (t_arr >= tf) & (t_arr < tf + 2 * WINDOW_SEC)
            if post.sum() < 1:
                continue
            val = float(np.mean(Mr[post]))
            (rew_vals if rw == 1 else err_vals).append(val)
        if len(rew_vals) >= 5 and len(err_vals) >= 5:
            from scipy.stats import mannwhitneyu, kruskal
            U, p_mw = mannwhitneyu(rew_vals, err_vals, alternative="two-sided")
            n1, n2 = len(rew_vals), len(err_vals)
            # rank-biserial oriented rewarded-minus-error: >0 => rewarded ranks higher,
            # <0 => error ranks higher (U is for the first group = rewarded).
            rb_rewarded_minus_error = (2.0 * U) / (n1 * n2) - 1.0
            H, p_kw = kruskal(rew_vals, err_vals)
            N = n1 + n2
            # epsilon^2 rank effect size (labelled eta_squared for Phase-1A parity)
            eta2 = max(0.0, float((H - 1) / (N - 2)))
            verdict = ("PASS" if (p_kw < KW_P_PASS and eta2 > ETA2_PASS)
                       else "INCONCLUSIVE_GRAY_ZONE" if p_kw < 0.05 else "REFUTED")
            results["F_PHASE1B_2"] = {
                "n_rewarded": n1, "n_error": n2,
                "rewarded_mean_M_r": float(np.mean(rew_vals)), "error_mean_M_r": float(np.mean(err_vals)),
                "mannwhitney_U": float(U), "p_mannwhitney": float(p_mw),
                "rank_biserial_rewarded_minus_error": float(rb_rewarded_minus_error),
                "kruskal_H": float(H), "p_kruskal": float(p_kw), "eta_squared": eta2,
                "verdict": verdict,
            }
        else:
            results["F_PHASE1B_2"] = {
                "n_rewarded": len(rew_vals), "n_error": len(err_vals),
                "verdict": "INSUFFICIENT_OUTCOME_GROUPS (need >=5 each in window)",
            }
        log(f"   F-PHASE1B-2: {results['F_PHASE1B_2']}")
    except Exception as e:
        log(f"   FAIL: {traceback.format_exc()}")
        results["F_PHASE1B_2"] = {"ok": False, "error": repr(e)}

    # Aggregate
    v1 = results.get("F_PHASE1B_1", {}).get("verdict", "?")
    v2 = results.get("F_PHASE1B_2", {}).get("verdict", "?")
    results["aggregate_verdict"] = f"F1(stim-reaction)={v1} | F2(valence-proxy)={v2}"
    results["total_elapsed_s"] = round(time.time() - t0, 2)

    for h in ("hp", "hr"):
        try:
            locals()[h].close()
        except Exception:
            pass

    with open(OUT, "w") as f:
        json.dump(results, f, indent=2, default=str)
    log(f"DONE in {time.time()-t0:.1f}s — verdict: {results['aggregate_verdict']}")


if __name__ == "__main__":
    main()
