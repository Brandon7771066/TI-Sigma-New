"""
Pass-77-B4 Phase-1A — Rodent Mood-Trajectory Pipeline Validation on DANDI

PRE-REGISTERED HYPOTHESES (locked before execution per per-pass anti-HARK):

F-PHASE1A-1: M_r(t) reacts coherently to PulseStim_* events.
  Operationalization: for each PulseStim event onset t_i, compute
    Δ = mean(M_r in [t_i, t_i+2s]) - mean(M_r in [t_i-2s, t_i])
  Aggregate across N events; test |mean(Δ)| effect-size d > 0.3
  via Cohen's d on per-event Δ distribution.
  PASS if d > 0.3 with bootstrap-95%-CI excluding zero.
  FAIL otherwise (REFUTED-PHASE-1A-PRIMARY → mood-model needs revision).
  INCONCLUSIVE if d in [0.15, 0.3] (gray zone).

F-PHASE1A-2: M_r(t) discriminates behavior/states (NREM/REM/wake).
  Operationalization: if processing/behavior/states present, compute
  mean and SD of M_r within each labeled state-interval; test
  Kruskal-Wallis H across states.
  PASS if p < 0.01 with effect-size η² > 0.06 (medium).
  FAIL otherwise.
  GATED on states-table presence in this NWB.

F-PHASE1A-3: cross-rat reliability — DEFERRED to Pass-77-B5 (multi-rat
  cohort, needs DANDI:001044 or multiple YutaMouse sessions).

INSTRUMENT (from corpus): per eeg_bci_system.py canonical
  L = gamma-band PLV across channel pairs (Love/Connection)
  E = arousal proxy. Human stack uses HRV RMSSD; rodent LFP lacks
      ECG so we substitute the canonical rodent-arousal-analog:
      E_rodent = theta(6-10Hz) / delta(1-4Hz) power ratio, normalized
      to [0,1] via E = min(1, ratio/3.0). This is the standard
      rodent-arousal index (high theta/delta = wake/active; high
      delta = NREM sleep).
  M_r(t) = L(t) * E(t) per Pass-74 TLC-1 canonical.

DATASET: DANDI:000003 sub-YutaMouse41 ses-150829 behavior+ecephys.nwb
  (Buzsaki lab rat hippocampal LFP; Pass-36 confirmed asset accessible;
  Pass-37 confirmed 17 PulseStim_* event-types present).

BUDGET: 5 min hard timeout on DANDI streaming; 256MB partial-download cap.
"""
import json, os, sys, time, traceback, warnings
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

DANDISET = "000003"
ASSET = "sub-YutaMouse41/sub-YutaMouse41_ses-YutaMouse41-150829_behavior+ecephys.nwb"
SEED = 27182818
np.random.seed(SEED)

# Frequency bands per canonical neuroscience + eeg_bci_system.py
GAMMA_LO, GAMMA_HI = 30.0, 80.0
THETA_LO, THETA_HI = 6.0, 10.0
DELTA_LO, DELTA_HI = 1.0, 4.0
WINDOW_SEC = 2.0       # mood-trajectory bin
MAX_CHANNELS = 4       # 4 channels = 6 pair-PLVs, sufficient for L estimate
OFFSET_SEC = int(os.environ.get("OFFSET_SEC", "0"))  # window start
MAX_DURATION_SEC = int(os.environ.get("MAX_DURATION_SEC", "600"))  # window length
# Default: 0-600s (PulseStim-rich, F1 test).
# State test: OFFSET_SEC=4400 MAX_DURATION_SEC=1100 (covers states 4437s+).

# Decision thresholds (pre-reg locked)
D_PASS = 0.30
D_INCONCLUSIVE_LO = 0.15
KW_P_PASS = 0.01
ETA2_PASS = 0.06


def bandpower(x, fs, lo, hi):
    """Welch PSD-based band power."""
    from scipy.signal import welch
    nperseg = min(int(fs * 1.0), len(x))
    if nperseg < 16:
        return 0.0
    f, Pxx = welch(x, fs=fs, nperseg=nperseg)
    mask = (f >= lo) & (f <= hi)
    return float(np.trapz(Pxx[mask], f[mask])) if mask.any() else 0.0


def gamma_plv(x1, x2, fs):
    """Phase-Locking Value in gamma band between two channels (eeg_bci_system canonical)."""
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
    """L * E per canonical TI Sigma TLC-1.
    L = mean gamma-PLV across sampled channel pairs.
    E = rodent-arousal-analog = min(1, theta/delta / 3.0)."""
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
    return (float(np.quantile(means, alpha/2)), float(np.quantile(means, 1-alpha/2)))


def main():
    results = {
        "pass": "77-B4", "phase": "1A", "dandiset": DANDISET, "asset": ASSET,
        "seed": SEED, "prereg_locked": True,
        "instrument_canonical": "L=gamma-PLV, E_rodent=theta/delta normalized, M_r=L*E (TLC-1 Pass-74)",
        "config": {
            "gamma_band_hz": [GAMMA_LO, GAMMA_HI],
            "theta_band_hz": [THETA_LO, THETA_HI],
            "delta_band_hz": [DELTA_LO, DELTA_HI],
            "window_sec": WINDOW_SEC,
            "max_channels": MAX_CHANNELS,
            "max_duration_sec": MAX_DURATION_SEC,
        },
        "stages": {},
    }
    t0 = time.time()

    # Stage 1: DANDI stream + open NWB
    try:
        log("Stage 1: open DANDI asset via remfile + h5py")
        from dandi.dandiapi import DandiAPIClient
        import h5py, remfile
        with DandiAPIClient() as client:
            ds = client.get_dandiset(DANDISET, "draft")
            asset = ds.get_asset_by_path(ASSET)
            s3 = asset.get_content_url(follow_redirects=1, strip_query=True)
        rfile = remfile.File(url=s3)
        h5f = h5py.File(rfile, "r")
        results["stages"]["s1_open"] = {"ok": True, "elapsed_s": round(time.time()-t0, 2)}
        log(f"   opened in {time.time()-t0:.1f}s")
    except Exception as e:
        log(f"   FAIL: {traceback.format_exc()}")
        results["stages"]["s1_open"] = {"ok": False, "error": repr(e)}
        results["aggregate_verdict"] = "BLOCKED_S1_OPEN"
        with open(OUT, "w") as f:
            json.dump(results, f, indent=2, default=str)
        return

    # Stage 2: locate LFP + PulseStim + states
    try:
        log("Stage 2: catalog NWB contents")
        lfp_candidates, pulsestim_paths, states_path = [], [], None
        def walker(name, obj):
            nl = name.lower()
            if isinstance(obj, h5py.Dataset):
                shp = obj.shape
                if "lfp" in nl and len(shp) == 2 and "data" in nl.split("/")[-1]:
                    lfp_candidates.append((name, shp))
                if "pulsestim" in nl and name.endswith("/timestamps"):
                    pulsestim_paths.append(name)
            if name.endswith("processing/behavior/states") or name.endswith("behavior/states"):
                nonlocal_assign(name)
        nonlocal_holder = {"states": None}
        def nonlocal_assign(p):
            nonlocal_holder["states"] = p
        h5f.visititems(walker)
        states_path = nonlocal_holder["states"]
        # Fallback LFP candidate: look for any /acquisition/*/data with >=2 channels
        if not lfp_candidates:
            def lfp_walker(name, obj):
                if isinstance(obj, h5py.Dataset) and name.endswith("/data"):
                    if len(obj.shape) == 2 and min(obj.shape) >= 2:
                        if "/acquisition/" in name or "lfp" in name.lower() or "ecephys" in name.lower():
                            lfp_candidates.append((name, obj.shape))
            h5f.visititems(lfp_walker)
        lfp_candidates = sorted(lfp_candidates, key=lambda x: -np.prod(x[1]))[:5]
        results["stages"]["s2_catalog"] = {
            "lfp_top5": [{"name": n, "shape": list(s)} for n, s in lfp_candidates],
            "pulsestim_count": len(pulsestim_paths),
            "states_path": states_path,
        }
        log(f"   LFP candidates: {len(lfp_candidates)}; PulseStim timestamps: {len(pulsestim_paths)}; states: {states_path}")
    except Exception as e:
        log(f"   FAIL: {traceback.format_exc()}")
        results["stages"]["s2_catalog"] = {"ok": False, "error": repr(e)}
        results["aggregate_verdict"] = "BLOCKED_S2_CATALOG"
        with open(OUT, "w") as f:
            json.dump(results, f, indent=2, default=str)
        return

    if not lfp_candidates:
        results["aggregate_verdict"] = "BLOCKED_NO_LFP"
        with open(OUT, "w") as f:
            json.dump(results, f, indent=2, default=str)
        return

    # Stage 3: read LFP window + compute M_r(t)
    try:
        log("Stage 3: read LFP + compute M_r(t)")
        lfp_name, lfp_shape = lfp_candidates[0]
        lfp_ds = h5f[lfp_name]
        # Find sampling rate
        parent = lfp_ds.parent
        fs = None
        for key in ("rate", "starting_time_rate", "sampling_rate"):
            if key in parent.attrs:
                fs = float(parent.attrs[key]); break
        if fs is None and "starting_time" in parent:
            try:
                fs = float(parent["starting_time"].attrs.get("rate", 1250.0))
            except Exception:
                fs = 1250.0
        if fs is None:
            fs = 1250.0  # Buzsaki canonical default
        # Determine channel and sample axes
        n_samples_axis = int(np.argmax(lfp_shape))
        n_ch_axis = 1 - n_samples_axis
        total_samples = lfp_shape[n_samples_axis]
        total_channels = lfp_shape[n_ch_axis]
        offset_samples = int(fs * OFFSET_SEC)
        n_samples = min(int(fs * MAX_DURATION_SEC), total_samples - offset_samples)
        ch_indices = np.linspace(0, total_channels - 1, min(MAX_CHANNELS, total_channels), dtype=int)
        log(f"   LFP {lfp_name} shape={lfp_shape} fs={fs:.1f}Hz; reading {n_samples} samples × {len(ch_indices)} channels from t={OFFSET_SEC}s")
        # Read partial
        if n_samples_axis == 0:
            data = lfp_ds[offset_samples:offset_samples+n_samples, list(ch_indices)]
            data = data.T  # → (channels, samples)
        else:
            data = lfp_ds[list(ch_indices), offset_samples:offset_samples+n_samples]
        data = np.asarray(data, dtype=np.float32)
        log(f"   loaded LFP array shape={data.shape}; computing M_r windows")

        win_samples = int(WINDOW_SEC * fs)
        n_windows = data.shape[1] // win_samples
        pairs = [(i, j) for i in range(data.shape[0]) for j in range(i+1, data.shape[0])][:8]
        Mr, L_arr, E_arr, t_arr = [], [], [], []
        for w in range(n_windows):
            seg = data[:, w*win_samples:(w+1)*win_samples]
            m, L, E = compute_M_r_window(seg, fs, pairs)
            Mr.append(m); L_arr.append(L); E_arr.append(E)
            t_arr.append(OFFSET_SEC + (w + 0.5) * WINDOW_SEC)
        Mr = np.asarray(Mr); L_arr = np.asarray(L_arr); E_arr = np.asarray(E_arr); t_arr = np.asarray(t_arr)
        results["stages"]["s3_mr"] = {
            "lfp_path": lfp_name, "fs_hz": fs, "n_channels_used": int(len(ch_indices)),
            "n_windows": n_windows, "window_sec": WINDOW_SEC,
            "M_r_mean": float(np.mean(Mr)), "M_r_std": float(np.std(Mr)),
            "M_r_min": float(np.min(Mr)), "M_r_max": float(np.max(Mr)),
            "L_mean": float(np.mean(L_arr)), "E_mean": float(np.mean(E_arr)),
        }
        log(f"   M_r mean={np.mean(Mr):.4f} std={np.std(Mr):.4f} range=[{np.min(Mr):.4f},{np.max(Mr):.4f}]")
    except Exception as e:
        log(f"   FAIL: {traceback.format_exc()}")
        results["stages"]["s3_mr"] = {"ok": False, "error": repr(e)}
        results["aggregate_verdict"] = "BLOCKED_S3_MR"
        with open(OUT, "w") as f:
            json.dump(results, f, indent=2, default=str)
        return

    # Stage 4: F-PHASE1A-1 — PulseStim reaction
    try:
        log("Stage 4: F-PHASE1A-1 PulseStim reaction test")
        all_stim_times = []
        for psp in pulsestim_paths[:20]:  # cap
            try:
                ts = h5f[psp][:]
                all_stim_times.extend([float(t) for t in ts if OFFSET_SEC <= t < OFFSET_SEC + MAX_DURATION_SEC])
            except Exception:
                continue
        all_stim_times = sorted(set(all_stim_times))
        log(f"   {len(all_stim_times)} stim events within first {MAX_DURATION_SEC}s")
        # For each event, compute pre/post M_r delta
        deltas = []
        for t_ev in all_stim_times:
            pre_mask = (t_arr >= t_ev - 2*WINDOW_SEC) & (t_arr < t_ev)
            post_mask = (t_arr >= t_ev) & (t_arr < t_ev + 2*WINDOW_SEC)
            if pre_mask.sum() >= 1 and post_mask.sum() >= 1:
                deltas.append(float(np.mean(Mr[post_mask]) - np.mean(Mr[pre_mask])))
        if len(deltas) >= 5:
            d = cohens_d(deltas)
            ci_lo, ci_hi = bootstrap_ci(deltas)
            ci_excludes_zero = (ci_lo > 0) or (ci_hi < 0)
            abs_d = abs(d)
            if abs_d >= D_PASS and ci_excludes_zero:
                verdict = "PASS"
            elif abs_d >= D_INCONCLUSIVE_LO:
                verdict = "INCONCLUSIVE_GRAY_ZONE"
            else:
                verdict = "REFUTED"
            results["F_PHASE1A_1"] = {
                "n_events": len(deltas), "cohens_d": d, "abs_d": abs_d,
                "delta_mean": float(np.mean(deltas)), "delta_std": float(np.std(deltas, ddof=1)),
                "bootstrap_95ci": [ci_lo, ci_hi], "ci_excludes_zero": ci_excludes_zero,
                "threshold_d_pass": D_PASS, "verdict": verdict,
            }
        else:
            results["F_PHASE1A_1"] = {"n_events": len(deltas), "verdict": "INSUFFICIENT_EVENTS"}
        log(f"   F-PHASE1A-1: {results['F_PHASE1A_1']}")
    except Exception as e:
        log(f"   FAIL: {traceback.format_exc()}")
        results["F_PHASE1A_1"] = {"ok": False, "error": repr(e)}

    # Stage 5: F-PHASE1A-2 — state discrimination
    try:
        log("Stage 5: F-PHASE1A-2 state discrimination")
        if states_path is None:
            results["F_PHASE1A_2"] = {"verdict": "GATED_NO_STATES_TABLE"}
        else:
            states_grp = h5f[states_path]
            # NWB TimeIntervals has start_time, stop_time, and a vectordata with label
            try:
                start_times = states_grp["start_time"][:]
                stop_times = states_grp["stop_time"][:]
                # find label column
                label_key = None
                for k in states_grp.keys():
                    if k in ("label", "labels", "state", "tags"):
                        label_key = k; break
                labels = [str(x.decode() if isinstance(x, bytes) else x) for x in states_grp[label_key][:]] if label_key else [f"state_{i}" for i in range(len(start_times))]
                from collections import defaultdict
                state_M = defaultdict(list)
                for s, e, lab in zip(start_times, stop_times, labels):
                    if e <= OFFSET_SEC or s >= OFFSET_SEC + MAX_DURATION_SEC: continue
                    mask = (t_arr >= s) & (t_arr < e)
                    if mask.sum() >= 1:
                        state_M[lab].extend(Mr[mask].tolist())
                state_M = {k: v for k, v in state_M.items() if len(v) >= 3}
                if len(state_M) >= 2:
                    from scipy.stats import kruskal
                    groups = list(state_M.values())
                    H, p = kruskal(*groups)
                    # eta-squared approximation
                    N = sum(len(g) for g in groups)
                    eta2 = (H - len(groups) + 1) / (N - len(groups))
                    eta2 = max(0.0, float(eta2))
                    if p < KW_P_PASS and eta2 > ETA2_PASS:
                        verdict = "PASS"
                    elif p < 0.05:
                        verdict = "INCONCLUSIVE_GRAY_ZONE"
                    else:
                        verdict = "REFUTED"
                    results["F_PHASE1A_2"] = {
                        "states": {k: {"n": len(v), "mean_M_r": float(np.mean(v)), "std_M_r": float(np.std(v))} for k, v in state_M.items()},
                        "kruskal_H": float(H), "p_value": float(p), "eta_squared": eta2,
                        "verdict": verdict,
                    }
                else:
                    results["F_PHASE1A_2"] = {"verdict": "INSUFFICIENT_STATES", "n_states": len(state_M)}
            except Exception as inner_e:
                results["F_PHASE1A_2"] = {"verdict": "STATES_READ_FAIL", "error": repr(inner_e)}
        log(f"   F-PHASE1A-2: {results['F_PHASE1A_2']}")
    except Exception as e:
        log(f"   FAIL: {traceback.format_exc()}")
        results["F_PHASE1A_2"] = {"ok": False, "error": repr(e)}

    # Aggregate
    v1 = results.get("F_PHASE1A_1", {}).get("verdict", "?")
    v2 = results.get("F_PHASE1A_2", {}).get("verdict", "?")
    results["aggregate_verdict"] = f"F1={v1} | F2={v2}"
    results["total_elapsed_s"] = round(time.time() - t0, 2)

    try: h5f.close()
    except Exception: pass

    with open(OUT, "w") as f:
        json.dump(results, f, indent=2, default=str)
    log(f"DONE in {time.time()-t0:.1f}s — verdict: {results['aggregate_verdict']}")


if __name__ == "__main__":
    main()
