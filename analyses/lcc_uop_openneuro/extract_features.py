#!/usr/bin/env python3
"""
LCC/UOP empirical test on OpenNeuro ds007471 (joint-agency EEG hyperscanning).

Per-trial NEURAL LCC predictors from two interacting brains:
  C = inter-brain coupling magnitude (mean homologous-ROI PLV in a band)
  P = bidirectional linear-Granger predictive gain (min of the two directions)
  S = temporal stability of the inter-brain phase difference (windowed-PLV concentration)

Behavioural OUTCOMES (from the dataset, not derived):
  JointAgencyRatings (1-7, averaged over the two performers per trial)
  MeanSynchronizationPerformance (proportion asynchrony; LOWER = better -> we use sync_quality = 1-value)

Also caches per-trial per-brain ROI-mean band-limited signals (downsampled) so the
analysis stage can build CROSS-PAIR SURROGATES (common-auditory-input confound control):
two brains that heard the same tone sequence but did NOT interact.

Channels: 1-32 suffix _R, 33-64 suffix _L (per .vhdr labels; README prose is swapped).
Sampling 1000 Hz. Usage: python extract_features.py <pair_int>
"""
import sys, os, json, warnings
import numpy as np
import pandas as pd
from scipy.signal import butter, filtfilt, hilbert, resample_poly

warnings.filterwarnings("ignore")
import mne
mne.set_log_level("ERROR")

HERE = os.path.dirname(os.path.abspath(__file__))
DATA = os.path.join(HERE, "data")
OUT = os.path.join(HERE, "features")
os.makedirs(OUT, exist_ok=True)

FS = 1000.0
DS = 125.0                       # downsample target for VAR/Granger + surrogate cache
ROIS = ["Fz", "FCz", "Cz", "C3", "C4", "Pz"]   # central/motor ROIs per brain
BANDS = {"delta": (1, 4), "theta": (4, 8), "alpha": (8, 12), "beta": (13, 30)}
VAR_ORDER = 5                    # ~40 ms at 125 Hz


def bandpass(x, lo, hi, fs):
    b, a = butter(4, [lo / (fs / 2), hi / (fs / 2)], btype="band")
    return filtfilt(b, a, x, axis=-1)


def plv(ph1, ph2):
    return np.abs(np.mean(np.exp(1j * (ph1 - ph2))))


def windowed_plv_stability(ph1, ph2, fs, win_s=1.0):
    """S: temporal stability of inter-brain phase diff = concentration of per-window mean phase-diffs."""
    w = int(win_s * fs)
    if w < 8 or ph1.size < 2 * w:
        return plv(ph1, ph2)
    means = []
    for k in range(0, ph1.size - w + 1, w):
        d = ph1[k:k + w] - ph2[k:k + w]
        means.append(np.angle(np.mean(np.exp(1j * d))))
    means = np.array(means)
    return float(np.abs(np.mean(np.exp(1j * means))))   # resultant length of window means


def granger_bidir(xr, xl, order=VAR_ORDER):
    """Linear Granger (Geweke) both directions on two 1-D signals; return (GC_R->L, GC_L->R)."""
    def gc(target, source):
        n = target.size
        m = order
        Y = target[m:]
        # restricted: target on its own past
        Xr = np.column_stack([target[m - k - 1:n - k - 1] for k in range(m)] + [np.ones(n - m)])
        # full: + source past
        Xf = np.column_stack([target[m - k - 1:n - k - 1] for k in range(m)]
                             + [source[m - k - 1:n - k - 1] for k in range(m)] + [np.ones(n - m)])
        br, *_ = np.linalg.lstsq(Xr, Y, rcond=None)
        bf, *_ = np.linalg.lstsq(Xf, Y, rcond=None)
        rss_r = np.var(Y - Xr @ br)
        rss_f = np.var(Y - Xf @ bf)
        if rss_f <= 0 or rss_r <= 0:
            return 0.0
        return max(0.0, float(np.log(rss_r / rss_f)))
    return gc(xl, xr), gc(xr, xl)   # R->L drives xl ; L->R drives xr


def load_events(pair):
    p = os.path.join(DATA, f"sub-{pair:02d}", f"sub-{pair:02d}_task-jointaction_events.tsv")
    df = pd.read_csv(p, sep="\t")
    df["ev"] = df["trial_type"].astype(str).str.replace(" ", "", regex=False)
    return df


def parse_full_trials(ev):
    """Full test trials only (both performer parts S2 AND S3 present before S106).
    Blocks delimited by S107. Each block starts with warm-up/practice windows; the
    real test trials are the LAST k full windows of the block. Returns DataFrame with
    block (0-based, by S107 count), cond_marker (1=duet/S10, 0=constant/S11), t0, t1.
    """
    s1 = ev.loc[ev.ev == "S1", "onset"]
    t0 = float(s1.iloc[0]) if len(s1) else 0.0
    e = ev[ev.onset >= t0].reset_index(drop=True)
    onsets = e["onset"].values
    evs = e["ev"].values
    N = len(evs)
    recs = []
    for k in range(N):
        if evs[k] != "S105":
            continue
        j = k + 1
        while j < N and evs[j] != "S106":
            j += 1
        if j >= N:
            continue
        inside = set(evs[k + 1:j])
        if not ({"S2", "S3"} <= inside):     # require both parts -> full trial
            continue
        tone = [onsets[m] for m in range(k + 1, j) if evs[m] in ("S128", "S4")]
        if not tone:
            continue
        w0 = float(min(tone)); w1 = float(onsets[j])
        if w1 - w0 < 3.0:
            continue
        block = int(np.sum(evs[:k] == "S107"))
        # block marker = the S10/S11 immediately preceding this S105
        cm = None
        for m in range(k - 1, -1, -1):
            if evs[m] in ("S10", "S11"):
                cm = 1 if evs[m] == "S10" else 0
                break
        recs.append({"block": block, "cond_marker": cm, "t0": w0, "t1": w1})
    return pd.DataFrame(recs)


def align_to_behaviour(full, bt):
    """Align EEG full-trial windows to the behavioural test trials.

    EEG recordings may contain extra practice blocks (leading/trailing), so block INDEX is
    not reliable. Conditions are counterbalanced across pairs (some start duet, some constant).
    We therefore align by CONDITION SEQUENCE: slide the N-long behavioural condition sequence
    over the ordered EEG block markers (S10=duet=1 / S11=constant=0) and pick the offset with
    the most agreement. Within each matched block, take the LAST k full windows (warm-ups first)
    and map them to that block's k behavioural trials (sorted by TrialNumber).
    Returns list of dicts {t0,t1,brow,block,cond,cond_ok}.
    """
    beh_blocks = sorted(bt["BlockNumber"].unique())
    beh_cond = [int(bt[bt.BlockNumber == bb]["ExperimentalCondition"].iloc[0]) for bb in beh_blocks]
    N = len(beh_blocks)
    eeg_order = sorted(full["block"].unique())
    eeg_marker = []
    for eb in eeg_order:
        cm = full[full.block == eb]["cond_marker"].dropna()
        eeg_marker.append(int(round(cm.mean())) if len(cm) else -1)
    # best sliding offset
    best_off, best_hits = 0, -1
    for off in range(0, max(1, len(eeg_order) - N + 1)):
        hits = sum(1 for i in range(N) if off + i < len(eeg_marker) and eeg_marker[off + i] == beh_cond[i])
        if hits > best_hits:
            best_hits, best_off = hits, off
    cond_ok_global = (best_hits == N)
    out = []
    for i, bb in enumerate(beh_blocks):
        ei = best_off + i
        if ei >= len(eeg_order):
            break
        eb = eeg_order[ei]
        bwin = full[full.block == eb].sort_values("t0")
        brows = bt[bt.BlockNumber == bb].sort_values("TrialNumber")
        k = len(brows)
        use = bwin.tail(k)                    # last k full windows = test trials
        if len(use) != k:
            k = len(use)
            brows = brows.iloc[:k]
        cond = int(brows["ExperimentalCondition"].iloc[0])
        block_ok = (eeg_marker[ei] == cond)
        for (_, w), (_, br) in zip(use.iterrows(), brows.iterrows()):
            out.append({"t0": float(w.t0), "t1": float(w.t1), "brow": br,
                        "block": int(bb), "cond": cond,
                        "cond_ok": bool(block_ok and cond_ok_global)})
    return out


def main(pair):
    sub = f"sub-{pair:02d}"
    d = os.path.join(DATA, sub)
    vhdr = os.path.join(d, f"{sub}_task-jointaction_eeg.vhdr")
    # vhdr/vmrk reference the original acquisition names (e.g. IBS_0001.eeg/.vmrk);
    # symlink those names to the actual BIDS files so MNE can resolve them.
    with open(vhdr) as fh:
        head = fh.read()
    for line in head.splitlines():
        if line.startswith("DataFile="):
            ref = line.split("=", 1)[1].strip()
            tgt = os.path.join(d, f"{sub}_task-jointaction_eeg.eeg")
            lp = os.path.join(d, ref)
            if not os.path.exists(lp) and os.path.exists(tgt):
                os.symlink(os.path.basename(tgt), lp)
        if line.startswith("MarkerFile="):
            ref = line.split("=", 1)[1].strip()
            tgt = os.path.join(d, f"{sub}_task-jointaction_eeg.vmrk")
            lp = os.path.join(d, ref)
            if not os.path.exists(lp) and os.path.exists(tgt):
                os.symlink(os.path.basename(tgt), lp)
    raw = mne.io.read_raw_brainvision(vhdr, preload=True, verbose="ERROR")
    names = raw.ch_names
    idx_R = {r: names.index(f"{r}_R") for r in ROIS if f"{r}_R" in names}
    idx_L = {r: names.index(f"{r}_L") for r in ROIS if f"{r}_L" in names}
    rois = [r for r in ROIS if r in idx_R and r in idx_L]
    dat = raw.get_data()          # (64, N) volts
    R = np.array([dat[idx_R[r]] for r in rois])   # (nroi, N)
    L = np.array([dat[idx_L[r]] for r in rois])

    ev = load_events(pair)
    full = parse_full_trials(ev)

    beh = pd.read_csv(os.path.join(DATA, "behavioural_all.tsv"), sep=r"\s+")
    beh = beh[beh.PairNumber == pair].copy()
    # average the two performers' agency per trial; sync/SD are per-trial (same across the 2 rows)
    bt = (beh.groupby(["BlockNumber", "TrialNumber"])
             .agg(agency=("JointAgencyRatings", "mean"),
                  sync=("MeanSynchronizationPerformance", "mean"),
                  syncsd=("SDSynchronizationPerformance", "mean"),
                  ExperimentalCondition=("ExperimentalCondition", "first"),
                  tone=("ToneSequence", "first"))
             .reset_index())

    aligned = align_to_behaviour(full, bt)
    rows = []
    cache = {}    # (band) -> list of (r_sig, l_sig) downsampled, per trial for surrogates
    for b in BANDS:
        cache[b] = []
    up_dn = (int(DS), int(FS))
    for rec in aligned:
        w0, w1 = rec["t0"], rec["t1"]
        i0, i1 = int(w0 * FS), int(w1 * FS)
        i1 = min(i1, R.shape[1])
        segR = R[:, i0:i1]
        segL = L[:, i0:i1]
        brow = rec["brow"]
        feat = {"pair": pair, "block": rec["block"], "trial": int(brow.TrialNumber),
                "agency": float(brow.agency), "sync": float(brow.sync),
                "syncsd": float(brow.syncsd), "cond": rec["cond"],
                "cond_ok": rec["cond_ok"], "tone": int(brow.tone),
                "dur": (i1 - i0) / FS}
        for b, (lo, hi) in BANDS.items():
            fR = bandpass(segR, lo, hi, FS)
            fL = bandpass(segL, lo, hi, FS)
            phR = np.angle(hilbert(fR, axis=-1))
            phL = np.angle(hilbert(fL, axis=-1))
            # C: mean homologous-ROI inter-brain PLV
            c = np.mean([plv(phR[k], phL[k]) for k in range(len(rois))])
            # S: stability using ROI-mean phase
            mphR = np.angle(np.mean(np.exp(1j * phR), axis=0))
            mphL = np.angle(np.mean(np.exp(1j * phL), axis=0))
            s = windowed_plv_stability(mphR, mphL, FS, 1.0)
            # P: bidirectional Granger on ROI-mean band signals, downsampled
            mR = resample_poly(np.mean(fR, axis=0), up_dn[0], up_dn[1])
            mL = resample_poly(np.mean(fL, axis=0), up_dn[0], up_dn[1])
            gRL, gLR = granger_bidir(mR - mR.mean(), mL - mL.mean())
            p = min(gRL, gLR)
            feat[f"C_{b}"] = float(c)
            feat[f"S_{b}"] = float(s)
            feat[f"P_{b}"] = float(p)
            cache[b].append((mR.astype(np.float32), mL.astype(np.float32)))
        rows.append(feat)

    df = pd.DataFrame(rows)
    df.to_csv(os.path.join(OUT, f"{sub}_features.csv"), index=False)
    # cache signals for surrogate construction (object arrays, ragged)
    np.savez_compressed(
        os.path.join(OUT, f"{sub}_sig.npz"),
        meta=json.dumps({"pair": pair, "trials": df["trial"].tolist(),
                         "tone": df["tone"].tolist(), "cond": df["cond"].tolist(),
                         "fs": DS, "bands": list(BANDS)}),
        **{f"{b}_R": np.array([cache[b][t][0] for t in range(len(df))], dtype=object) for b in BANDS},
        **{f"{b}_L": np.array([cache[b][t][1] for t in range(len(df))], dtype=object) for b in BANDS},
    )
    print(f"{sub}: full_windows={len(full)} beh_trials={len(bt)} aligned={len(df)} "
          f"cond_ok={df['cond_ok'].all() if len(df) else False} rois={rois}")
    print(df[["block", "trial", "cond", "agency", "sync", "C_beta", "P_beta", "S_beta"]].head(6).to_string(index=False))
    return df


if __name__ == "__main__":
    main(int(sys.argv[1]))
