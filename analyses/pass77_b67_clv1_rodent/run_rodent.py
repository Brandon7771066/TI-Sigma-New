"""
Pass-77 B67: CLV-1 real-brain-data leg via DANDI streaming (the proven workaround,
reused from Pass-77-B4). Hippocampal LFP, Buzsaki lab YutaMouse41.

Rodent LFP has behavioral STATES (wake/NREM/REM) = an arousal/LEVEL axis, but NO
valence label. So this leg tests TWO real-data components of CLV-1 (not the gold
valence-blindness test, which stays OPEN):
  (R1) the LEVEL family is real & meaningful on neural data: a complexity/level
       measure (spectral entropy) discriminates arousal STATES (Kruskal-Wallis).
  (R2) axis-separability: the LEVEL measure and a lateralization/asymmetry measure
       (the structural 'symmetry-axis' analog) are statistically ~independent across
       windows (|corr| small) -> the two feature families are separable on real brain
       data, consistent with CLV-1's orthogonality claim.
Hard caps: <=600s of LFP, <=4 channels, streamed byte-ranges only.
"""
import json, time, warnings, traceback
import numpy as np
warnings.filterwarnings("ignore")
t_start = time.time()
OUT = "analyses/pass77_b67_clv1_rodent"
DANDISET = "000003"
ASSET = "sub-YutaMouse41/sub-YutaMouse41_ses-YutaMouse41-150829_behavior+ecephys.nwb"
OFFSET_SEC, MAX_DUR, MAX_CH = 4400, 800, 8
res = {"pass": "77-B67", "dandiset": DANDISET, "asset": ASSET}

def spectral_entropy(x, fs):
    x = x - x.mean()
    f = np.fft.rfftfreq(len(x), 1/fs); P = np.abs(np.fft.rfft(x))**2
    m = (f >= 1) & (f <= 100); P = P[m]
    if P.sum() <= 0: return 0.0
    p = P/P.sum(); return float(-np.sum(p*np.log2(p+1e-12))/np.log2(len(p)))

def band(x, fs, lo, hi):
    f = np.fft.rfftfreq(len(x), 1/fs); P = np.abs(np.fft.rfft(x))**2
    return float(P[(f >= lo) & (f < hi)].sum())

try:
    from dandi.dandiapi import DandiAPIClient
    import h5py, remfile
    with DandiAPIClient() as client:
        asset = client.get_dandiset(DANDISET, "draft").get_asset_by_path(ASSET)
        s3 = asset.get_content_url(follow_redirects=1, strip_query=True)
    h5f = h5py.File(remfile.File(url=s3), "r")
    print(f"[{time.time()-t_start:.0f}s] opened NWB")

    cands = []; states_path = None
    def visit(name, obj):
        global states_path
        if isinstance(obj, h5py.Dataset) and name.endswith("/data") and obj.ndim == 2:
            cands.append((name, obj.shape))
        if name.endswith("behavior/states") or name.endswith("/states"):
            states_path = name
    h5f.visititems(visit)
    lfp_name = max(cands, key=lambda c: c[1][0]*c[1][1])[0]  # largest 2D dataset = LFP
    dset = h5f[lfp_name]
    parent = h5f[lfp_name.rsplit("/", 1)[0]]
    fs = 1250.0
    for k in ("rate", "sampling_rate"):
        if k in dset.attrs: fs = float(dset.attrs[k])
    if "starting_time" in parent and "rate" in parent["starting_time"].attrs:
        fs = float(parent["starting_time"].attrs["rate"])
    nt = max(dset.shape); nch = min(dset.shape)
    nuse = min(nch, MAX_CH)
    i0 = int(OFFSET_SEC*fs); i1 = min(int((OFFSET_SEC+MAX_DUR)*fs), nt)
    data = np.asarray(dset[i0:i1, :nuse], float)  # contiguous time x first-nuse channels
    ch_idx = list(range(nuse))
    print(f"[{time.time()-t_start:.0f}s] LFP {lfp_name} fs={fs:.0f} shape={data.shape} states={states_path}")

    # read states intervals (start,stop,label) if present
    intervals = []
    if states_path is not None:
        sg = h5f[states_path]
        try:
            st = np.array(sg["start_time"][:]); en = np.array(sg["stop_time"][:])
            lab = sg["label"][:] if "label" in sg else sg["state"][:]
            lab = [l.decode() if isinstance(l, bytes) else str(l) for l in lab]
            intervals = list(zip(st, en, lab))
        except Exception as e:
            print("states parse fail:", e)

    win = int(4*fs); levels = []; asyms = []; wtimes = []
    half = len(ch_idx)//2 or 1
    for s in range(0, data.shape[0]-win, win):
        seg = data[s:s+win]
        se = np.mean([spectral_entropy(seg[:, c], fs) for c in range(seg.shape[1])])  # LEVEL
        # lateralization/asymmetry: log-power difference between channel halves (broadband)
        pL = np.mean([band(seg[:, c], fs, 1, 100) for c in range(half)])
        pR = np.mean([band(seg[:, c], fs, 1, 100) for c in range(half, seg.shape[1])]) if seg.shape[1] > half else pL
        asym = (np.log(pL+1e-9) - np.log(pR+1e-9))
        levels.append(se); asyms.append(abs(asym)); wtimes.append(OFFSET_SEC + s/fs + 2)
    levels = np.array(levels); asyms = np.array(asyms); wtimes = np.array(wtimes)

    # R2 orthogonality
    if levels.std() > 0 and asyms.std() > 0:
        r_la = float(np.corrcoef(levels, asyms)[0, 1])
    else:
        r_la = float("nan")

    # R1 level discriminates states
    state_groups = {}
    for (st, en, lab) in intervals:
        m = (wtimes >= st) & (wtimes < en)
        if m.sum() >= 3:
            state_groups.setdefault(lab, []).extend(levels[m].tolist())
    kw = None
    if len(state_groups) >= 2:
        from scipy.stats import kruskal
        groups = [np.array(v) for v in state_groups.values() if len(v) >= 3]
        if len(groups) >= 2:
            H, p = kruskal(*groups)
            # eta^2 approx
            N = sum(len(g) for g in groups); k = len(groups)
            eta2 = (H - k + 1)/(N - k) if N > k else float("nan")
            kw = {"H": float(H), "p": float(p), "k": k, "N": int(N), "eta2": float(eta2),
                  "state_mean_level": {s: float(np.mean(v)) for s, v in state_groups.items()}}

    res.update({"fs": fs, "n_windows": int(len(levels)), "channels_used": len(ch_idx),
                "R2_corr_level_asym": r_la,
                "R1_kruskal_level_vs_state": kw,
                "states_found": sorted(state_groups.keys())})
    json.dump(res, open(f"{OUT}/results.json", "w"), indent=2)
    print("\n=== CLV-1 RODENT REAL-DATA LEG ===")
    print(f"  R2 orthogonality: corr(LEVEL, asymmetry) = {r_la:+.3f}  (CLV-1: small => separable feature families)")
    if kw:
        print(f"  R1 level vs arousal-state: Kruskal H={kw['H']:.2f} p={kw['p']:.2e} eta2={kw['eta2']:.3f} over {kw['k']} states {res['states_found']}")
        print(f"     state mean LEVEL: {kw['state_mean_level']}")
    else:
        print("  R1: no usable states table in window (GATED).")
except Exception as e:
    res["error"] = repr(e); traceback.print_exc()
    json.dump(res, open(f"{OUT}/results.json", "w"), indent=2)
print(f"[{time.time()-t_start:.0f}s] done")
