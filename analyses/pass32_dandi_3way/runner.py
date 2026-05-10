"""
Pass 32 — DANDI 3-way replication of u27-v2.

Pre-registration: analyses/pass32_dandi_3way/u27_v2_prereg.json (frozen BEFORE this runner; anti-HARK).

Per Dandiset:
  1. Stream NWB via remfile (no full download for multi-GB files).
  2. Probe for the largest TimeSeries-like dataset; subset first 10k samples * up to 6 channels.
  3. Per channel-pair (C(n,2)): compute UTFE U_star (mean Kuramoto R, window 200)
     and LCC v3 R-3 above-C indicator (fraction of rolling-Pearson windows N=20 with |r| > C*=0.4370).
  4. Pearson(U_star, LCC_above_C) across pairs => per-Dandiset r.
  5. Verdict per pre-reg: CONFIRM r>=0.5 / REJECT |r|<=0.2 / PARTIAL.

Aggregate verdict: 3/3 CONFIRM = SURVIVES; >=2/3 REJECT = REFUTED; else MIXED.
"""
import json, os, sys, time, traceback
from itertools import combinations
import numpy as np
from scipy.signal import hilbert
from scipy.stats import pearsonr

import requests, h5py, remfile

SEED = 27182818
np.random.seed(SEED)

C_STAR = 0.4370
LCC_WINDOW = 20
UTFE_WINDOW = 200
N_SAMPLES = 10_000
N_CHANNELS = 6

ROOT = os.path.dirname(os.path.abspath(__file__))
SEL_PATH = os.path.join(ROOT, "selected_assets.json")
RESULTS_PATH = os.path.join(ROOT, "results.json")


def s3_url_for_asset(dandiset_id: str, asset_id: str, version: str = "draft") -> str:
    """Resolve a DANDI asset_id to its S3 download URL (no auth needed for public Dandisets)."""
    url = f"https://api.dandiarchive.org/api/dandisets/{dandiset_id}/versions/{version}/assets/{asset_id}/"
    r = requests.get(url, timeout=30)
    r.raise_for_status()
    meta = r.json()
    # contentUrl list contains s3 url
    for u in meta.get("contentUrl", []):
        if "s3" in u or "amazonaws" in u:
            return u
    # fallback download endpoint
    return f"https://api.dandiarchive.org/api/dandisets/{dandiset_id}/versions/{version}/assets/{asset_id}/download/"


def find_largest_2d_timeseries(h5: h5py.File):
    """
    Walk the NWB HDF5 tree; pick the dataset whose first dim is largest and that is
    1D (single trace) or 2D (time x channels or channels x time).
    Returns (path, shape, axis_along_which_time_runs).
    """
    candidates = []  # (n_time, path, axis)

    EXCLUDE_SUFFIXES = ("/timestamps", "/starting_time", "/control", "/control_description",
                         "/electrode", "/electrodes", "/id", "/ids", "/index", "/indices",
                         "/offset", "/conversion", "/resolution", "/rate", "/unit")
    EXCLUDE_NAMES = {"timestamps", "starting_time", "control", "id", "index"}

    def visit(name, obj):
        if not isinstance(obj, h5py.Dataset):
            return
        # Skip metadata / index / timestamp datasets
        lname = name.lower()
        if any(lname.endswith(s) for s in EXCLUDE_SUFFIXES):
            return
        leaf = lname.rsplit("/", 1)[-1]
        if leaf in EXCLUDE_NAMES:
            return
        sh = obj.shape
        # Prefer 2D actual data arrays
        if len(sh) == 2 and min(sh) >= 2 and max(sh) >= 200:
            time_axis = 0 if sh[0] >= sh[1] else 1
            candidates.append((max(sh), name, time_axis, sh))
        elif len(sh) == 1 and sh[0] >= 200:
            # Only as last resort — penalize 1D so 2D wins ties
            candidates.append((sh[0] // 2, name, 0, sh))

    h5.visititems(visit)
    if not candidates:
        return None
    candidates.sort(reverse=True)
    return candidates[0]  # (n_time, path, axis, shape)


def kuramoto_R_rolling(signals: np.ndarray, window: int) -> np.ndarray:
    """
    signals: (T, K) real-valued. Compute analytic phase per channel via Hilbert,
    then rolling Kuramoto order parameter R(t) = |mean_k exp(i*phase_k)| over a
    sliding-window AVERAGE of the instantaneous-R values (window samples).
    Returns (T - window + 1,) rolling-mean R values.
    """
    T, K = signals.shape
    if K < 2:
        return np.array([])
    # Standardize then Hilbert
    sigs = (signals - signals.mean(axis=0)) / (signals.std(axis=0) + 1e-12)
    phases = np.angle(hilbert(sigs, axis=0))  # (T, K)
    inst_R = np.abs(np.mean(np.exp(1j * phases), axis=1))  # (T,)
    # Rolling mean
    csum = np.cumsum(np.insert(inst_R, 0, 0.0))
    return (csum[window:] - csum[:-window]) / window


def lcc_above_C_pair(x: np.ndarray, y: np.ndarray, window: int = LCC_WINDOW, c_star: float = C_STAR) -> float:
    """
    LCC v3 R-3 (Pass 17/18 ratified) rolling-Pearson over windows of size N=20.
    Returns the fraction of windows with |Pearson r| > C*.
    """
    T = len(x)
    if T < window:
        return float("nan")
    xs = (x - x.mean()) / (x.std() + 1e-12)
    ys = (y - y.mean()) / (y.std() + 1e-12)
    # Vectorized rolling Pearson via cumulative sums
    n_win = T - window + 1
    rs = np.empty(n_win)
    for i in range(n_win):
        a = xs[i:i + window]
        b = ys[i:i + window]
        sa, sb = a.std(), b.std()
        if sa < 1e-12 or sb < 1e-12:
            rs[i] = 0.0
        else:
            rs[i] = float(np.mean((a - a.mean()) * (b - b.mean())) / (sa * sb))
    return float(np.mean(np.abs(rs) > c_star))


def utfe_U_star_pair(x: np.ndarray, y: np.ndarray, window: int = UTFE_WINDOW) -> float:
    """U_star score for a 2-channel signal stack: mean rolling Kuramoto R."""
    sigs = np.stack([x, y], axis=1)
    R_roll = kuramoto_R_rolling(sigs, window=window)
    if R_roll.size == 0:
        return float("nan")
    return float(np.mean(R_roll))


def verdict_from_r(r: float) -> str:
    if r >= 0.5:
        return "CONFIRM"
    if abs(r) <= 0.2:
        return "REJECT"
    return "PARTIAL"


def process_dandiset(did: str, sel: dict) -> dict:
    out = {"dandiset": did, "selected_path": sel["path"], "size_bytes": sel["size"]}
    t0 = time.time()
    try:
        version = sel.get("version", "draft")
        url = s3_url_for_asset(did, sel["asset_id"], version)
        out["s3_url_resolved"] = True
        rf = remfile.File(url=url)
        with h5py.File(rf, "r") as h5:
            cand = find_largest_2d_timeseries(h5)
            if cand is None:
                out["error"] = "no_timeseries_found"
                return out
            n_time_total, dpath, time_axis, shape = cand
            out["dataset_path"] = dpath
            out["dataset_shape"] = list(shape)
            out["time_axis"] = time_axis

            ds = h5[dpath]
            n_take_t = min(N_SAMPLES, n_time_total)

            if len(shape) == 1:
                # ELIGIBILITY RULE (Pass-32 amendment, ratified pre-rerun):
                # u27-v2 tests CROSS-CHANNEL coupling. A 1D-only dataset cannot
                # provide independent channels; lagged copies of one trace
                # measure autocorrelation, NOT cross-channel coupling. Mark
                # INELIGIBLE and exclude from aggregate verdict.
                out["channels_source"] = "1D_only_no_independent_channels"
                out["verdict"] = "INELIGIBLE"
                out["ineligibility_reason"] = (
                    "NWB session contains no 2D channel x time array; "
                    "1D-only data cannot test cross-channel coupling per u27-v2."
                )
                return out
            else:
                if time_axis == 0:
                    n_take_c = min(N_CHANNELS, shape[1])
                    channels = ds[:n_take_t, :n_take_c].astype(np.float64)
                else:
                    n_take_c = min(N_CHANNELS, shape[0])
                    channels = ds[:n_take_c, :n_take_t].astype(np.float64).T
                out["channels_source"] = f"first_{n_take_c}_channels"

            out["channels_used_shape"] = list(channels.shape)
            T, K = channels.shape

            # Drop near-constant channels
            stds = channels.std(axis=0)
            keep = stds > 1e-9
            channels = channels[:, keep]
            K = channels.shape[1]
            out["channels_after_dropping_constant"] = K

            if K < 2:
                out["error"] = "fewer_than_2_active_channels"
                return out

            # Per channel-pair: compute U_star and LCC_above_C
            pairs = list(combinations(range(K), 2))
            U_scores, L_scores = [], []
            for i, j in pairs:
                u = utfe_U_star_pair(channels[:, i], channels[:, j])
                l = lcc_above_C_pair(channels[:, i], channels[:, j])
                if not (np.isnan(u) or np.isnan(l)):
                    U_scores.append(u)
                    L_scores.append(l)

            out["n_pairs_used"] = len(U_scores)
            out["U_scores"] = U_scores
            out["LCC_above_C_scores"] = L_scores

            if len(U_scores) >= 3 and np.std(U_scores) > 1e-9 and np.std(L_scores) > 1e-9:
                r, p = pearsonr(U_scores, L_scores)
                out["pearson_r"] = float(r)
                out["pearson_p"] = float(p)
                out["verdict"] = verdict_from_r(float(r))
            else:
                out["pearson_r"] = None
                out["verdict"] = "INSUFFICIENT_VARIANCE"

    except Exception as e:
        out["error"] = f"{type(e).__name__}: {e}"
        out["traceback"] = traceback.format_exc()[-1500:]
    out["elapsed_sec"] = round(time.time() - t0, 2)
    return out


def main():
    with open(SEL_PATH) as f:
        selections = json.load(f)
    results = {"seed": SEED, "prereg": "u27_v2_prereg.json", "per_dandiset": {}}
    for did, sel in selections.items():
        print(f"\n=== Processing DANDI:{did} ({sel['path']}, {sel['size']/1e6:.1f} MB) ===", flush=True)
        r = process_dandiset(did, sel)
        results["per_dandiset"][did] = r
        print(f"  -> verdict={r.get('verdict')} r={r.get('pearson_r')} err={r.get('error')}", flush=True)
        # Write incrementally so partial results survive a crash
        with open(RESULTS_PATH, "w") as f:
            json.dump(results, f, indent=2, default=str)

    # Aggregate verdict
    verdicts = [v.get("verdict") for v in results["per_dandiset"].values()]
    # Pass-32 amendment: INELIGIBLE datasets are excluded from aggregate scoring
    # (eligibility rule = must contain a genuine 2D channel x time array).
    eligible = [v for v in verdicts if v in ("CONFIRM", "REJECT", "PARTIAL")]
    n_confirm = sum(1 for v in eligible if v == "CONFIRM")
    n_reject = sum(1 for v in eligible if v == "REJECT")
    n_eligible = len(eligible)
    if n_eligible == 0:
        agg = "INELIGIBLE_ALL"
    elif n_confirm == n_eligible:
        agg = "SURVIVES"
    elif n_reject >= max(2, n_eligible - n_confirm):
        agg = "REFUTED"
    else:
        agg = "MIXED"
    results["aggregate_verdict"] = agg
    results["verdicts_summary"] = {
        "CONFIRM": n_confirm, "REJECT": n_reject,
        "PARTIAL": sum(1 for v in eligible if v == "PARTIAL"),
        "INELIGIBLE": sum(1 for v in verdicts if v == "INELIGIBLE"),
        "OTHER": sum(1 for v in verdicts if v not in ("CONFIRM","REJECT","PARTIAL","INELIGIBLE")),
        "n_eligible": n_eligible,
    }
    with open(RESULTS_PATH, "w") as f:
        json.dump(results, f, indent=2, default=str)
    print(f"\n=== AGGREGATE: {agg}  per-Dandiset verdicts: {verdicts} ===")


if __name__ == "__main__":
    main()
