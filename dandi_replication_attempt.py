"""URB #808 — DANDI replication attempt for the C_EMERICK ~= 0.4370 anchor.

Tries to download a small subset of a public neural dataset from DANDI
(prefers DANDI:000559 Allen Visual Coding; falls back to DANDI:000552
hippocampal ripple data) using only the public REST API + direct HTTPS
GET (no `dandi` package install required).

For each downloaded NWB asset, extracts an LFP-like time series from a
small number of channels, segments it into T=300-sample windows,
computes Form B LCC pairwise, and reports the per-segment mean LCC
distribution.

Decision tree:
  - H4 SUPPORTED: mean LCC in [0.412, 0.462]
  - H4 FALSIFIED: mean LCC outside [0.412, 0.462] AND 95% CI excludes
                  C_EMERICK
  - H4 INCONCLUSIVE: mean inside band but CI wide; or download failed
"""

import json
import math
import os
import time
import urllib.request
import urllib.error

import numpy as np
import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt

PHI = (1.0 + 5.0**0.5) / 2.0
C_EMERICK = 1.0 / (PHI * 2.0**0.5)
ACCEPT_BAND = (0.412, 0.462)
T_SEG = 300
SIGMA = 5.0
MAX_LAG = 15
DOWNLOAD_BUDGET_BYTES = 200 * 1024 * 1024  # 200 MB hard cap
TIMEOUT_S = 30

CANDIDATES = [
    ("000559", "Allen Visual Coding Neuropixels"),
    ("000552", "Hippocampal ripples (URB #401 anchor source)"),
    ("000582", "NHP wake/sleep cortex"),
]
ASSET_LIST_URL = "https://api.dandiarchive.org/api/dandisets/{ds}/versions/draft/assets/?page_size=20"


def lcc_resonance_form_b(a, b, sigma=SIGMA, max_lag=MAX_LAG):
    a = (a - a.mean()) / (a.std() + 1e-12)
    b = (b - b.mean()) / (b.std() + 1e-12)
    n = len(a)
    best = 0.0
    for tau in range(-max_lag, max_lag + 1):
        if tau >= 0:
            x, y = a[: n - tau], b[tau:]
        else:
            x, y = a[-tau:], b[: n + tau]
        if len(x) < 2:
            continue
        rho = float(np.dot(x, y) / len(x))
        w = math.exp(-(tau * tau) / (2.0 * sigma * sigma))
        v = rho * w
        if abs(v) > abs(best):
            best = v
    return best


def http_get_json(url, timeout=TIMEOUT_S):
    req = urllib.request.Request(url, headers={"Accept": "application/json"})
    with urllib.request.urlopen(req, timeout=timeout) as r:
        return json.loads(r.read().decode("utf-8"))


def list_assets(ds, max_pages=2):
    url = ASSET_LIST_URL.format(ds=ds)
    assets = []
    page = 0
    while url and page < max_pages:
        try:
            data = http_get_json(url)
        except Exception as e:
            print(f"    list_assets({ds}) page {page} failed: {e}")
            return assets
        for r in data.get("results", []):
            assets.append({
                "asset_id": r.get("asset_id"),
                "path": r.get("path"),
                "size": r.get("size"),
            })
        url = data.get("next")
        page += 1
    return assets


def asset_download_url(ds, asset_id):
    return f"https://api.dandiarchive.org/api/dandisets/{ds}/versions/draft/assets/{asset_id}/download/"


def head_check(url, timeout=TIMEOUT_S):
    """Returns (final_url, content_length) following redirects."""
    req = urllib.request.Request(url, method="HEAD")
    try:
        with urllib.request.urlopen(req, timeout=timeout) as r:
            return r.geturl(), int(r.headers.get("Content-Length", "0"))
    except Exception as e:
        print(f"    HEAD {url[:80]}... failed: {e}")
        return None, 0


def download_partial(url, out_path, max_bytes, timeout=TIMEOUT_S):
    """Stream-download up to max_bytes; return bytes actually written."""
    req = urllib.request.Request(url)
    written = 0
    try:
        with urllib.request.urlopen(req, timeout=timeout) as r, open(out_path, "wb") as f:
            chunk = 1 << 18  # 256 KB
            while True:
                if written >= max_bytes:
                    break
                buf = r.read(min(chunk, max_bytes - written))
                if not buf:
                    break
                f.write(buf)
                written += len(buf)
    except Exception as e:
        print(f"    download failed at {written} bytes: {e}")
    return written


def try_extract_with_h5py(nwb_path):
    """Try to load LFP-like data from a partial NWB (HDF5) file. Returns ndarray or None."""
    try:
        import h5py
    except ImportError:
        return None, "h5py not available"
    try:
        with h5py.File(nwb_path, "r") as f:
            candidates = []

            def visit(name, obj):
                if isinstance(obj, h5py.Dataset) and obj.ndim >= 1:
                    sz = int(np.prod(obj.shape))
                    if sz >= 5000 and obj.dtype.kind in ("f", "i", "u"):
                        candidates.append((sz, name, obj.shape, str(obj.dtype)))

            f.visititems(visit)
            if not candidates:
                return None, "no usable dataset found in partial NWB"
            candidates.sort(reverse=True)
            sz, name, shape, dtype = candidates[0]
            print(f"    extracting from dataset '{name}' shape={shape} dtype={dtype}")
            ds = f[name]
            if ds.ndim == 1:
                return np.asarray(ds[: min(50000, ds.shape[0])], dtype=np.float64), name
            elif ds.ndim == 2:
                n_ch = min(16, ds.shape[1] if ds.shape[1] < ds.shape[0] else ds.shape[0])
                if ds.shape[0] > ds.shape[1]:
                    return np.asarray(ds[: min(50000, ds.shape[0]), :n_ch], dtype=np.float64), name
                else:
                    return np.asarray(ds[:n_ch, : min(50000, ds.shape[1])], dtype=np.float64).T, name
            else:
                return None, f"dataset {name} has unsupported ndim {ds.ndim}"
    except Exception as e:
        return None, f"h5py read failed: {e}"


def compute_per_segment_lcc(data_2d):
    """data_2d: (T, n_channels). Returns list of per-segment mean pairwise LCC."""
    if data_2d.ndim == 1:
        return []
    T_total, n_ch = data_2d.shape
    n_seg = T_total // T_SEG
    if n_seg < 1 or n_ch < 2:
        return []
    out = []
    for s in range(n_seg):
        seg = data_2d[s * T_SEG : (s + 1) * T_SEG, :]
        lccs = []
        for i in range(n_ch):
            for j in range(i + 1, n_ch):
                lccs.append(lcc_resonance_form_b(seg[:, i], seg[:, j]))
        out.append(float(np.mean(lccs)))
    return out


def main():
    t0 = time.time()
    os.makedirs(".dandi_cache", exist_ok=True)
    result = {
        "C_EMERICK": C_EMERICK,
        "accept_band": list(ACCEPT_BAND),
        "candidates_tried": [],
        "outcome": "PENDING",
        "wall_time_s": None,
    }

    for ds, name in CANDIDATES:
        print(f"\n[{time.time()-t0:.1f}s] === Trying DANDI:{ds} ({name}) ===")
        cand = {"dandiset": ds, "name": name, "stage": "list_assets"}
        result["candidates_tried"].append(cand)

        assets = list_assets(ds)
        cand["n_assets_listed"] = len(assets)
        if not assets:
            cand["outcome"] = "no assets returned"
            continue

        nwb_assets = [a for a in assets if a["path"] and a["path"].lower().endswith(".nwb")]
        if not nwb_assets:
            cand["outcome"] = "no .nwb in first page"
            continue
        nwb_assets.sort(key=lambda a: a.get("size") or 0)
        chosen = nwb_assets[0]
        cand["chosen_asset"] = chosen
        print(f"    chose smallest .nwb: {chosen['path']}  size={chosen.get('size'):,} bytes")

        if chosen.get("size") and chosen["size"] > 5 * 1024 * 1024 * 1024:
            cand["outcome"] = f"smallest asset too large: {chosen['size']:,} bytes"
            continue

        dl_url = asset_download_url(ds, chosen["asset_id"])
        out_path = os.path.join(".dandi_cache", f"{ds}_{chosen['asset_id'][:12]}.nwb")
        cand["stage"] = "download"
        print(f"    downloading up to {DOWNLOAD_BUDGET_BYTES // (1024*1024)} MB ...")
        n_bytes = download_partial(dl_url, out_path, DOWNLOAD_BUDGET_BYTES)
        cand["bytes_downloaded"] = n_bytes
        if n_bytes < 1024 * 1024:
            cand["outcome"] = f"only {n_bytes} bytes downloaded; abandoning this candidate"
            continue
        print(f"    downloaded {n_bytes / (1024*1024):.1f} MB")

        cand["stage"] = "extract"
        data, info = try_extract_with_h5py(out_path)
        cand["extract_info"] = str(info) if data is None else f"shape={list(data.shape)}"
        if data is None:
            cand["outcome"] = f"extract failed: {info}"
            continue

        cand["stage"] = "lcc"
        if data.ndim == 1:
            data = data.reshape(-1, 1)
        if data.shape[1] < 2:
            print(f"    only {data.shape[1]} channel; cannot do pairwise LCC. Skipping.")
            cand["outcome"] = "only 1 channel; cannot do pairwise LCC"
            continue

        per_seg_lcc = compute_per_segment_lcc(data)
        cand["n_segments"] = len(per_seg_lcc)
        if len(per_seg_lcc) < 5:
            cand["outcome"] = f"only {len(per_seg_lcc)} segments; underpowered"
            continue

        arr = np.array(per_seg_lcc)
        mean_lcc = float(arr.mean())
        std_lcc = float(arr.std(ddof=1))
        ci95 = 1.96 * std_lcc / math.sqrt(len(arr))
        cand["mean_lcc"] = mean_lcc
        cand["std_lcc"] = std_lcc
        cand["ci95"] = ci95
        cand["n"] = len(arr)
        in_band = ACCEPT_BAND[0] <= mean_lcc <= ACCEPT_BAND[1]
        ci_excludes_C = (mean_lcc + ci95 < C_EMERICK) or (mean_lcc - ci95 > C_EMERICK)
        if in_band and not ci_excludes_C:
            cand["outcome"] = "H4_SUPPORTED"
            result["outcome"] = "H4_SUPPORTED"
        elif (not in_band) and ci_excludes_C:
            cand["outcome"] = "H4_FALSIFIED"
            if result["outcome"] == "PENDING":
                result["outcome"] = "H4_FALSIFIED"
        else:
            cand["outcome"] = "H4_INCONCLUSIVE"
            if result["outcome"] == "PENDING":
                result["outcome"] = "H4_INCONCLUSIVE"

        print(f"\n    >>> n={len(arr)}  mean LCC={mean_lcc:+.4f}  std={std_lcc:.4f}  "
              f"95% CI=[{mean_lcc-ci95:+.4f}, {mean_lcc+ci95:+.4f}]")
        print(f"    accept band: [{ACCEPT_BAND[0]:.3f}, {ACCEPT_BAND[1]:.3f}]; "
              f"C_EMERICK={C_EMERICK:.4f}; outcome={cand['outcome']}")

        try:
            fig, ax = plt.subplots(figsize=(8, 5))
            ax.hist(arr, bins=20, color="tab:blue", alpha=0.7)
            ax.axvline(C_EMERICK, color="red", linestyle="--", label=f"C_EMERICK={C_EMERICK:.4f}")
            ax.axvspan(ACCEPT_BAND[0], ACCEPT_BAND[1], color="green", alpha=0.15, label="H4 accept band")
            ax.axvline(mean_lcc, color="black", linestyle="-", label=f"mean={mean_lcc:.4f}")
            ax.set_xlabel("Per-segment mean pairwise LCC (Form B)")
            ax.set_ylabel("count")
            ax.set_title(f"DANDI:{ds} replication: outcome = {cand['outcome']}")
            ax.legend()
            plt.tight_layout()
            plt.savefig(f"dandi_replication_{ds}.png", dpi=120)
            plt.close()
        except Exception as e:
            print(f"    plot failed: {e}")
        break

    if result["outcome"] == "PENDING":
        result["outcome"] = "PROTOCOL_ATTEMPTED_NO_USABLE_DATA"

    result["wall_time_s"] = float(time.time() - t0)
    with open("dandi_replication_attempt_report.json", "w", encoding="utf-8") as f:
        json.dump(result, f, indent=2)
    print(f"\n[{time.time()-t0:.1f}s] FINAL OUTCOME: {result['outcome']}")
    print(f"  report -> dandi_replication_attempt_report.json")


if __name__ == "__main__":
    main()
