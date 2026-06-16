"""Live open-access animal-data loader (DANDI Archive streaming).

Reuses the corpus streaming pattern (DandiAPIClient + remfile + h5py) from
analyses/pass32_dandi_3way and pass77_b4. Streams a slice of multichannel
LFP/ecephys, returning the same dict shape as simulate.simulate (H=None;
the runner builds a label-free cross-group latent). Any failure -> None so
the runner can fall back to simulation and RECORD that it did so.
"""
import hashlib
import os

import numpy as np

from features import window_grid

_CACHE_DIR = os.path.join(os.path.dirname(os.path.abspath(__file__)), ".dandi_cache")

# (dandiset, asset_path or None -> first .nwb)
CANDIDATES = [
    ("000003", "sub-YutaMouse41/sub-YutaMouse41_ses-YutaMouse41-150829_behavior+ecephys.nwb"),
    ("000003", None),
    ("000552", None),
    ("001044", None),
]


def _find_lfp_dataset(h5):
    """Walk the NWB/HDF5 tree for the largest 2-D numeric dataset that looks
    like an ElectricalSeries (channels x time or time x channels)."""
    best = None
    best_size = 0

    def visit(name, obj):
        nonlocal best, best_size
        try:
            import h5py
            if isinstance(obj, h5py.Dataset) and obj.ndim == 2 and obj.dtype.kind in "fiu":
                if name.endswith("/data") and obj.size > best_size:
                    best = obj
                    best_size = obj.size
        except Exception:
            pass

    h5.visititems(visit)
    return best


def _rate_for(h5, dset):
    """Best-effort sampling rate from the dataset's parent group."""
    try:
        grp = dset.parent
        if "starting_time" in grp and "rate" in grp["starting_time"].attrs:
            return float(grp["starting_time"].attrs["rate"])
        for k in ("rate", "sampling_rate"):
            if k in grp.attrs:
                return float(grp.attrs[k])
    except Exception:
        pass
    return None


def _cache_path(dandiset, asset_path, n_ch, max_samples):
    key = f"{dandiset}|{asset_path}|{n_ch}|{max_samples}"
    h = hashlib.sha1(key.encode()).hexdigest()[:16]
    return os.path.join(_CACHE_DIR, f"{dandiset}_{h}.npz")


def _build_result(raw, fs, dandiset, label_name, win_s, step_s, n_ch):
    # decimate very high rates toward ~250-500 Hz for speed
    decim = max(1, int(fs // 250))
    if decim > 1:
        raw = raw[:, ::decim]
        fs = fs / decim
    # robust per-channel z-score
    raw = (raw - raw.mean(1, keepdims=True)) / (raw.std(1, keepdims=True) + 1e-9)
    n = raw.shape[1]
    starts, w = window_grid(n, fs, win_s, step_s)
    if len(starts) < 40 or raw.shape[0] < 4:
        return None
    a = raw.shape[0] // 2
    return {
        "sig": raw,
        "fs": float(fs),
        "H": None,                         # built by runner (cross-group cluster)
        "starts": starts,
        "w": w,
        "groupA": list(range(a)),
        "groupB": list(range(a, raw.shape[0])),
        "n_states": 3,
        "source": "dandi",
        "label": f"DANDI:{dandiset}/{label_name}",
    }


def load_dandi(dandiset, asset_path=None, n_ch=8, max_samples=180000,
               win_s=2.0, step_s=1.0, default_fs=1250.0):
    # cache hit: skip the network entirely (removes streaming-latency variance)
    cpath = _cache_path(dandiset, asset_path, n_ch, max_samples)
    if os.path.exists(cpath):
        try:
            z = np.load(cpath, allow_pickle=False)
            raw = z["raw"].astype(float)
            fs = float(z["fs"])
            label_name = str(z["label_name"])
            res = _build_result(raw, fs, dandiset, label_name, win_s, step_s, n_ch)
            if res is not None:
                res["source"] = "dandi-cache"
                return res
        except Exception as e:
            print(f"[data_dandi] cache read failed ({type(e).__name__}); restreaming")
    try:
        from dandi.dandiapi import DandiAPIClient
        import remfile
        import h5py

        with DandiAPIClient() as client:
            ds = client.get_dandiset(dandiset, "draft")
            if asset_path is not None:
                asset = ds.get_asset_by_path(asset_path)
            else:
                asset = None
                for a in ds.get_assets():
                    if a.path.endswith(".nwb"):
                        asset = a
                        break
                if asset is None:
                    return None
            url = asset.get_content_url(follow_redirects=1, strip_query=True)

        rf = remfile.File(url=url)
        h5 = h5py.File(rf, "r")
        dset = _find_lfp_dataset(h5)
        if dset is None:
            return None
        fs = _rate_for(h5, dset) or default_fs

        # orient as (channels, samples)
        if dset.shape[0] >= dset.shape[1]:        # (time, channels)
            nsamp = min(max_samples, dset.shape[0])
            nc = min(n_ch, dset.shape[1])
            raw = np.asarray(dset[:nsamp, :nc], dtype=float).T
        else:                                      # (channels, time)
            nsamp = min(max_samples, dset.shape[1])
            nc = min(n_ch, dset.shape[0])
            raw = np.asarray(dset[:nc, :nsamp], dtype=float)

        label_name = asset.path.split('/')[-1]
        # persist the streamed raw slice so re-runs skip the network entirely
        try:
            os.makedirs(_CACHE_DIR, exist_ok=True)
            np.savez_compressed(cpath, raw=raw, fs=float(fs),
                                label_name=label_name)
        except Exception as e:
            print(f"[data_dandi] cache write failed ({type(e).__name__}); continuing")

        return _build_result(raw, float(fs), dandiset, label_name,
                             win_s, step_s, n_ch)
    except Exception as e:  # network / parsing / asset issues -> fallback
        print(f"[data_dandi] {dandiset} failed: {type(e).__name__}: {e}")
        return None


def load_first_available(max_sources=2, **kw):
    out = []
    for ds, path in CANDIDATES:
        if len(out) >= max_sources:
            break
        d = load_dandi(ds, path, **kw)
        if d is not None:
            print(f"[data_dandi] loaded {d['label']} "
                  f"({d['sig'].shape[0]} ch x {d['sig'].shape[1]} samp @ {d['fs']:.0f}Hz, "
                  f"{len(d['starts'])} windows)")
            out.append(d)
    return out
