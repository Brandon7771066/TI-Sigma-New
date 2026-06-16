"""Live open-access rodent HEMODYNAMIC loader (best-effort, honest fallback).

#69 data-availability reality (probed 2026-06-16):
  * Rodent BOLD-fMRI is NOT on DANDI (000623=human, 001773=primate DBS). It lives
    on OpenNeuro as 4-D NIFTI (heavy; needs nibabel + ROI extraction). Left as an
    OPTIONAL leg (attempted only if a local NIFTI is provided), so the batch never
    blocks on a multi-hundred-MB download in a $0 sandbox.
  * Open-access rodent fNIRS effectively DOES NOT EXIST (fNIRS is overwhelmingly a
    human modality). Honestly recorded as unavailable -> fNIRS is simulation-only.
  * The nearest LIVE rodent hemodynamic signal that streams here is DANDI
    001211 / 001543 "Neurovascular impulse response function" (Mus musculus,
    one-photon cell-population optical imaging). Neurovascular = exactly the
    haemodynamic process fMRI/fNIRS measure -> used as the live hemodynamic anchor,
    LABELLED for what it is (optical neurovascular, not BOLD/fNIRS).

Any failure -> None so the runner falls back to simulation and RECORDS that it did.
"""
import hashlib
import os

import numpy as np

from features import window_grid

_CACHE_DIR = os.path.join(os.path.dirname(os.path.abspath(__file__)), ".live_cache")

# DANDI mouse neurovascular (optical hemodynamic) candidates.
CANDIDATES = [
    ("001543", None),
    ("001211", None),
]


def _find_2d(h5):
    import h5py
    best, best_size = None, 0
    def visit(name, obj):
        nonlocal best, best_size
        try:
            if (isinstance(obj, h5py.Dataset) and obj.ndim == 2
                    and obj.dtype.kind in "fiu" and name.endswith("/data")
                    and obj.size > best_size):
                best, best_size = obj, obj.size
        except Exception:
            pass
    h5.visititems(visit)
    return best


def _rate_for(h5, dset, default):
    try:
        g = dset.parent
        if "starting_time" in g and "rate" in g["starting_time"].attrs:
            return float(g["starting_time"].attrs["rate"])
        for k in ("rate", "sampling_rate"):
            if k in g.attrs:
                return float(g.attrs[k])
    except Exception:
        pass
    return default


def _cache_path(dandiset, n_ch, max_samples):
    h = hashlib.sha1(f"{dandiset}|{n_ch}|{max_samples}".encode()).hexdigest()[:16]
    return os.path.join(_CACHE_DIR, f"{dandiset}_{h}.npz")


def _build(raw, fs, label, win_s, step_s, n_ch, target_fs=2.0):
    # decimate optical rate toward ~target_fs (hemodynamic content is slow)
    decim = max(1, int(round(fs / target_fs)))
    if decim > 1:
        raw = raw[:, ::decim]
        fs = fs / decim
    raw = (raw - raw.mean(1, keepdims=True)) / (raw.std(1, keepdims=True) + 1e-9)
    n = raw.shape[1]
    starts, w = window_grid(n, fs, win_s, step_s)
    if len(starts) < 40 or raw.shape[0] < 4:
        return None
    a = raw.shape[0] // 2
    return {
        "sig": raw, "fs": float(fs), "H": None, "starts": starts, "w": w,
        "groupA": list(range(a)), "groupB": list(range(a, raw.shape[0])),
        "n_states": 3, "source": "dandi-neurovascular",
        "modality": "optical-neurovascular(live)",
        "label": f"DANDI:{label}",
    }


def load_dandi_neurovascular(dandiset, n_ch=8, max_samples=12000,
                             win_s=120.0, step_s=8.0):
    cpath = _cache_path(dandiset, n_ch, max_samples)
    if os.path.exists(cpath):
        try:
            z = np.load(cpath, allow_pickle=False)
            return _build(z["raw"].astype(float), float(z["fs"]),
                          str(z["label_name"]), win_s, step_s, n_ch)
        except Exception as e:
            print(f"[data_live] cache read failed ({type(e).__name__}); restreaming")
    try:
        from dandi.dandiapi import DandiAPIClient
        import remfile
        import h5py
        with DandiAPIClient() as client:
            ds = client.get_dandiset(dandiset, "draft")
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
        dset = _find_2d(h5)
        if dset is None:
            return None
        fs = _rate_for(h5, dset, default=10.0)
        if dset.shape[0] >= dset.shape[1]:        # (time, roi)
            nsamp = min(max_samples, dset.shape[0])
            nc = min(n_ch, dset.shape[1])
            raw = np.asarray(dset[:nsamp, :nc], dtype=float).T
        else:                                      # (roi, time)
            nsamp = min(max_samples, dset.shape[1])
            nc = min(n_ch, dset.shape[0])
            raw = np.asarray(dset[:nc, :nsamp], dtype=float)
        label = asset.path.split("/")[-1]
        try:
            os.makedirs(_CACHE_DIR, exist_ok=True)
            np.savez_compressed(cpath, raw=raw, fs=float(fs), label_name=label)
        except Exception as e:
            print(f"[data_live] cache write failed ({type(e).__name__}); continuing")
        return _build(raw, float(fs), label, win_s, step_s, n_ch)
    except Exception as e:
        print(f"[data_live] {dandiset} failed: {type(e).__name__}: {e}")
        return None


def load_first_available(max_sources=1, **kw):
    out = []
    for ds, _ in CANDIDATES:
        if len(out) >= max_sources:
            break
        d = load_dandi_neurovascular(ds, **kw)
        if d is not None:
            print(f"[data_live] loaded {d['label']} "
                  f"({d['sig'].shape[0]} ch x {d['sig'].shape[1]} samp @ {d['fs']:.2f}Hz, "
                  f"{len(d['starts'])} windows)")
            out.append(d)
    return out
