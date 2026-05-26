"""ETM-1 v2 (Enlightenment-Triggering Music) Phase-2 MIR feature extractor.

Reads audio file(s) -> writes <stem>.etm.json with 9-feature ETM-1 v2 scores.

Per Pass-77-B7 §5.3 graceful-fallback design:
  - Features extractable on scipy-only run normally.
  - Features requiring librosa return {"status": "BLOCKED_NEEDS_LIBROSA"} if librosa is unavailable.

Run:
    python extract_etm_features.py audio/song1.wav audio/song2.mp3 ...

Output: writes one <stem>.etm.json per input file in the same dir.

Honest #69: Phase-2 extractor is scaffolding-ready, NOT yet validated on real audio.
Validation = comparison of MIR-extracted scores to expected_phase1_baseline.json
via compare_to_baseline.py (created at-runtime when audio arrives).
"""
from __future__ import annotations
import json, sys, os, traceback
from pathlib import Path

import numpy as np
import scipy.signal as sps
import scipy.io.wavfile as wavfile

try:
    import librosa
    LIBROSA_AVAILABLE = True
except ImportError:
    LIBROSA_AVAILABLE = False

BLOCKED = {"status": "BLOCKED_NEEDS_LIBROSA"}


def _load_audio(path: Path):
    """Returns (samples, sample_rate). Mono-mixdown if multi-channel."""
    if LIBROSA_AVAILABLE:
        y, sr = librosa.load(str(path), sr=None, mono=True)
        return y.astype(np.float32), int(sr)
    # scipy fallback: WAV only
    if path.suffix.lower() != ".wav":
        raise RuntimeError(
            f"scipy-only fallback requires WAV input; got {path.suffix}. "
            "Install librosa (Brandon-blocked: pyproject github==1.2.6 stale dep)."
        )
    sr, y = wavfile.read(str(path))
    if y.ndim > 1:
        y = y.mean(axis=1)
    y = y.astype(np.float32)
    peak = float(np.max(np.abs(y))) or 1.0
    y = y / peak
    return y, int(sr)


# ---------- Feature extractors ----------

def feat_DAM(y, sr):
    """Dynamic Arc Magnitude — RMS-envelope range in dB, normalized to [0,1] via /60dB."""
    frame = int(0.05 * sr)  # 50ms
    hop = int(0.025 * sr)
    n = (len(y) - frame) // hop
    if n <= 0:
        return {"value": 0.0, "raw_dB_range": 0.0, "n_frames": 0}
    rms = np.array([
        np.sqrt(np.mean(y[i*hop : i*hop + frame] ** 2)) for i in range(n)
    ])
    rms = np.maximum(rms, 1e-7)
    db = 20.0 * np.log10(rms)
    rng_db = float(db.max() - db.min())
    val = float(min(rng_db / 60.0, 1.0))
    return {"value": val, "raw_dB_range": rng_db, "n_frames": n}


def feat_SFD(y, sr):
    """Spectral Fusion Density — 1 - mean(spectral_flatness)."""
    if LIBROSA_AVAILABLE:
        flat = librosa.feature.spectral_flatness(y=y)[0]
        sfd = float(1.0 - np.mean(flat))
        return {"value": max(0.0, min(1.0, sfd)), "mean_flatness": float(np.mean(flat))}
    # scipy-partial: geometric/arithmetic mean of magnitude spectrum
    f, _, S = sps.spectrogram(y, fs=sr, nperseg=2048, noverlap=1024)
    mag = np.abs(S) + 1e-10
    gm = np.exp(np.mean(np.log(mag), axis=0))
    am = np.mean(mag, axis=0)
    flat = gm / am
    sfd = float(1.0 - np.mean(flat))
    return {"value": max(0.0, min(1.0, sfd)), "mean_flatness": float(np.mean(flat)),
            "note": "scipy-fallback (less accurate than librosa)"}


def feat_MCC(y, sr, segment_seconds: float = 15.0):
    """Motif Circularity Closure — spectrogram-DTW similarity of opening vs closing N seconds."""
    seg = int(segment_seconds * sr)
    if len(y) < 2 * seg + sr:
        return {"value": 0.0, "note": "audio too short", "segment_seconds": segment_seconds}
    head = y[:seg]
    tail = y[-seg:]
    # Spectrogram-based similarity (cosine on mean-spectrum)
    f, _, Sh = sps.spectrogram(head, fs=sr, nperseg=1024, noverlap=512)
    _, _, St = sps.spectrogram(tail, fs=sr, nperseg=1024, noverlap=512)
    mh = np.mean(np.abs(Sh), axis=1)
    mt = np.mean(np.abs(St), axis=1)
    cos = float(np.dot(mh, mt) / (np.linalg.norm(mh) * np.linalg.norm(mt) + 1e-10))
    return {"value": max(0.0, min(1.0, cos)), "segment_seconds": segment_seconds,
            "method": "mean-spectrum cosine (DTW preferred when librosa available)"}


def feat_TRD(y, sr):
    """Tension-Resolution Depth — Sethares-roughness curve range/std."""
    if not LIBROSA_AVAILABLE:
        # scipy partial: spectral-bandwidth variance as roughness proxy
        f, _, S = sps.spectrogram(y, fs=sr, nperseg=2048, noverlap=1024)
        mag = np.abs(S)
        centroid = np.sum(mag * f[:, None], axis=0) / (np.sum(mag, axis=0) + 1e-10)
        bw = np.sqrt(np.sum(mag * (f[:, None] - centroid) ** 2, axis=0) / (np.sum(mag, axis=0) + 1e-10))
        rng = float(np.percentile(bw, 95) - np.percentile(bw, 5))
        val = float(min(rng / 2000.0, 1.0))
        return {"value": val, "method": "scipy bandwidth-range proxy", "note": "PARTIAL — Sethares roughness preferred"}
    # librosa-full would use spectral-contrast + custom Sethares; placeholder:
    sc = librosa.feature.spectral_contrast(y=y, sr=sr)
    rng = float(np.percentile(sc, 95) - np.percentile(sc, 5))
    val = float(min(rng / 40.0, 1.0))
    return {"value": val, "method": "librosa spectral_contrast range"}


def feat_HS(y, sr):
    if not LIBROSA_AVAILABLE:
        return BLOCKED
    chroma = librosa.feature.chroma_cqt(y=y, sr=sr)
    # Bayesian surprise proxy = sum of squared first-difference of chromagram
    d = np.diff(chroma, axis=1)
    surprise = float(np.mean(d * d))
    val = float(min(surprise * 100.0, 1.0))
    return {"value": val, "method": "chroma first-difference variance"}


def feat_LBS(y, sr):
    if not LIBROSA_AVAILABLE:
        return BLOCKED
    # Bass-band isolation + pYIN on bass region
    f0, voiced_flag, _ = librosa.pyin(y, fmin=40, fmax=200, sr=sr)
    f0 = f0[~np.isnan(f0)]
    if len(f0) < 8:
        return {"value": 0.0, "note": "insufficient bass-voiced frames"}
    # Detect descending stepwise runs >= 4 notes
    diffs = np.diff(f0)
    desc_run = max_desc_run = 0
    for d in diffs:
        if d < 0:
            desc_run += 1
            max_desc_run = max(max_desc_run, desc_run)
        else:
            desc_run = 0
    val = float(min(max_desc_run / 16.0, 1.0))
    return {"value": val, "max_descending_run_frames": int(max_desc_run)}


def feat_AKM(y, sr):
    if not LIBROSA_AVAILABLE:
        return BLOCKED
    # Segment-wise chroma + Krumhansl-Schmuckler key detection (simplified)
    chroma = librosa.feature.chroma_cqt(y=y, sr=sr)
    seg_n = chroma.shape[1] // 8  # 8 segments
    if seg_n < 1:
        return {"value": 0.0, "note": "audio too short"}
    keys = []
    major_profile = np.array([6.35,2.23,3.48,2.33,4.38,4.09,2.52,5.19,2.39,3.66,2.29,2.88])
    for i in range(8):
        seg = chroma[:, i*seg_n:(i+1)*seg_n].mean(axis=1)
        corrs = [np.corrcoef(np.roll(major_profile, -k), seg)[0,1] for k in range(12)]
        keys.append(int(np.argmax(corrs)))
    ascents = sum(1 for a, b in zip(keys, keys[1:]) if ((b - a) % 12) in (1, 2, 5, 7))
    val = float(min(ascents / 4.0, 1.0))
    return {"value": val, "key_sequence": keys, "ascending_modulation_count": int(ascents)}


def feat_RRF(y, sr):
    if not LIBROSA_AVAILABLE:
        return BLOCKED
    tempo, beats = librosa.beat.beat_track(y=y, sr=sr)
    if len(beats) < 4:
        return {"value": 0.0, "note": "insufficient beats"}
    intervals = np.diff(librosa.frames_to_time(beats, sr=sr))
    rrf = float(np.std(intervals) / (np.mean(intervals) + 1e-10))
    val = float(np.tanh(rrf * 5.0))
    return {"value": val, "tempo": float(tempo) if hasattr(tempo, '__float__') else float(tempo[0]),
            "interval_std": float(np.std(intervals)), "interval_mean": float(np.mean(intervals))}


def feat_VPS(y, sr):
    """VPS composite: mean of 6 sub-features."""
    subs = {}

    # VSF — spectral flatness in vocal band (partial without librosa)
    f, _, S = sps.spectrogram(y, fs=sr, nperseg=2048, noverlap=1024)
    vocal_mask = (f >= 200) & (f <= 3500)
    if vocal_mask.any():
        vmag = np.abs(S[vocal_mask, :]) + 1e-10
        gm = np.exp(np.mean(np.log(vmag), axis=0))
        am = np.mean(vmag, axis=0)
        vsf = float(1.0 - np.mean(gm / am))
    else:
        vsf = 0.0
    subs["VSF"] = {"value": max(0.0, min(1.0, vsf)), "method": "vocal-band-flatness inverted"}

    # LTS — needs librosa pyin
    if LIBROSA_AVAILABLE:
        f0, voiced_flag, _ = librosa.pyin(y, fmin=80, fmax=900, sr=sr)
        f0 = f0[~np.isnan(f0)]
        if len(f0) > 16:
            uq = float(np.percentile(f0, 75))
            # Normalize 130-525 Hz range
            lts = float(min(max((uq - 130.0) / 400.0, 0.0), 1.0))
            subs["LTS"] = {"value": lts, "upper_quartile_Hz": uq, "n_voiced_frames": int(len(f0))}
        else:
            subs["LTS"] = {"value": 0.0, "note": "insufficient voiced frames"}
    else:
        subs["LTS"] = BLOCKED

    # VCM — spectral-centroid trajectory mean-shift
    centroid = np.sum(np.abs(S) * f[:, None], axis=0) / (np.sum(np.abs(S), axis=0) + 1e-10)
    if len(centroid) >= 8:
        thirds = np.array_split(centroid, 3)
        means = [float(np.mean(t)) for t in thirds]
        rng = float(max(means) - min(means))
        vcm = float(min(rng / 1000.0, 1.0))
        subs["VCM"] = {"value": vcm, "centroid_means_by_third": means}
    else:
        subs["VCM"] = {"value": 0.0, "note": "audio too short"}

    # GMP — spectral kurtosis at energy peaks
    rms = np.array([np.sqrt(np.mean(y[i:i+2048]**2)) for i in range(0, len(y)-2048, 1024)])
    if len(rms) >= 10:
        peak_thresh = float(np.percentile(rms, 90))
        peak_idx = [i for i, r in enumerate(rms) if r >= peak_thresh]
        kurts = []
        for i in peak_idx[:50]:
            seg = y[i*1024 : i*1024 + 2048]
            spec = np.abs(np.fft.rfft(seg)) + 1e-10
            m = np.mean(spec); s = np.std(spec)
            if s > 1e-9:
                k = float(np.mean(((spec - m) / s) ** 4)) - 3.0
                kurts.append(k)
        if kurts:
            grit = float(np.tanh(np.mean(kurts) / 10.0))
            subs["GMP"] = {"value": max(0.0, min(1.0, grit)),
                           "method": "scipy spectral-kurtosis at peaks",
                           "note": "PARTIAL — melisma-component needs librosa" if not LIBROSA_AVAILABLE else None}
        else:
            subs["GMP"] = {"value": 0.0, "note": "no valid peak segments"}
    else:
        subs["GMP"] = {"value": 0.0, "note": "audio too short"}

    # TEI — RMS-mean comparison final-third vs middle-third
    n3 = len(y) // 3
    if n3 > sr:
        mid_rms = float(np.sqrt(np.mean(y[n3:2*n3] ** 2)))
        end_rms = float(np.sqrt(np.mean(y[2*n3:] ** 2)))
        ratio = end_rms / (mid_rms + 1e-10)
        tei = float(min(max((ratio - 1.0) / 0.5, 0.0), 1.0))
        subs["TEI"] = {"value": tei, "end_to_mid_rms_ratio": ratio,
                       "note": "RMS-only; repetition-detection needs librosa" if not LIBROSA_AVAILABLE else None}
    else:
        subs["TEI"] = {"value": 0.0, "note": "audio too short"}

    # CRA — voice-activity-detection alternation (partial without librosa)
    rms_db = 20.0 * np.log10(rms + 1e-7) if len(rms) else np.array([])
    if len(rms_db) >= 20:
        thresh = float(np.percentile(rms_db, 40))
        active = rms_db > thresh
        transitions = int(np.sum(active[1:] != active[:-1]))
        cra = float(min(transitions / 40.0, 1.0))
        subs["CRA"] = {"value": cra, "voice_transitions": transitions}
    else:
        subs["CRA"] = {"value": 0.0, "note": "audio too short"}

    valid_vals = [s["value"] for s in subs.values() if isinstance(s, dict) and "value" in s and s.get("status") != "BLOCKED_NEEDS_LIBROSA"]
    vps_aggregate = float(np.mean(valid_vals)) if valid_vals else 0.0
    return {"value": vps_aggregate, "n_subfeatures_extracted": len(valid_vals), "sub_features": subs}


# ---------- Pipeline ----------

FEATURE_FUNCS = {
    "TRD": feat_TRD, "HS": feat_HS, "DAM": feat_DAM, "SFD": feat_SFD,
    "LBS": feat_LBS, "AKM": feat_AKM, "MCC": feat_MCC, "RRF": feat_RRF,
    "VPS": feat_VPS,
}


def extract_etm(path: Path) -> dict:
    out = {
        "audio_file": str(path),
        "schema_version": "1.0-Pass77B7-2026-05-26",
        "librosa_available": LIBROSA_AVAILABLE,
        "features": {},
    }
    try:
        y, sr = _load_audio(path)
        out["duration_seconds"] = float(len(y) / sr)
        out["sample_rate"] = sr
    except Exception as e:
        out["error"] = f"audio-load: {e!r}"
        out["aggregate_etm_v2"] = None
        return out

    feat_values = []
    for name, fn in FEATURE_FUNCS.items():
        try:
            res = fn(y, sr)
            out["features"][name] = res
            if isinstance(res, dict) and "value" in res:
                feat_values.append(res["value"])
        except Exception as e:
            out["features"][name] = {"error": repr(e), "trace": traceback.format_exc(limit=2)}

    if feat_values:
        out["aggregate_etm_v2"] = float(np.mean(feat_values))
        out["n_features_extracted"] = len(feat_values)
        out["transformational_grade"] = bool(out["aggregate_etm_v2"] >= 0.65)
    else:
        out["aggregate_etm_v2"] = None
    return out


def main(argv):
    if len(argv) < 2:
        print("Usage: python extract_etm_features.py <audio_file> [<audio_file> ...]", file=sys.stderr)
        sys.exit(2)
    files = [Path(a) for a in argv[1:]]
    for f in files:
        if not f.exists():
            print(f"SKIP (not found): {f}", file=sys.stderr)
            continue
        print(f"Extracting ETM-1 v2 features for: {f.name}")
        result = extract_etm(f)
        out_path = f.with_suffix(f.suffix + ".etm.json")
        with open(out_path, "w") as h:
            json.dump(result, h, indent=2)
        agg = result.get("aggregate_etm_v2")
        agg_str = f"{agg:.3f}" if agg is not None else "N/A"
        print(f"  -> {out_path.name}  ETM_v2={agg_str}  librosa={LIBROSA_AVAILABLE}")


if __name__ == "__main__":
    main(sys.argv)
