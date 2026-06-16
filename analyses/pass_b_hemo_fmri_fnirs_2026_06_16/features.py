"""Hemodynamic signal-feature formulas (fMRI-BOLD + fNIRS adaptation).

Modality port of analyses/pass_b_consciousness_hamiltonian_2026_06_16/features.py.
The ELECTROPHYSIOLOGY band-plan (delta..gamma, 1-80 Hz) is meaningless for
hemodynamics: BOLD lives at ~0.01-0.1 Hz and fNIRS neuronal hemodynamics at
~0.01-0.15 Hz. We therefore swap to a single low-frequency hemodynamic band-plan
that is valid for BOTH modalities (fMRI fs~1 Hz, fNIRS fs~10 Hz both contain it),
and replace theta-gamma phase-amplitude coupling (the LFP-specific cross-frequency
primitive) with an INFRASLOW cross-frequency coupling (slow-phase -> faster-amp)
analog, which is the faithful hemodynamic counterpart.

Everything else (window grid, leakage-safe block filtering, spectral entropy,
Gaussian-weighted LCC resonance) is timescale-agnostic and reused unchanged.
"""
import numpy as np
from scipy.signal import welch, butter, sosfiltfilt, hilbert

PHI = (1.0 + 5.0 ** 0.5) / 2.0
C_EMERICK = 1.0 / (PHI * (2.0 ** 0.5))  # 1/(phi*sqrt2) ~ 0.4370

# Hemodynamic band-plan (Hz) — valid for fMRI BOLD (Nyquist 0.5 Hz @ TR=1s) and
# fNIRS (Nyquist 5 Hz @ 10 Hz). Mirrors Zuo et al. slow-5/slow-4/slow-3 splits.
BANDS = {
    "slow5": (0.015, 0.04),    # infraslow
    "slow4": (0.04, 0.08),     # canonical resting-state BOLD band
    "slow3": (0.08, 0.15),     # fast hemodynamic / Mayer-adjacent
}
# infraslow cross-frequency coupling bands (hemodynamic PAC analog)
CFC_PHASE = (0.015, 0.04)
CFC_AMP = (0.08, 0.15)
REF_HZ = 0.03                  # fixed slow probe for the passive-resonance readout
SE_LO, SE_HI = 0.01, 0.2       # spectral-entropy support


def bandpass(x, fs, lo, hi, order=4):
    nyq = fs / 2.0
    hi = min(hi, nyq * 0.99)
    lo = max(lo, 1e-4)
    sos = butter(order, [lo, hi], btype="band", fs=fs, output="sos")
    n = len(x)
    # short truncated boundary windows (leakage-parity truncation at the split)
    # degrade gracefully rather than crash sosfiltfilt's padlen check.
    if n < 12:
        return np.zeros_like(x, dtype=float)
    try:
        return sosfiltfilt(sos, x)
    except ValueError:
        return sosfiltfilt(sos, x, padlen=n - 1)


def bandpower(x, fs, lo, hi):
    nper = int(min(len(x), max(64, len(x))))
    f, P = welch(x, fs=fs, nperseg=nper)
    m = (f >= lo) & (f <= hi)
    if not np.any(m):
        return 0.0
    return float(np.trapezoid(P[m], f[m]))


def band_features(x, fs):
    return np.array([bandpower(x, fs, lo, hi) for (lo, hi) in BANDS.values()])


def lowfreq_plv(x1, x2, fs, lo=CFC_PHASE[0], hi=CFC_AMP[1]):
    """Phase-locking value in the hemodynamic band (replaces gamma-PLV)."""
    p1 = np.angle(hilbert(bandpass(x1, fs, lo, hi)))
    p2 = np.angle(hilbert(bandpass(x2, fs, lo, hi)))
    return float(np.abs(np.mean(np.exp(1j * (p1 - p2)))))


def spectral_entropy(x, fs, lo=SE_LO, hi=SE_HI):
    f = np.fft.rfftfreq(len(x), 1.0 / fs)
    P = np.abs(np.fft.rfft(x)) ** 2
    m = (f >= lo) & (f <= hi)
    P = P[m]
    if P.size == 0 or P.sum() <= 0:
        return 0.0
    p = P / P.sum()
    return float(-np.sum(p * np.log2(p + 1e-12)) / np.log2(len(p) + 1e-12))


def hemo_cfc(x, fs, ph_band=CFC_PHASE, amp_band=CFC_AMP):
    """Infraslow cross-frequency coupling = mean-vector-length PAC analog
    (slow-phase modulates faster-hemodynamic amplitude). Hemodynamic counterpart
    of theta-gamma PAC; the cross-frequency coupling primitive carried over."""
    ph = np.angle(hilbert(bandpass(x, fs, *ph_band)))
    amp = np.abs(hilbert(bandpass(x, fs, *amp_band)))
    mvl = np.abs(np.mean(amp * np.exp(1j * ph))) / (np.mean(amp) + 1e-12)
    return float(mvl)


def lcc_resonance(a, b, sigma=5.0, max_lag=15):
    """Gaussian-weighted, sign-preserving max-lag correlation (LCC Form B)."""
    a = (a - a.mean()) / (a.std() + 1e-12)
    b = (b - b.mean()) / (b.std() + 1e-12)
    n = len(a)
    best = 0.0
    for tau in range(-max_lag, max_lag + 1):
        if tau >= 0:
            x, y = a[tau:], b[: n - tau]
        else:
            x, y = a[: n + tau], b[-tau:]
        if len(x) < 8:
            continue
        rho = np.corrcoef(x, y)[0, 1]
        if not np.isfinite(rho):
            continue
        v = rho * np.exp(-(tau ** 2) / (2.0 * sigma ** 2))
        if abs(v) > abs(best):
            best = float(v)
    return best


def window_grid(n_samples, fs, win_s=128.0, step_s=8.0):
    w = int(win_s * fs)
    s = int(step_s * fs)
    starts = list(range(0, n_samples - w + 1, s))
    return starts, w


def _band_features_welch(x, fs):
    """All band powers from a single Welch PSD. nperseg = full window so the
    infraslow bands (period up to ~67 s) are actually resolvable."""
    nper = int(len(x))
    f, P = welch(x, fs=fs, nperseg=nper)
    out = []
    for (lo, hi) in BANDS.values():
        m = (f >= lo) & (f <= hi)
        out.append(float(np.trapezoid(P[m], f[m])) if np.any(m) else 0.0)
    return np.array(out)


def _sos(fs, lo, hi, order=4):
    nyq = fs / 2.0
    hi = min(hi, nyq * 0.99)
    lo = max(lo, 1e-4)
    return butter(order, [lo, hi], btype="band", fs=fs, output="sos")


def _window_feat_from_block(sig, fs, chans, st, w, b0, b1, cph, camp, pph, pairs):
    """Feature row for one window, using block-local analytic signals (offset b0)
    and block-capped raw slices (no read past b1)."""
    end = min(st + w, b1)
    feat = []
    for c in chans:
        raw = sig[c][st:end]
        bp = np.log1p(_band_features_welch(raw, fs))
        se = spectral_entropy(raw, fs)
        lo, hi = st - b0, end - b0
        am = camp[c][lo:hi]
        ph = cph[c][lo:hi]
        cfc = float(np.abs(np.mean(am * np.exp(1j * ph))) / (np.mean(am) + 1e-12))
        feat.extend(list(bp) + [se, cfc])
    if pairs:
        plv = np.mean([
            np.abs(np.mean(np.exp(1j * (pph[i][st - b0:end - b0] - pph[j][st - b0:end - b0]))))
            for (i, j) in pairs
        ])
    else:
        plv = 0.0
    feat.append(float(plv))
    return feat


def window_features(sig, fs, chans, starts, w, split_sample=None):
    """Per-window feature matrix for the OBSERVED channel set.

    Per channel: 3 log hemodynamic band-powers + spectral entropy + infraslow
    CFC (=5). Plus 1 global feature: mean low-frequency PLV across observed
    channel pairs. Returns X with shape (n_windows, 5*len(chans) + 1).

    LEAKAGE-SAFE: bandpass + Hilbert analytic signals are computed independently
    for the TRAIN block [0, split_sample) and the TEST block [split_sample, end);
    no filtering spans the split boundary. Filter coefficients computed once.
    """
    sos_p = _sos(fs, *CFC_PHASE)          # phase band (slow)
    sos_a = _sos(fs, *CFC_AMP)            # amplitude band (faster hemo)
    sos_w = _sos(fs, CFC_PHASE[0], CFC_AMP[1])   # whole-band for PLV
    pairs = [(chans[i], chans[j]) for i in range(len(chans)) for j in range(i + 1, len(chans))]
    pairs = pairs[:6]
    n = sig.shape[1]

    if split_sample is None:
        blocks = [(0, n, list(starts))]
    else:
        tr = [s for s in starts if s < split_sample]
        te = [s for s in starts if s >= split_sample]
        blocks = [(0, split_sample, tr), (split_sample, n, te)]

    feat_by_start = {}
    for (b0, b1, bstarts) in blocks:
        if not bstarts:
            continue
        cph, camp, pph = {}, {}, {}
        for c in chans:
            seg = sig[c][b0:b1]
            cph[c] = np.angle(hilbert(sosfiltfilt(sos_p, seg)))
            camp[c] = np.abs(hilbert(sosfiltfilt(sos_a, seg)))
            pph[c] = np.angle(hilbert(sosfiltfilt(sos_w, seg)))
        for st in bstarts:
            feat_by_start[st] = _window_feat_from_block(
                sig, fs, chans, st, w, b0, b1, cph, camp, pph, pairs)
    return np.asarray([feat_by_start[s] for s in starts], dtype=float)


def passive_resonance_feature(sig, fs, chans, starts, w, split_sample=None):
    """Scalar 'are-we-coupled' readout per window = mean |LCC| of observed
    channels to a fixed slow reference oscillator (REF_HZ)."""
    out = []
    t_full = np.arange(sig.shape[1]) / fs
    ref_full = np.sin(2 * np.pi * REF_HZ * t_full)   # fixed infraslow probe
    n = sig.shape[1]
    for st in starts:
        if split_sample is not None and st < split_sample:
            end = min(st + w, split_sample)
        else:
            end = min(st + w, n)
        sl = slice(st, end)
        ref = ref_full[sl]
        vals = [abs(lcc_resonance(sig[c][sl], ref, sigma=5.0, max_lag=8)) for c in chans]
        out.append(float(np.mean(vals)))
    return np.asarray(out, dtype=float).reshape(-1, 1)
