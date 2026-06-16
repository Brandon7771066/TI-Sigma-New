"""Self-contained signal-feature formulas reused from the TI Sigma corpus.

Ported (not imported) to keep the benchmark free of project modules that
trigger network/API calls on import. Formulas match:
  - gamma_plv / theta-delta E / spectral_entropy : analyses/pass77_b4 + pass77_b67
  - lcc_resonance (Gaussian-weighted max-lag)     : ai_corpus_lcc_test.py / ti_lcc_virus_full.py
"""
import numpy as np
from scipy.signal import welch, butter, sosfiltfilt, hilbert

PHI = (1.0 + 5.0 ** 0.5) / 2.0
C_EMERICK = 1.0 / (PHI * (2.0 ** 0.5))  # 1/(phi*sqrt2) ~ 0.4370

BANDS = {
    "delta": (1.0, 4.0),
    "theta": (4.0, 8.0),
    "alpha": (8.0, 13.0),
    "beta": (13.0, 30.0),
    "gamma": (30.0, 80.0),
}


def bandpass(x, fs, lo, hi, order=4):
    nyq = fs / 2.0
    hi = min(hi, nyq * 0.99)
    sos = butter(order, [lo, hi], btype="band", fs=fs, output="sos")
    return sosfiltfilt(sos, x)


def bandpower(x, fs, lo, hi):
    nper = int(min(len(x), max(64, fs * 1.0)))
    f, P = welch(x, fs=fs, nperseg=nper)
    m = (f >= lo) & (f <= hi)
    if not np.any(m):
        return 0.0
    return float(np.trapezoid(P[m], f[m]))


def band_features(x, fs):
    return np.array([bandpower(x, fs, lo, hi) for (lo, hi) in BANDS.values()])


def gamma_plv(x1, x2, fs, lo=30.0, hi=80.0):
    p1 = np.angle(hilbert(bandpass(x1, fs, lo, hi)))
    p2 = np.angle(hilbert(bandpass(x2, fs, lo, hi)))
    return float(np.abs(np.mean(np.exp(1j * (p1 - p2)))))


def theta_delta_E(x, fs):
    theta = bandpower(x, fs, 6.0, 10.0)
    delta = bandpower(x, fs, 1.0, 4.0)
    return float(min(1.0, (theta / (delta + 1e-12)) / 3.0))


def spectral_entropy(x, fs, lo=1.0, hi=100.0):
    f = np.fft.rfftfreq(len(x), 1.0 / fs)
    P = np.abs(np.fft.rfft(x)) ** 2
    m = (f >= lo) & (f <= hi)
    P = P[m]
    if P.size == 0 or P.sum() <= 0:
        return 0.0
    p = P / P.sum()
    return float(-np.sum(p * np.log2(p + 1e-12)) / np.log2(len(p) + 1e-12))


def theta_gamma_pac(x, fs, ph_band=(4.0, 8.0), amp_band=(30.0, 80.0)):
    """Mean-vector-length phase-amplitude coupling (Canolty-style)."""
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


def window_grid(n_samples, fs, win_s=2.0, step_s=1.0):
    w = int(win_s * fs)
    s = int(step_s * fs)
    starts = list(range(0, n_samples - w + 1, s))
    return starts, w


def _band_features_welch(x, fs):
    """All 5 band powers from a single Welch PSD (faster than 5 calls)."""
    nper = int(min(len(x), max(64, fs * 1.0)))
    f, P = welch(x, fs=fs, nperseg=nper)
    out = []
    for (lo, hi) in BANDS.values():
        m = (f >= lo) & (f <= hi)
        out.append(float(np.trapezoid(P[m], f[m])) if np.any(m) else 0.0)
    return np.array(out)


def _sos(fs, lo, hi, order=4):
    nyq = fs / 2.0
    hi = min(hi, nyq * 0.99)
    return butter(order, [lo, hi], btype="band", fs=fs, output="sos")


def _window_feat_from_block(sig, fs, chans, st, w, b0, b1, tph, gam, gph, pairs):
    """Feature row for one window, using block-local analytic signals (offset b0)
    and block-capped raw slices (no read past b1)."""
    end = min(st + w, b1)
    feat = []
    for c in chans:
        raw = sig[c][st:end]
        bp = np.log1p(_band_features_welch(raw, fs))
        se = spectral_entropy(raw, fs)
        lo, hi = st - b0, end - b0
        am = gam[c][lo:hi]
        ph = tph[c][lo:hi]
        pac = float(np.abs(np.mean(am * np.exp(1j * ph))) / (np.mean(am) + 1e-12))
        feat.extend(list(bp) + [se, pac])
    if pairs:
        plv = np.mean([
            np.abs(np.mean(np.exp(1j * (gph[i][st - b0:end - b0] - gph[j][st - b0:end - b0]))))
            for (i, j) in pairs
        ])
    else:
        plv = 0.0
    feat.append(float(plv))
    return feat


def window_features(sig, fs, chans, starts, w, split_sample=None):
    """Per-window feature matrix for the OBSERVED channel set.

    Per channel: 5 log band-powers + spectral entropy + theta-gamma PAC (=7).
    Plus 1 global feature: mean gamma-PLV across observed channel pairs.
    Returns X with shape (n_windows, 7*len(chans) + 1).

    LEAKAGE-SAFE: the theta/gamma bandpass + Hilbert analytic signals are computed
    independently for the TRAIN block [0, split_sample) and the TEST block
    [split_sample, end). No filtering spans the split boundary, so no future
    (test) sample can influence a train-window feature or vice versa. When
    split_sample is None the whole signal is one block (used where there is no
    split). Filter coefficients are computed once and reused.
    """
    sos_t = _sos(fs, 4.0, 8.0)
    sos_g = _sos(fs, 30.0, 80.0)
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
        tph, gam, gph = {}, {}, {}
        for c in chans:
            seg = sig[c][b0:b1]
            tph[c] = np.angle(hilbert(sosfiltfilt(sos_t, seg)))
            ga = hilbert(sosfiltfilt(sos_g, seg))
            gam[c] = np.abs(ga)
            gph[c] = np.angle(ga)
        for st in bstarts:
            feat_by_start[st] = _window_feat_from_block(
                sig, fs, chans, st, w, b0, b1, tph, gam, gph, pairs)
    return np.asarray([feat_by_start[s] for s in starts], dtype=float)


def passive_resonance_feature(sig, fs, chans, starts, w, split_sample=None):
    """Scalar 'are-we-coupled' readout per window = mean |LCC| of observed
    channels to a fixed reference oscillator (the passive baseline's only input).
    """
    out = []
    t_full = np.arange(sig.shape[1]) / fs
    ref_full = np.sin(2 * np.pi * 6.0 * t_full)  # fixed theta probe
    n = sig.shape[1]
    for st in starts:
        # LEAKAGE-SAFE: a train-side window (start < split_sample) is capped at the
        # split boundary so its resonance never reads test-region samples.
        if split_sample is not None and st < split_sample:
            end = min(st + w, split_sample)
        else:
            end = min(st + w, n)
        sl = slice(st, end)
        ref = ref_full[sl]
        vals = [abs(lcc_resonance(sig[c][sl], ref, sigma=5.0, max_lag=8)) for c in chans]
        out.append(float(np.mean(vals)))
    return np.asarray(out, dtype=float).reshape(-1, 1)
