"""Consciousness-Hamiltonian feature extractor — HEMODYNAMIC port.

Modality adaptation of analyses/pass_b_consciousness_hamiltonian_2026_06_16/
ch_features.py. Per-window GILE-HEM (8-D, canonical formulas) -> ring weights ->
H_TSC spectrum features + FULL PD block + GILE-graph block.

Only the band-plan and the coupling (Love) primitive change for hemodynamics:
the 5 EEG bands -> 3 hemodynamic bands; theta-gamma PAC -> infraslow CFC. The
GILE-HEM definitions (coherence stability, spectral entropy/purity, amplitude
stability, contradiction ratio) are timescale-agnostic and unchanged.
"""
import numpy as np

from tsc_hamiltonian import (
    gile_composite, pd_full, pd_zone, hamiltonian_spectrum_features,
    gile_graph_fiedler, ET,
)
from features import hemo_cfc, BANDS

CH_FEATURE_NAMES = [
    "G", "I", "L", "E", "D1", "D2", "D3", "D4",
    "gile_comp", "hem_score", "pd_real", "pd_imag", "pd_zone",
    "lambda0", "gap", "lam_mean", "lam_std", "bandwidth",
    "ground_ipr", "ring_entropy", "dom_ring", "fiedler", "edge_density",
]

_BANDS = list(BANDS.values())          # 3 hemodynamic bands


def _zscore_clip(x):
    s = x.std()
    if s < 1e-9:
        return np.zeros_like(x)
    return np.clip((x - x.mean()) / (3.0 * s), -1.0, 1.0)


def _coherence(seg_ch):
    """LCC coherence = 1 - fraction in Tralse zone |tb|<=ET."""
    tb = _zscore_clip(seg_ch)
    return 1.0 - float(np.mean(np.abs(tb) <= ET))


def _spectrum(seg_ch, fs):
    n = seg_ch.shape[0]
    x = seg_ch - seg_ch.mean()
    win = np.hanning(n)
    P = np.abs(np.fft.rfft(x * win)) ** 2
    f = np.fft.rfftfreq(n, d=1.0 / fs)
    return f, P


def _spectral_entropy(P):
    p = P[1:]
    s = p.sum()
    if s < 1e-12:
        return 0.0
    p = p / s
    H = -(p * np.log(p + 1e-12)).sum()
    return float(H / np.log(len(p) + 1e-12))


def _spectral_purity(f, P):
    p = P.copy()
    p[0] = 0.0
    s = p.sum()
    if s < 1e-12:
        return 0.0
    return float(p.max() / s)


def gile_hem_from_window(seg, fs, n_sub=4):
    """seg : (n_ch, w) slice of observed channels. Returns the 8-D GILE-HEM dict."""
    n_ch, w = seg.shape
    sub = max(8, w // n_sub)
    cohs_time = []
    for s0 in range(0, w - sub + 1, sub):
        block = seg[:, s0:s0 + sub]
        cohs_time.append(np.mean([_coherence(block[c]) for c in range(n_ch)]))
    cohs_time = np.asarray(cohs_time) if cohs_time else np.array([0.5])
    mean_coh = float(cohs_time.mean())
    G = float(np.clip(1.0 - cohs_time.std(), 0.0, 1.0))
    D4 = float(np.clip(np.mean(np.abs(np.diff(cohs_time))) * 4.0, 0.0, 1.0)) \
        if cohs_time.shape[0] > 1 else 0.0

    ents, purs = [], []
    for c in range(n_ch):
        f, P = _spectrum(seg[c], fs)
        ents.append(_spectral_entropy(P))
        purs.append(_spectral_purity(f, P))
    I = float(np.clip(np.mean(ents), 0.0, 1.0))
    E = float(np.clip(np.mean(purs), 0.0, 1.0))
    D3 = E

    # GILE-L = cross-coupling strength. Hemodynamic coupling primitive = infraslow
    # cross-frequency coupling (features.hemo_cfc); broadband correlation retained
    # as a weak secondary term (shared multichannel structure).
    cfcs = [hemo_cfc(seg[c], fs) for c in range(n_ch)]
    L_cfc = float(np.clip(np.mean(cfcs) * 5.0, 0.0, 1.0))
    if n_ch > 1:
        Cc = np.corrcoef(seg)
        iu = np.triu_indices(n_ch, k=1)
        L_corr = float(np.clip(np.mean(np.abs(Cc[iu])), 0.0, 1.0))
    else:
        L_corr = 0.0
    L = float(np.clip(0.75 * L_cfc + 0.25 * L_corr, 0.0, 1.0))

    mag = np.abs(seg).mean(0)
    cv = mag.std() / (mag.mean() + 1e-9)
    D1 = float(np.clip(1.0 - cv, 0.0, 1.0))
    D2 = float(np.clip(1.0 - mean_coh, 0.0, 1.0))

    return {"G": G, "I": I, "L": L, "E": E,
            "D1": D1, "D2": D2, "D3": D3, "D4": D4}


def _alpha_from_window(seg, fs):
    """Project the window onto crystal-vertex amplitudes via per-channel band powers."""
    feats = []
    for c in range(seg.shape[0]):
        f, P = _spectrum(seg[c], fs)
        for lo, hi in _BANDS:
            m = (f >= lo) & (f < hi)
            feats.append(float(P[m].sum()))
    a = np.asarray(feats, dtype=float)
    a = a / (a.max() + 1e-12)
    return np.sqrt(a)


def ch_window_features(sig, fs, chans, starts, w, split_sample=None):
    """Return (nW, D) Consciousness-Hamiltonian feature matrix. Each row is built
    only from its own window slice.

    LEAKAGE PARITY WITH BASE: when `split_sample` is given, train windows
    (st < split_sample) are truncated at the boundary exactly as window_features
    does, so NO train row peeks at post-split samples. This makes the CH feature
    set obey the SAME boundary rule as BASE (symmetric leakage discipline)."""
    out = np.zeros((len(starts), len(CH_FEATURE_NAMES)))
    cidx = list(chans)
    n = sig.shape[1]
    for r, st in enumerate(starts):
        if split_sample is not None and st < split_sample:
            end = min(st + w, split_sample)
        else:
            end = min(st + w, n)
        seg = sig[np.ix_(cidx, range(st, end))]
        gh = gile_hem_from_window(seg, fs)
        G, I, L, E = gh["G"], gh["I"], gh["L"], gh["E"]
        comp = gile_composite(G, I, L, E)
        hem_score = float(np.clip(
            (gh["D1"] + (1 - gh["D2"]) + gh["D3"] + (1 - abs(gh["D4"] - 0.5) * 2)) / 4.0,
            0.0, 1.0))
        pdr, pdi = pd_full(comp, gh["D2"])
        z = pd_zone(pdr)
        alpha = _alpha_from_window(seg, fs)
        spec = hamiltonian_spectrum_features(alpha, G, I, L, E)
        fied, edens = gile_graph_fiedler(G, I, L, E)
        out[r] = [
            G, I, L, E, gh["D1"], gh["D2"], gh["D3"], gh["D4"],
            comp, hem_score, pdr, pdi, float(z),
            spec["lambda0"], spec["gap"], spec["lam_mean"], spec["lam_std"],
            spec["bandwidth"], spec["ground_ipr"], spec["ring_entropy"],
            spec["dom_ring"], fied, edens,
        ]
    return out
