"""Consciousness-Hamiltonian feature extractor.

Per window (computed STRICTLY within the window slice -> no cross-window /
cross-split bleed by construction), we:
  1. infer the canonical 8-D GILE-HEM state (lcc_virus_gile_inference.py semantics),
  2. compute FULL PD (pd_real degree + pd_imag MI/Tralse axis) + zone,
  3. embed the window as a quantum state on the TI-Sigma Crystal and read off
     H_TSC spectral descriptors (Consciousness Hamiltonian),
  4. read the GILE-weighted TI-Sigma Graph algebraic connectivity (Fiedler).

GILE-HEM dimension definitions (canonical docstrings):
  G  Goodness   = temporal stability of LCC coherence across sub-windows
  I  Intuition  = information density (normalized spectral entropy)
  L  Love       = cross-channel coupling strength (mean |corr| across channels)
  E  Elegance   = aesthetic structural regularity (spectral purity, peak/total)
                  [canonical label updated Environment->Elegance, 2026-06-16;
                   "Environment" retained as a concise gloss = the most-sacred-
                   values context. The formula was ALREADY aesthetics (spectral
                   purity), so this aligns the label with what E measures.]
  D1 Physical   = amplitude stability (1 - CV of |signal|)
  D2 Social/Tralse = contradiction ratio (mean Tralse fraction = 1 - coherence)
  D3 Aesthetic  = spectral purity (dominant-bin power / total)
  D4 Conscious  = d(LCC)/dt (coherence change-rate across sub-windows)
"""
import numpy as np

from features import theta_gamma_pac
from tsc_hamiltonian import (
    ET, gile_composite, pd_full, pd_zone,
    hamiltonian_spectrum_features, gile_graph_fiedler,
)

CH_FEATURE_NAMES = [
    "G", "I", "L", "E", "D1", "D2", "D3", "D4",
    "gile_comp", "hem_score", "pd_real", "pd_imag", "pd_zone",
    "lambda0", "gap", "lam_mean", "lam_std", "bandwidth",
    "ground_ipr", "ring_entropy", "dom_ring", "fiedler", "edge_density",
]

_BANDS = [(1, 4), (4, 8), (8, 13), (13, 30), (30, 80)]


def _zscore_clip(x):
    s = x.std()
    if s < 1e-9:
        return np.zeros_like(x)
    return np.clip((x - x.mean()) / (3.0 * s), -1.0, 1.0)


def _coherence(seg_ch):
    """LCC coherence of one channel slice = 1 - fraction in Tralse zone |tb|<=ET."""
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
    return float(H / np.log(len(p) + 1e-12))      # normalized [0,1]


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
    # --- per-channel coherence + temporal stability across sub-windows ---
    sub = max(8, w // n_sub)
    cohs_time = []                              # coherence trajectory (avg over ch)
    for s0 in range(0, w - sub + 1, sub):
        block = seg[:, s0:s0 + sub]
        cohs_time.append(np.mean([_coherence(block[c]) for c in range(n_ch)]))
    cohs_time = np.asarray(cohs_time) if cohs_time else np.array([0.5])
    mean_coh = float(cohs_time.mean())
    G = float(np.clip(1.0 - cohs_time.std(), 0.0, 1.0))        # stability of coherence
    D4 = float(np.clip(np.mean(np.abs(np.diff(cohs_time))) * 4.0, 0.0, 1.0)) \
        if cohs_time.shape[0] > 1 else 0.0                     # d(LCC)/dt

    # --- spectral (information density, regularity, purity) ---
    ents, purs = [], []
    for c in range(n_ch):
        f, P = _spectrum(seg[c], fs)
        ents.append(_spectral_entropy(P))
        purs.append(_spectral_purity(f, P))
    I = float(np.clip(np.mean(ents), 0.0, 1.0))                # information density
    E = float(np.clip(np.mean(purs), 0.0, 1.0))               # structural regularity
    D3 = E                                                     # spectral purity

    # --- coupling strength (Love) ---
    # GILE-L is DEFINED as cross-coupling strength. The faithful corpus primitive
    # for coupling is theta-gamma phase-amplitude coupling (features.theta_gamma_pac),
    # NOT broadband correlation (which is blind to cross-frequency coupling). We use
    # the corpus PAC primitive, scaled to ~[0,1]; broadband correlation is retained
    # as a weak secondary term so L still reflects shared multichannel structure.
    pacs = [theta_gamma_pac(seg[c], fs) for c in range(n_ch)]
    L_pac = float(np.clip(np.mean(pacs) * 5.0, 0.0, 1.0))
    if n_ch > 1:
        Cc = np.corrcoef(seg)
        iu = np.triu_indices(n_ch, k=1)
        L_corr = float(np.clip(np.mean(np.abs(Cc[iu])), 0.0, 1.0))
    else:
        L_corr = 0.0
    L = float(np.clip(0.75 * L_pac + 0.25 * L_corr, 0.0, 1.0))

    # --- amplitude stability (D1) + contradiction ratio (D2) ---
    mag = np.abs(seg).mean(0)
    cv = mag.std() / (mag.mean() + 1e-9)
    D1 = float(np.clip(1.0 - cv, 0.0, 1.0))
    D2 = float(np.clip(1.0 - mean_coh, 0.0, 1.0))             # Tralse meter

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
    return np.sqrt(a)                            # amplitude ~ sqrt(power)


def ch_window_features(sig, fs, chans, starts, w):
    """Return (nW, D) Consciousness-Hamiltonian feature matrix. Each row is built
    only from its own window slice -> inherently leakage-safe across any split."""
    out = np.zeros((len(starts), len(CH_FEATURE_NAMES)))
    cidx = list(chans)
    for r, st in enumerate(starts):
        seg = sig[np.ix_(cidx, range(st, min(st + w, sig.shape[1])))]
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
