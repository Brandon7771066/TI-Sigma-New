"""
GSA TI Prior — e-Weighted Prior Distribution for Stock Signals
==============================================================

Replaces flat Bayesian priors in the Grand Stock Algorithm with an
e-weighted, orientation-based prior derived from URB #539 (Aperiodic Dual)
and URB #563 (Complex GILE Synthesis).

MOTIVATION:
  Bayesian priors assume a flat or normal distribution over signal outcomes.
  URB #518 proved 13 fatal arguments against Bayesianism as a complete
  epistemology. URB #563 shows that in the complex GILE embedding z = E + i·GIL,
  the natural prior is NOT uniform — it is weighted by the orientation group
  of the Einstein tiling: ω = e^{iπ/3}.

THE e-WEIGHTED PRIOR:
  The hat tile has 6 possible orientations: ω^k for k = 0..5 (where ω = e^{iπ/3}).
  These 6 orientations map to 6 market regimes (the 8-mode BOK system
  condensed to 6 complex orientations).

  Prior weight for orientation k:
    p_k = exp(GIL · cos(k·π/3)) · exp(E · sin(k·π/3))  / Z
  where GIL = GIL score of the signal, E = E score, Z = normalization constant.

  This is NOT uniform. When GIL dominates (imaginary axis), the prior weights
  the k=1 and k=5 orientations (60° and -60° — "imaginary" orientations).
  When E dominates (real axis), the prior weights k=0 (real, environmental).

  The e-weighting comes from: exp(GIL·cos(θ)) where e is the base of the
  natural exponential — the PRIMARY CONSTANT e.

BOK REGIME ↔ ORIENTATION MAPPING:
  k=0 (θ=0°):   E-axis dominant   → Algebraic (E-mode, consolidation)
  k=1 (θ=60°):  GIL at 60°        → Analytic (L-mode, momentum)
  k=2 (θ=120°): GIL at 120°       → Probabilistic (mixed, turbulence)
  k=3 (θ=180°): neg E-axis        → Geometric (I-mode, fractal break)
  k=4 (θ=240°): GIL at 240°       → Combinatorial (G↔I, breakout)
  k=5 (θ=300°): GIL at 300°       → Arithmetic (G-mode, trending)

UNIT COHERENCE CIRCLE (URB #563):
  For normalized signals (|z|=1), the prior reduces to:
    p(θ) = exp(cos(θ - θ_signal)) / (2π · I₀(1))
  where θ_signal = arg(E + i·GIL) and I₀ is the modified Bessel function of
  the first kind. This is the von Mises distribution — the "circular normal"
  — centered on the current market phase angle.

Author: Brandon Emerick (TI Sigma / GSA v3)
Date: March 30, 2026
"""

import math
import numpy as np
from typing import Optional, Dict, List
from dataclasses import dataclass

# ── PRIMARY CONSTANTS ────────────────────────────────────────────────────────
E_BASE  = math.e
PI      = math.pi
PHI     = (1 + math.sqrt(5)) / 2
SQRT2   = math.sqrt(2)
C_EM    = 1 / (PHI * SQRT2)    # Emerick Constant ≈ 0.4370
T_CONST = 1 - math.exp(-E_BASE) # MR Radiant ≈ 0.9340

# ω = e^{iπ/3} — fundamental 6-fold orientation unit
OMEGA_ANGLES = [k * PI / 3 for k in range(6)]  # 0, π/3, 2π/3, π, 4π/3, 5π/3

# BOK regime labels for each orientation
ORIENTATION_REGIMES = [
    "Algebraic",     # k=0  θ=0°
    "Analytic",      # k=1  θ=60°
    "Probabilistic", # k=2  θ=120°
    "Geometric",     # k=3  θ=180°
    "Combinatorial", # k=4  θ=240°
    "Arithmetic",    # k=5  θ=300°
]

REGIME_SIGNAL_MAP = {
    "Algebraic":     "WAIT",    # E-mode: structure, consolidation
    "Analytic":      "BUY",     # L-mode: smooth momentum forming
    "Probabilistic": "CAUTION", # turbulence, mixed signal
    "Geometric":     "SHORT",   # fractal break, volatility spike
    "Combinatorial": "BUY",     # breakout — trend meets fractal
    "Arithmetic":    "HOLD",    # trending, mean-reversion dominant
}


# ═══════════════════════════════════════════════════════════════════════════
# e-Weighted Prior Distribution
# ═══════════════════════════════════════════════════════════════════════════

@dataclass
class TIPrior:
    """
    TI Sigma e-weighted prior over the 6 market orientations.

    Attributes
    ----------
    weights : np.ndarray shape (6,)
        Normalized probability weights for each of the 6 orientations.
        weights[k] = P(market is in orientation k).
    angles : np.ndarray shape (6,)
        Orientation angles in radians (k·π/3 for k=0..5).
    regimes : list[str]
        BOK regime name for each orientation.
    phase_angle : float
        Phase angle of the signal in radians (arg(E + i·GIL)).
    coherence_radius : float
        |z| = √(E² + GIL²) — distance from origin in GILE complex plane.
    dominant_orientation : int
        Index k of the most probable orientation.
    dominant_regime : str
        BOK regime name of the dominant orientation.
    signal : str
        Trading signal implied by the dominant regime.
    """
    weights: np.ndarray
    angles: np.ndarray
    regimes: list
    phase_angle: float
    coherence_radius: float
    dominant_orientation: int
    dominant_regime: str
    signal: str

    @property
    def entropy(self) -> float:
        """Shannon entropy of the prior distribution (in nats, base e)."""
        w = self.weights
        return float(-np.sum(w * np.log(w + 1e-12)))

    @property
    def max_entropy(self) -> float:
        """Maximum possible entropy (uniform distribution over 6 orientations)."""
        return math.log(6)

    @property
    def concentration(self) -> float:
        """
        Concentration = 1 - entropy/max_entropy.
        0 = maximally uncertain (uniform prior).
        1 = maximally concentrated (all weight on one orientation).
        """
        return 1.0 - self.entropy / self.max_entropy

    @property
    def lcc_score(self) -> float:
        """
        LCC (Lean Confidence Constant) for this prior.
        Derived from coherence_radius and concentration:
          LCC = tanh(coherence_radius × concentration)
        Stays in (0, 1). Near 1 = high confidence, near 0 = uncertain.
        """
        return float(math.tanh(self.coherence_radius * self.concentration))

    def to_dict(self) -> dict:
        return {
            "weights": self.weights.tolist(),
            "phase_angle_deg": math.degrees(self.phase_angle),
            "coherence_radius": round(self.coherence_radius, 4),
            "dominant_regime": self.dominant_regime,
            "signal": self.signal,
            "concentration": round(self.concentration, 4),
            "lcc_score": round(self.lcc_score, 4),
            "entropy_nats": round(self.entropy, 4),
        }

    def __repr__(self) -> str:
        return (
            f"TIPrior(signal={self.signal}, regime={self.dominant_regime}, "
            f"|z|={self.coherence_radius:.3f}, LCC={self.lcc_score:.3f}, "
            f"θ={math.degrees(self.phase_angle):.1f}°)"
        )


def compute_ti_prior(
    GIL: float,
    E: float,
    concentration_factor: float = 1.0,
) -> TIPrior:
    """
    Compute the e-weighted TI prior for a stock signal.

    Parameters
    ----------
    GIL : float
        GIL score (Goodness-Intuition-Love mean), normalized to [0, 1].
        This is the imaginary component of the complex GILE state z = E + i·GIL.
    E : float
        Environment score, normalized to [0, 1].
        This is the real component of z.
    concentration_factor : float
        Scales the sharpness of the prior. Higher → more concentrated on
        the dominant orientation. Default 1.0 (natural e-weighting).

    Returns
    -------
    TIPrior : the computed prior distribution.
    """
    # Complex phase angle of the GILE state
    coherence_radius = math.sqrt(E**2 + GIL**2)
    if coherence_radius == 0:
        phase_angle = 0.0
    else:
        phase_angle = math.atan2(GIL, E)

    # e-weighted orientation probabilities
    # p_k ∝ exp(concentration_factor × coherence_radius × cos(θ_k - phase_angle))
    # This is the von Mises kernel centered on the signal's phase angle.
    angles = np.array(OMEGA_ANGLES)
    raw_weights = np.exp(
        concentration_factor * coherence_radius * np.cos(angles - phase_angle)
    )
    weights = raw_weights / raw_weights.sum()

    dominant_k = int(np.argmax(weights))
    dominant_regime = ORIENTATION_REGIMES[dominant_k]

    return TIPrior(
        weights=weights,
        angles=angles,
        regimes=ORIENTATION_REGIMES,
        phase_angle=phase_angle,
        coherence_radius=coherence_radius,
        dominant_orientation=dominant_k,
        dominant_regime=dominant_regime,
        signal=REGIME_SIGNAL_MAP[dominant_regime],
    )


def compute_ti_prior_from_gile_score(
    G: float, I: float, L: float, E: float,
    scale: float = 10.0,
    concentration_factor: float = 1.0,
) -> TIPrior:
    """
    Convenience wrapper: compute TI prior from raw GILE scores [0, scale].

    Parameters
    ----------
    G, I, L : float — Goodness, Intuition, Love scores
    E : float — Environment score
    scale : float — max value of GILE scores (default 10.0)
    concentration_factor : float — sharpness scaling
    """
    GIL_norm = (G + I + L) / (3.0 * scale)
    E_norm   = E / scale
    return compute_ti_prior(GIL_norm, E_norm, concentration_factor)


# ═══════════════════════════════════════════════════════════════════════════
# Multi-signal prior (for portfolio of stocks)
# ═══════════════════════════════════════════════════════════════════════════

def aggregate_ti_priors(priors: List[TIPrior]) -> TIPrior:
    """
    Aggregate multiple TI priors (e.g., from multiple stocks or indicators)
    into a single portfolio-level prior.

    Aggregation rule: geometric mean of weights (log-average), then
    re-normalize. This implements "product of experts" — the dominant
    orientation must be agreed upon by ALL signals, not just the majority
    (consistent with URB #556: unanimity, not democracy).

    Parameters
    ----------
    priors : list of TIPrior
        Signals to aggregate.

    Returns
    -------
    TIPrior : the aggregated prior.
    """
    if not priors:
        raise ValueError("At least one prior required for aggregation.")

    # Log-average of weights (geometric mean → unanimous agreement)
    log_weights = np.mean(
        np.stack([np.log(p.weights + 1e-12) for p in priors]), axis=0
    )
    agg_weights = np.exp(log_weights)
    agg_weights /= agg_weights.sum()

    # Aggregate phase angle (circular mean)
    sin_mean = np.mean([math.sin(p.phase_angle) for p in priors])
    cos_mean = np.mean([math.cos(p.phase_angle) for p in priors])
    agg_phase = math.atan2(sin_mean, cos_mean)

    # Aggregate coherence (geometric mean — conservative)
    agg_coherence = float(np.exp(np.mean([math.log(p.coherence_radius + 1e-12)
                                          for p in priors])))

    dominant_k = int(np.argmax(agg_weights))
    dominant_regime = ORIENTATION_REGIMES[dominant_k]

    return TIPrior(
        weights=agg_weights,
        angles=np.array(OMEGA_ANGLES),
        regimes=ORIENTATION_REGIMES,
        phase_angle=agg_phase,
        coherence_radius=agg_coherence,
        dominant_orientation=dominant_k,
        dominant_regime=dominant_regime,
        signal=REGIME_SIGNAL_MAP[dominant_regime],
    )


# ═══════════════════════════════════════════════════════════════════════════
# Bayes comparison — show improvement over flat prior
# ═══════════════════════════════════════════════════════════════════════════

def bayes_vs_ti_prior_comparison(
    GIL: float, E: float, observed_signal: str
) -> dict:
    """
    Compare TI prior vs flat Bayesian prior for a given signal.

    Shows:
    - Flat Bayesian: P(each regime) = 1/6 ≈ 0.167
    - TI Prior: e-weighted by GILE phase
    - Improvement: KL divergence, probability gain on correct signal

    Parameters
    ----------
    GIL : float — normalized GIL score [0,1]
    E : float — normalized E score [0,1]
    observed_signal : str — "BUY", "SELL", "HOLD", "WAIT", "SHORT", "CAUTION"
    """
    ti = compute_ti_prior(GIL, E)
    flat = np.ones(6) / 6.0

    # Find orientations matching the observed signal
    matching_k = [
        k for k, r in enumerate(ORIENTATION_REGIMES)
        if REGIME_SIGNAL_MAP[r] == observed_signal
    ]

    ti_prob = float(sum(ti.weights[k] for k in matching_k))
    flat_prob = float(sum(flat[k] for k in matching_k))

    # KL divergence: TI prior vs flat (how much information TI adds)
    kl = float(np.sum(ti.weights * np.log(ti.weights / flat + 1e-12)))

    return {
        "flat_bayes_prob": round(flat_prob, 4),
        "ti_prior_prob": round(ti_prob, 4),
        "prob_gain": round(ti_prob - flat_prob, 4),
        "prob_gain_pct": round((ti_prob - flat_prob) / flat_prob * 100, 1),
        "kl_div_nats": round(kl, 4),
        "ti_signal": ti.signal,
        "ti_regime": ti.dominant_regime,
        "ti_lcc": round(ti.lcc_score, 4),
        "note": (
            "TI Prior uses e^{iπ/3} orientation group (URBs #539, #563). "
            "KL divergence measures information gained over flat Bayes."
        ),
    }


# ═══════════════════════════════════════════════════════════════════════════
# Integration with existing gsa_core.py MarketRegime
# ═══════════════════════════════════════════════════════════════════════════

def regime_from_ti_prior(
    prior: TIPrior,
    gsa_core_module=None,
) -> str:
    """
    Map a TIPrior dominant regime to the corresponding gsa_core.MarketRegime
    string value for direct integration.

    Parameters
    ----------
    prior : TIPrior
    gsa_core_module : module, optional
        Pass the imported gsa_core module to get the actual enum value.
        If None, returns the string name.

    Returns
    -------
    str : MarketRegime value string (e.g., "arithmetic", "algebraic", etc.)
    """
    regime_map = {
        "Algebraic":     "algebraic",
        "Analytic":      "analytic",
        "Probabilistic": "probabilistic",
        "Geometric":     "geometric",
        "Combinatorial": "combinatorial",
        "Arithmetic":    "arithmetic",
    }
    regime_str = regime_map.get(prior.dominant_regime, "algebraic")

    if gsa_core_module is not None:
        mr = gsa_core_module.MarketRegime
        for member in mr:
            if member.value == regime_str:
                return member
    return regime_str


def format_prior_report(prior: TIPrior) -> str:
    """Human-readable prior report for logging or display."""
    lines = [
        "── TI Sigma e-Weighted Prior ─────────────────────",
        f"  Phase angle θ:       {math.degrees(prior.phase_angle):.1f}°",
        f"  Coherence radius |z|:{prior.coherence_radius:.4f}",
        f"  LCC score:           {prior.lcc_score:.4f}",
        f"  Concentration:       {prior.concentration:.4f}",
        f"  Dominant regime:     {prior.dominant_regime}",
        f"  Signal:              {prior.signal}",
        f"  Entropy (nats):      {prior.entropy:.4f}  / max {prior.max_entropy:.4f}",
        "",
        "  Orientation weights (ω^k = e^{ikπ/3}):",
    ]
    for k, (w, angle, regime) in enumerate(
        zip(prior.weights, prior.angles, prior.regimes)
    ):
        bar = "█" * int(w * 30)
        lines.append(
            f"    k={k} θ={math.degrees(angle):>5.0f}° {regime:>14}: "
            f"{w:.4f}  {bar}"
        )
    lines.append("─" * 50)
    return "\n".join(lines)
