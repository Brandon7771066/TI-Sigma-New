"""
GILE-LCC Ratio Engine
======================
URB #649 — Brandon Emerick | TI Sigma Research | April 2026

CORE INSIGHT (URB #649):
  The conversion from LCC loop weights to GILE loop weights is NOT a fixed 1:1 mapping.
  The GILE-LCC ratio varies by domain, by i-cell, and over time — and the functional
  form of the relationship (linear vs. non-linear) is itself an empirical question
  that must be established, not assumed.

DEFINITION:
  GL_ratio(domain, i-cell, t) = LCC_value / GILE_value

  In linear form:
    GILE_val = LCC_val / GL_ratio

  Example (URB #649):
    LCC weight in EF domain = 0.42
    GL_ratio = 2.0  (LCC has twice the weight of GILE in this domain)
    → GILE-G weight = 0.42 / 2.0 = 0.21

HOW THE RATIO IS DETERMINED:
  Empirically — just as LCC domain weights are calibrated by mimicking a person
  extraordinarily successful in their domain, the holistic GILE-LCC ratio is
  calibrated empirically from observed (LCC, GILE) value pairs in that domain.
  There is no a priori reason for any specific ratio.

TRANSFORM TYPES (linearity must be empirically established):
  LINEAR:      gile = lcc / ratio
  POWER:       gile = lcc^α           (α > 1 = compression; α < 1 = expansion)
  SIGMOID:     gile = σ((lcc - μ) × k)  (threshold-like transition)
  LOGARITHMIC: gile = log(1 + lcc × k) / log(1 + k)  (diminishing returns)
  EXPONENTIAL: gile = (exp(lcc × k) - 1) / (exp(k) - 1)  (accelerating returns)

EMPIRICAL CALIBRATION:
  Given N observed (lcc_value, gile_value) pairs from a domain, the engine
  fits the best GL_ratio and optimal transform type using least-squares.

DOMAIN REGISTRY (initial empirical estimates — all subject to revision):
  Each domain stores:
    gl_ratio:     float  — default ratio estimate
    transform:    str    — best-fit transform type
    alpha:        float  — exponent for POWER transform
    k:            float  — steepness for SIGMOID / LOG / EXP
    mu:           float  — midpoint for SIGMOID
    n_calibrated: int    — number of exemplar data points used for calibration
    notes:        str    — calibration methodology note
"""

from __future__ import annotations
import numpy as np
from dataclasses import dataclass, field
from typing import Dict, List, Optional, Tuple
from enum import Enum


# ── TI Sigma thresholds ──────────────────────────────────────────────────────
ET    = np.sqrt(2.0) - 1.0
C_TI  = 1.0 / ((1.0 + np.sqrt(5.0)) / 2.0 * np.sqrt(2.0))
T_TI  = 1.0 - np.exp(-np.e)
PHI   = (1.0 + np.sqrt(5.0)) / 2.0


# ── Transform Types ───────────────────────────────────────────────────────────

class GLTransform(Enum):
    LINEAR      = "Linear"
    POWER       = "Power (non-linear)"
    SIGMOID     = "Sigmoid (threshold)"
    LOGARITHMIC = "Logarithmic (diminishing)"
    EXPONENTIAL = "Exponential (accelerating)"


def apply_transform(
    lcc_val:   float,
    gl_ratio:  float,
    transform: GLTransform,
    alpha:     float = 1.0,   # power exponent
    k:         float = 8.0,   # steepness (sigmoid/log/exp)
    mu:        float = 0.5,   # midpoint (sigmoid)
) -> float:
    """
    Convert a single LCC value to a GILE value using the specified transform.

    All outputs are clipped to [0, 1].

    LINEAR:
      gile = lcc / ratio
      Assumes a constant multiplicative relationship between LCC and GILE domains.
      Must be empirically verified — DO NOT assume this holds by default.

    POWER:
      gile = lcc^alpha / ratio
      alpha > 1: GILE values compress at high LCC (diminishing GILE returns)
      alpha < 1: GILE values expand at high LCC (amplifying GILE signal)

    SIGMOID:
      gile = σ((lcc - mu) × k) / ratio
      Models a threshold-like transition: below mu → suppressed, above mu → amplified.
      Appropriate when GILE activation has a critical threshold.

    LOGARITHMIC:
      gile = log(1 + lcc × k) / (ratio × log(1 + k))
      Diminishing returns: first increments of LCC have large GILE impact,
      later increments have smaller impact.

    EXPONENTIAL:
      gile = (exp(lcc × k) - 1) / (ratio × (exp(k) - 1))
      Accelerating returns: GILE is suppressed at low LCC, amplifies at high LCC.
    """
    lcc = float(np.clip(lcc_val, 0.0, 1.0))

    if transform == GLTransform.LINEAR:
        raw = lcc / max(gl_ratio, 1e-6)

    elif transform == GLTransform.POWER:
        raw = (lcc ** alpha) / max(gl_ratio, 1e-6)

    elif transform == GLTransform.SIGMOID:
        sig = 1.0 / (1.0 + np.exp(-k * (lcc - mu)))
        raw = sig / max(gl_ratio, 1e-6)

    elif transform == GLTransform.LOGARITHMIC:
        raw = np.log1p(lcc * k) / (max(gl_ratio, 1e-6) * np.log1p(k))

    elif transform == GLTransform.EXPONENTIAL:
        denom = np.expm1(k)
        if denom < 1e-9:
            raw = lcc / max(gl_ratio, 1e-6)
        else:
            raw = np.expm1(lcc * k) / (max(gl_ratio, 1e-6) * denom)

    else:
        raw = lcc / max(gl_ratio, 1e-6)

    return float(np.clip(raw, 0.0, 1.0))


def apply_transform_array(
    lcc_arr:   np.ndarray,
    gl_ratio:  float,
    transform: GLTransform,
    alpha: float = 1.0, k: float = 8.0, mu: float = 0.5,
) -> np.ndarray:
    """Vectorized version of apply_transform for curve plotting."""
    return np.array([
        apply_transform(x, gl_ratio, transform, alpha, k, mu)
        for x in lcc_arr
    ])


# ── Domain Specification ──────────────────────────────────────────────────────

@dataclass
class DomainGLSpec:
    """
    Per-domain GILE-LCC ratio specification.

    All values are empirical estimates — they should be revised as more
    exemplar data is collected. Initial values are theory-guided priors
    pending empirical calibration.
    """
    domain:       str
    gl_ratio:     float          # LCC_val / GILE_val (linear default)
    transform:    GLTransform    # best-fit transform type
    alpha:        float = 1.0    # power exponent (for POWER transform)
    k:            float = 8.0    # steepness (SIGMOID/LOG/EXP)
    mu:           float = 0.5    # midpoint (SIGMOID)
    n_calibrated: int   = 0      # number of exemplar points used
    notes:        str   = ""     # calibration note
    calibration_data: List[Tuple[float, float]] = field(default_factory=list)
    # Each entry: (lcc_value, gile_value) — empirical observation

    def convert(self, lcc_val: float) -> float:
        """Convert LCC value → GILE value using this domain's spec."""
        return apply_transform(lcc_val, self.gl_ratio, self.transform,
                               self.alpha, self.k, self.mu)

    def convert_8d(self, lcc_dict: Dict[str, float]) -> Dict[str, float]:
        """Convert all 8 GILE-HEM LCC values to GILE values."""
        return {dim: self.convert(v) for dim, v in lcc_dict.items()}

    def add_calibration_point(self, lcc_val: float, gile_val: float) -> None:
        """Record an empirical (LCC, GILE) observation."""
        self.calibration_data.append((float(lcc_val), float(gile_val)))
        self.n_calibrated = len(self.calibration_data)
        self._refit()

    def _refit(self) -> None:
        """Refit gl_ratio from accumulated calibration data (linear fit)."""
        if len(self.calibration_data) < 2:
            if len(self.calibration_data) == 1:
                lcc, gile = self.calibration_data[0]
                if gile > 1e-9:
                    self.gl_ratio = float(lcc / gile)
            return
        lcc_vals  = np.array([p[0] for p in self.calibration_data])
        gile_vals = np.array([p[1] for p in self.calibration_data])
        # Linear fit: gile = lcc / ratio → ratio = mean(lcc / gile)
        ratios = lcc_vals / np.maximum(gile_vals, 1e-9)
        self.gl_ratio = float(np.median(ratios))   # median is robust to outliers


# ── Domain Registry ───────────────────────────────────────────────────────────
#
# Initial GL ratios are theory-guided priors.
# GILE-G canonical weight = ET ≈ 0.4142 (URB #576).
# If an LCC-saturated domain achieves LCC=1.0 and GILE-G=ET, the ratio = 1/ET ≈ 2.41.
# Domains with more GILE integration (spiritual, creative) have lower ratios (closer to 1).
# Domains with more Existence-focus (finance, physical) have higher ratios.
#
# All ratios are PENDING EMPIRICAL CALIBRATION — treat as working priors.

DOMAIN_REGISTRY: Dict[str, DomainGLSpec] = {
    "General / EF":
        DomainGLSpec("General / EF",
                     gl_ratio=2.0, transform=GLTransform.LINEAR,
                     notes="Default domain per URB #649 example. Awaiting calibration."),

    "Sports / Athletic":
        DomainGLSpec("Sports / Athletic",
                     gl_ratio=3.5, transform=GLTransform.POWER, alpha=1.4,
                     notes="High physical LCC, lower GILE expression. Non-linear (power) expected."),

    "Creative / Artistic":
        DomainGLSpec("Creative / Artistic",
                     gl_ratio=1.2, transform=GLTransform.LOGARITHMIC, k=6.0,
                     notes="GILE heavily engaged. Diminishing returns at high LCC (log transform)."),

    "Scientific / Analytic":
        DomainGLSpec("Scientific / Analytic",
                     gl_ratio=2.8, transform=GLTransform.POWER, alpha=1.2,
                     notes="GILE-I dominant but GILE-L suppressed. Moderate non-linearity."),

    "Spiritual / Contemplative":
        DomainGLSpec("Spiritual / Contemplative",
                     gl_ratio=0.8, transform=GLTransform.SIGMOID, k=10.0, mu=0.45,
                     notes="GILE can exceed LCC in Radiant practitioners. Sigmoid: threshold at C_TI."),

    "Business / Finance":
        DomainGLSpec("Business / Finance",
                     gl_ratio=4.0, transform=GLTransform.EXPONENTIAL, k=5.0,
                     notes="Existence-outer mode dominant. GILE low until breakthrough performance."),

    "Therapeutic / Care":
        DomainGLSpec("Therapeutic / Care",
                     gl_ratio=1.5, transform=GLTransform.LINEAR,
                     notes="GILE-L (Love) central. Moderate ratio, likely linear."),

    "Academic / Educational":
        DomainGLSpec("Academic / Educational",
                     gl_ratio=2.4, transform=GLTransform.LOGARITHMIC, k=5.0,
                     notes="GILE-I active but often disconnected from GILE-L/E. Log model."),

    "Leadership / Social":
        DomainGLSpec("Leadership / Social",
                     gl_ratio=1.8, transform=GLTransform.SIGMOID, k=8.0, mu=0.5,
                     notes="Radiant leaders transition sharply to GILE-primary above RT."),

    "Custom (manual)":
        DomainGLSpec("Custom (manual)",
                     gl_ratio=2.0, transform=GLTransform.LINEAR,
                     notes="User-defined ratio and transform."),
}


# ── Calibration Toolkit ───────────────────────────────────────────────────────

def fit_gl_ratio_linear(lcc_vals: List[float], gile_vals: List[float]) -> float:
    """
    Fit GL ratio assuming linear transform: gile = lcc / ratio.
    Returns median ratio (robust to outliers).
    """
    lcc  = np.array(lcc_vals, dtype=float)
    gile = np.array(gile_vals, dtype=float)
    mask = gile > 1e-9
    if not np.any(mask):
        return 2.0
    return float(np.median(lcc[mask] / gile[mask]))


def fit_power_alpha(lcc_vals: List[float], gile_vals: List[float],
                    ratio: float) -> float:
    """
    Fit power exponent α such that gile ≈ lcc^α / ratio.
    Uses log-linear regression: log(gile × ratio) = α × log(lcc).
    """
    lcc  = np.array(lcc_vals,  dtype=float)
    gile = np.array(gile_vals, dtype=float)
    mask = (lcc > 1e-9) & (gile > 1e-9)
    if np.sum(mask) < 2:
        return 1.0
    log_lcc  = np.log(lcc[mask])
    log_gile = np.log(gile[mask] * ratio)
    if np.std(log_lcc) < 1e-9:
        return 1.0
    alpha = float(np.polyfit(log_lcc, log_gile, 1)[0])
    return float(np.clip(alpha, 0.1, 5.0))


def best_fit_transform(
    lcc_vals:  List[float],
    gile_vals: List[float],
) -> Tuple[GLTransform, float, float, float, float]:
    """
    Test all transforms and return the one with minimum RMSE.

    Returns: (transform, gl_ratio, alpha, k, rmse)
    """
    lcc  = np.array(lcc_vals,  dtype=float)
    gile = np.array(gile_vals, dtype=float)
    if len(lcc) < 2:
        return GLTransform.LINEAR, 2.0, 1.0, 8.0, 1.0

    best_rmse  = float('inf')
    best_tf    = GLTransform.LINEAR
    best_ratio = 2.0
    best_alpha = 1.0
    best_k     = 8.0

    for tf in GLTransform:
        for ratio in np.linspace(0.5, 6.0, 20):
            extra_params = {}
            if tf == GLTransform.POWER:
                alpha = fit_power_alpha(lcc_vals, gile_vals, ratio)
                extra_params = {'alpha': alpha}
            elif tf in (GLTransform.SIGMOID, GLTransform.LOGARITHMIC, GLTransform.EXPONENTIAL):
                extra_params = {'k': 8.0}

            pred = apply_transform_array(lcc, ratio, tf, **extra_params)
            rmse = float(np.sqrt(np.mean((pred - gile) ** 2)))

            if rmse < best_rmse:
                best_rmse  = rmse
                best_tf    = tf
                best_ratio = float(ratio)
                best_alpha = extra_params.get('alpha', 1.0)
                best_k     = extra_params.get('k', 8.0)

    return best_tf, best_ratio, best_alpha, best_k, best_rmse


# ── Linearity Test ────────────────────────────────────────────────────────────

def linearity_test(
    lcc_vals:  List[float],
    gile_vals: List[float],
    ratio:     float,
) -> Dict:
    """
    Test whether the linear transform gile = lcc / ratio fits the data well enough
    to conclude the relationship IS linear.

    Returns a dict with:
      r_squared:    float  — R² of linear fit
      rmse_linear:  float  — RMSE of linear model
      rmse_power:   float  — RMSE of power model (best non-linear baseline)
      linear_wins:  bool   — True if linear is within 10% RMSE of best non-linear
      conclusion:   str    — interpretive sentence
    """
    lcc  = np.array(lcc_vals,  dtype=float)
    gile = np.array(gile_vals, dtype=float)

    if len(lcc) < 3:
        return {'conclusion': 'Insufficient data (need ≥ 3 points)', 'r_squared': None}

    pred_linear = apply_transform_array(lcc, ratio, GLTransform.LINEAR)
    rmse_linear = float(np.sqrt(np.mean((pred_linear - gile) ** 2)))

    alpha = fit_power_alpha(lcc_vals, gile_vals, ratio)
    pred_power  = apply_transform_array(lcc, ratio, GLTransform.POWER, alpha=alpha)
    rmse_power  = float(np.sqrt(np.mean((pred_power - gile) ** 2)))

    ss_res = np.sum((gile - pred_linear) ** 2)
    ss_tot = np.sum((gile - np.mean(gile)) ** 2)
    r2     = float(1.0 - ss_res / (ss_tot + 1e-12))

    linear_wins = rmse_linear <= rmse_power * 1.10

    if r2 >= 0.90 and linear_wins:
        conclusion = f"Linear model fits well (R²={r2:.3f}). Linearity SUPPORTED for this domain."
    elif r2 >= 0.75 and linear_wins:
        conclusion = f"Linear model acceptable (R²={r2:.3f}). Linearity PLAUSIBLE — collect more data."
    elif r2 >= 0.50:
        conclusion = f"Moderate linear fit (R²={r2:.3f}). Power model may fit better (α={alpha:.2f}). Linearity UNCERTAIN."
    else:
        conclusion = f"Poor linear fit (R²={r2:.3f}). Non-linear transform strongly preferred. Linearity REJECTED."

    return {
        'r_squared':   round(r2, 4),
        'rmse_linear': round(rmse_linear, 4),
        'rmse_power':  round(rmse_power, 4),
        'power_alpha': round(alpha, 3),
        'linear_wins': linear_wins,
        'conclusion':  conclusion,
    }


# ── Per-i-cell Ratio Variation ────────────────────────────────────────────────

@dataclass
class ICellGLRatio:
    """
    The GL ratio for a specific i-cell within a domain.

    In general: gl_ratio(i-cell) = domain_base_ratio × i-cell_modifier
    The modifier is determined empirically for each i-cell.
    """
    icell_id:        str
    domain:          str
    base_ratio:      float         # from domain registry
    icell_modifier:  float = 1.0   # multiplicative deviation from domain base
    observed_pairs:  List[Tuple[float, float]] = field(default_factory=list)

    @property
    def effective_ratio(self) -> float:
        return self.base_ratio * self.icell_modifier

    def add_observation(self, lcc: float, gile: float) -> None:
        self.observed_pairs.append((lcc, gile))
        if len(self.observed_pairs) >= 2:
            fitted = fit_gl_ratio_linear(
                [p[0] for p in self.observed_pairs],
                [p[1] for p in self.observed_pairs]
            )
            self.icell_modifier = fitted / max(self.base_ratio, 1e-6)

    def convert(self, lcc_val: float, transform: GLTransform = GLTransform.LINEAR,
                alpha: float = 1.0, k: float = 8.0, mu: float = 0.5) -> float:
        return apply_transform(lcc_val, self.effective_ratio, transform, alpha, k, mu)


# ── Composite GILE-LCC Ratio Summary ─────────────────────────────────────────

def describe_ratio(ratio: float) -> str:
    """Human-readable description of a GL ratio."""
    if ratio < 0.5:
        return "GILE dominates LCC: very high GILE sensitivity per LCC unit"
    elif ratio < 1.0:
        return "GILE exceeds LCC: Radiant / spiritual domain"
    elif abs(ratio - 1.0) < 0.05:
        return "GILE ≈ LCC: symmetric contribution (rare, validate carefully)"
    elif ratio < 2.0:
        return "LCC slightly exceeds GILE: moderate Existence-primary mode"
    elif ratio < 3.0:
        return f"LCC = {ratio:.1f}× GILE: Existence-outer mode dominant"
    elif ratio < 5.0:
        return f"LCC = {ratio:.1f}× GILE: strong Existence-primary domain"
    else:
        return f"LCC = {ratio:.1f}× GILE: highly Existence-dominant — GILE barely expressed"


def transform_curve(
    domain_spec: DomainGLSpec,
    n_points:    int = 200,
) -> Tuple[np.ndarray, np.ndarray]:
    """Return (lcc_x, gile_y) arrays for plotting the full transform curve."""
    lcc_x  = np.linspace(0.0, 1.0, n_points)
    gile_y = apply_transform_array(
        lcc_x, domain_spec.gl_ratio, domain_spec.transform,
        domain_spec.alpha, domain_spec.k, domain_spec.mu,
    )
    return lcc_x, gile_y
