"""
GSA CORE ENGINE v3 — TI Sigma BOK Architecture + TIL Pipeline
==============================================================
Grand Stock Algorithm — Existence Intensity Framework
Ξ(E) = A(t) · κ(t,τ) · C(t) → PD → BOK(GILE-EV) → MR → Signal

MAIN TI SIGMA THEORIES (URBs #615, #617, #618):
  TIL  = Tralse-Myrion Logic — the operational truth-navigation framework:
           PD  (Permissibility Distribution)  — 5-state truth assignment
           BOK (Being-of-Knowledge, GILE-EV i-Cell) — structural model
           MR  (Myrion Resolution)            — convergence procedure
  UOP  = Unified Optimization Principle — TIL's guiding principle;
           optimizes simultaneously across all GILE + EV dimensions.
  BOK  + LCC are the two structural flagships.
  PD   + MR  + EAR are the three operational pillars.

v2 Upgrades (March 2026):
  - Emerick Constant C_EMERICK = 1/(φ√2) ≈ 0.4370 as primary threshold
  - Extended Euler normalization: e^(iπ) + √2·φ·C = 0
  - BOK 8-Mode regime classification (4 primary + 4 interface)
  - Theorem A: Attractor basin bifurcation detection
  - Dual-Confidence Principle: EC (exploratory) + EpC (epistemic)

v2.1 Upgrades (March 20, 2026 — URBs #463–468):
  - PRIMARY CONSTANTS unity: {0, 1, i, √2, e, φ, π, C}
  - Complex Signal Representation: z = EC·e^(iθ) in ℂ-plane
  - Antifragile Score (URB #466)
  - Tralse Apology principle (URB #468)

v3 Upgrades (April 7, 2026 — URBs #615, #618):
  - TIL pipeline formally named; PD + BOK + MR integrated
  - PDDistribution: 5-state truth-distribution over market signals
      TT (True-Tralse)         → strong directional signal
      TI (Tralse-Indeterminate) → genuine ambiguity, MR unresolved
      TF (Tralse-False)        → contra-signal
      DT (Double-Tralse)       → no tradeable truth-state, pause
      EV (EV-Decoupled)        → existence diverges from signal
  - EVScore: HEM Dimensions for each stock (HEM-D1..4)
  - GILEScore expanded: now includes ev_composite for UOP scoring
  - UOP position sizing: replaces simple regime multiplier with full
    GILE-EV composite optimization across all five dimensions
  - MR-gated signal: DT screen as Level-1 MR before any action
"""

import numpy as np
from typing import Dict, List, Tuple, Optional
from dataclasses import dataclass, field
from enum import Enum

# ─── TI Sigma Primary Constants ───────────────────────────────────────────────

PHI      = (1.0 + np.sqrt(5.0)) / 2.0          # Golden ratio ≈ 1.6180
SQRT2    = np.sqrt(2.0)                          # √2 ≈ 1.4142
C_EMERICK = 1.0 / (PHI * SQRT2)                 # Emerick Constant ≈ 0.4370

# LCC Threshold ladder (derived from primary constants)
LCC_FLOOR   = 0.0                                # Absolute minimum
LCC_TRALSE  = C_EMERICK                          # ≈ 0.4370  (Tralse zone entry)
LCC_LOW     = 1.0 - 1.0 / PHI                   # ≈ 0.3820  (below golden mean)
LCC_MID     = 0.5                                # Symmetry axis
LCC_HIGH    = 1.0 / SQRT2                        # ≈ 0.7071  (Emerick Crossover)
LCC_RADIANT = 1.0 - 1.0 / (PHI * PHI)          # ≈ 0.6180  (golden section)
LCC_PEAK    = 1.0                                # Full coherence


# ─── BOK 8-Mode Market Regimes ────────────────────────────────────────────────

class MarketRegime(Enum):
    # PRIMARY 4 (single-axis BOK modes)
    ARITHMETIC    = "arithmetic"     # G-mode: trending, mean-reversion dominant
    ALGEBRAIC     = "algebraic"      # E-mode: structural, sideways/consolidation
    ANALYTIC      = "analytic"       # L-mode: smooth momentum flow, new trend forming
    GEOMETRIC     = "geometric"      # I-mode: fractal break, volatility spike

    # INTERFACE 4 (transition/hybrid BOK modes — bifurcation zone)
    LOGIC         = "logic"          # C1 = G↔E: trend meets structure (wait)
    COMBINATORIAL = "combinatorial"  # C2 = G↔I: trend meets fractal (breakout)
    PROBABILISTIC = "probabilistic"  # C3 = L↔I: flow meets fractal (turbulence)
    APPLIED       = "applied"        # C4 = E↔L: structure meets flow (regime shift)

    # Backward-compatible aliases (old 4-mode names still work)
    @classmethod
    def EXPANSION(cls):   return cls.ARITHMETIC
    @classmethod
    def COMPRESSION(cls): return cls.ALGEBRAIC
    @classmethod
    def FRACTURE(cls):    return cls.GEOMETRIC
    @classmethod
    def RESET(cls):       return cls.ANALYTIC


# ─── Dataclasses ──────────────────────────────────────────────────────────────

@dataclass
class XiMetrics:
    """Existence Intensity decomposition: Ξ(E) = A(t) · κ(t,τ) · C(t)"""
    amplitude:      float   # A(t)    — normalized current move
    memory_kernel:  float   # κ(t,τ)  — negative memory dominance [0,1]
    constraint:     float   # C(t)    — drawdown + volatility constraint [0,1]
    xi_unsigned:    float   # A·κ·C
    xi_signed:      float   # with valence weight
    pd:             float   # Probability Distribution score [-3, +2]


@dataclass
class GILEScore:
    """
    Four-dimensional GILE assessment (inner BOK loops).
    Extended in v3 to carry ev_composite for UOP position sizing.
    """
    goodness:    float   # G — risk-adjusted returns (Sharpe proxy)
    intuition:   float   # I — trend pre-recognition (MA crossover signal)
    love:        float   # L — market correlation coherence
    environment: float   # E — structural/momentum alignment
    composite:   float   # GILE weighted combination [0,1]
    ev_composite: float = 0.5  # EV composite from EVScore [0,1]; injected after compute_ev


@dataclass
class EVScore:
    """
    Holistic Existence Matrix (HEM) Score — HEM Dimensions.
    Models the stock's 'existence' in the market ecosystem (BOK outer loops).

    HEM-D1 Physical/Energetic:    Volume-weighted price stability
    HEM-D2 Social/Historical:     52-week position (institutional presence proxy)
    HEM-D3 Aesthetic/Structural:  Technical pattern quality (clean chart proxy)
    HEM-D4 Conscious/Experiential: Momentum-of-momentum (second derivative of trend)

    HEM-Score (Holistic Existence Score) = EAR output = weighted FDE mean [0,1].
    High HEM-Score → stock has robust market existence; position is warranted.
    Low HEM-Score  → stock is existentially fragile; EV-decoupling risk.
    """
    fde1_physical:    float   # Volume-energetic stability [0,1]
    fde2_social:      float   # 52W position proxy [0,1]
    fde3_aesthetic:   float   # Technical pattern quality [0,1]
    fde4_conscious:   float   # Momentum of momentum [0,1]
    esv:              float   # Existence Scalar Value (EAR output) [0,1]
    ev_decoupled:     bool    # True = EV and GILE are diverging (>0.35 delta)


@dataclass
class PDDistribution:
    """
    Permissibility Distribution — 5 market truth-states (URB #615, #618).
    Replaces the scalar PD float with a proper truth-state distribution.

    Applied to the stock's TIL pipeline:
      TT  True-Tralse:         Signal confirmed by GILE + EV → BUY / STRONG_BUY
      TI  Tralse-Indeterminate: Genuine ambiguity, MR unresolved → HOLD / WAIT
      TF  Tralse-False:         Contra-signal evidence dominates → CAUTION / SELL
      DT  Double-Tralse:        No tradeable truth-state present → EXIT / PAUSE
      EV  EV-Decoupled:         Holistic Existence Matrix diverges from signal → WATCH

    MR Resolution:
      Level 1: DT screen — if dt_weight > 0.35, action = 'pause' (MR gate)
      Level 2: HEM-GILE integration — reweight TT/TI/TF by GILE + HEM-Score
      Level 3: Convergence — if dominant state weight > MR_THRESHOLD, mr_resolved = True
    """
    tt_weight:   float   # True-Tralse weight
    ti_weight:   float   # Tralse-Indeterminate weight
    tf_weight:   float   # Tralse-False weight
    dt_weight:   float   # Double-Tralse weight (MR gate: >0.35 → pause)
    ev_weight:   float   # EV-Decoupled weight
    dominant:    str     # Name of highest-weight truth-state
    mr_resolved: bool    # True = dominant state > MR_THRESHOLD (0.45)
    til_action:  str     # TIL-derived action: buy/hold/sell/pause/watch

    @property
    def uncertainty(self) -> float:
        """Unresolved information = 1 - dominant_weight. NOT error."""
        weights = [self.tt_weight, self.ti_weight, self.tf_weight,
                   self.dt_weight, self.ev_weight]
        return float(1.0 - max(weights))

    @property
    def dt_gate_active(self) -> bool:
        """MR Level-1 DT screen: pause if DT > 0.35."""
        return self.dt_weight > 0.35

    def to_dict(self) -> dict:
        return {
            "tt": round(self.tt_weight, 4),
            "ti": round(self.ti_weight, 4),
            "tf": round(self.tf_weight, 4),
            "dt": round(self.dt_weight, 4),
            "ev": round(self.ev_weight, 4),
            "dominant": self.dominant,
            "mr_resolved": self.mr_resolved,
            "til_action": self.til_action,
            "uncertainty": round(self.uncertainty, 4),
            "dt_gate_active": self.dt_gate_active,
        }


@dataclass
class BifurcationResult:
    """
    Theorem A (MR Collapse): Attractor basin bifurcation detection.
    Regime transitions are non-linear basin crossings, not linear thresholds.
    """
    metastability:  float   # [0,1] — how long system has been near a boundary
    abruptness:     float   # [0,1] — sharpness of the recent transition
    basin_depth:    float   # [0,1] — post-transition stability (depth of new basin)
    in_bifurcation: bool    # True = currently in the metastable transition zone
    crossing_detected: bool # True = bifurcation just occurred in recent window


@dataclass
class TIComplexSignal:
    """
    Complex-number signal representation using PRIMARY CONSTANTS i.

    The signal lives in the ℂ-plane:
        z = EC · e^(iθ)
        Re(z) = EC · cos(θ) — trend component (price direction momentum)
        Im(z) = EC · sin(θ) — volatility structure (orthogonal, non-trend)
        |z|   = EC           — total signal magnitude
        θ     = phase angle in [0, 2π]

    Interpretation of phase θ:
        θ → 0           pure trend (real axis): clean momentum signal
        θ → π/4  (45°)  balanced trend + structure: highest quality signal
        θ → π/2  (90°)  pure volatility (imaginary axis): structurally driven
        θ → π    (180°) counter-trend: bearish vs price direction
        θ → 3π/2 (270°) inverse volatility structure: contrarian setup

    The Euler identity e^(iπ) + 1 = 0 governs the signal ceiling:
        when θ → π, the complex signal inverts — a natural sell override.
    Only trade when |z| > C_EMERICK (≈ 0.437) AND |Re(z)| > C_EMERICK/√2.
    """
    ec:          float          # Signal magnitude = |z|
    theta:       float          # Phase angle in radians
    real:        float          # Re(z) = trend component
    imag:        float          # Im(z) = volatility structure
    magnitude:   float          # |z| — same as ec by construction
    phase_deg:   float          # θ in degrees (readability)
    tradeable_complex: bool     # |z| > C_EMERICK AND Re(z) > 0
    signal_quality: str         # "trend_pure", "balanced", "vol_dominant", "counter"


@dataclass
class AntifragileScore:
    """
    Antifragile Score (URB #466 — Antifragile Confirms Tralse).

    Measures whether a stock specifically IMPROVES during market disorder.
    Based on Taleb's antifragility principle, formalized as the Tralse Both-And:
        Disorder (False pole) → activates True-pole response → synthesis above baseline

    Methodology:
        1. Identify high-disorder market periods (VIX proxy: market drawdown > 5% in 20d)
        2. Measure stock performance during those periods vs. baseline
        3. Antifragile bonus = mean(stock_ret | disorder) - mean(stock_ret | calm)
        4. If bonus > 0: stock improves from disorder → antifragile
        5. If bonus ≈ 0: resilient (survives but doesn't gain)
        6. If bonus < 0: fragile (damaged by disorder)

    Paradigm antifragile cases (URB #466):
        Energy majors (COP, CVX, XOM) during supply disruptions
        Gold miners during monetary disorder
        Defense contractors during geopolitical disorder
        Short-vol premium strategies during calm (inverse antifragile)
    """
    antifragile_bonus: float    # Stock excess return during disorder periods
    disorder_periods:  int      # Number of high-disorder periods identified
    calm_mean:         float    # Mean return during calm periods
    disorder_mean:     float    # Mean return during disorder periods
    classification:    str      # "antifragile", "resilient", "fragile"
    tralse_resolved:   bool     # True = disorder produces net synthesis (bonus > 0)


@dataclass
class Signal:
    """
    Trading signal with Dual-Confidence decomposition (Paper #389).
    EC and EpC are orthogonal — never collapse to single scalar before trading.
    """
    action:     str             # strong_buy, buy, hold, sell, strong_sell
    ec:         float           # Exploratory Confidence [0,1] — signal strength now
    epc:        float           # Epistemic Certainty [0,1] — pattern validation
    tral_state: bool            # True = EC high but EpC low (directionally supported)
    gile:       float
    xi_metrics: XiMetrics
    regime:     MarketRegime
    bifurcation: BifurcationResult
    reasons:    List[str] = field(default_factory=list)

    @property
    def confidence(self) -> float:
        """Backward-compatible composite confidence = (EC + EpC) / 2"""
        return float((self.ec + self.epc) / 2.0)

    @property
    def tradeable(self) -> bool:
        """Execute only when both EC > 0.65 AND EpC > 0.50 (Dual-Confidence gate)"""
        return self.ec > 0.65 and self.epc > 0.50


# ─── GSA Core Engine ──────────────────────────────────────────────────────────

class GSACore:
    """
    GSA Core v2 — BOK 8-Mode, Attractor Basin, Dual-Confidence.
    Platform-agnostic: works with Alpaca, QuantConnect, Numerai, or research.
    """

    def __init__(
        self,
        lookback_short:   int   = 7,
        lookback_long:    int   = 60,
        kappa_decay_pos:  float = 0.10,
        kappa_decay_neg:  float = 0.05,
        gile_weights: Tuple[float, float, float, float] = (0.20, 0.25, 0.25, 0.30)
    ):
        self.lookback_short  = lookback_short
        self.lookback_long   = lookback_long
        self.kappa_decay_pos = kappa_decay_pos
        self.kappa_decay_neg = kappa_decay_neg
        self.gile_weights    = gile_weights

        # PD valence weights
        self.W_GREAT     = 1.0
        self.W_TERRIBLE  = 2.0
        self.W_EXCEPTIONAL = 1.5
        self.W_WICKED    = 6.0

        # Regime exposure multipliers (position sizing)
        self.regime_adj: Dict[MarketRegime, float] = {
            MarketRegime.ARITHMETIC:    1.00,   # Full exposure — clean trend
            MarketRegime.ALGEBRAIC:     0.50,   # Half exposure — sideways
            MarketRegime.GEOMETRIC:     0.00,   # No exposure — fractal break
            MarketRegime.ANALYTIC:      0.30,   # Cautious — new trend forming
            MarketRegime.LOGIC:         0.40,   # Transition wait
            MarketRegime.COMBINATORIAL: 0.70,   # Breakout opportunity
            MarketRegime.PROBABILISTIC: 0.20,   # Turbulence — defensive
            MarketRegime.APPLIED:       0.35,   # Regime shift — reduced
        }

        # History for regime detection and EpC calculation
        self.constraint_history: List[float] = []
        self.pd_history:         List[float] = []
        self.regime_history:     List[MarketRegime] = []

    # ── Xi Metrics ────────────────────────────────────────────────────────────

    def compute_xi_metrics(self, returns: np.ndarray, prices: np.ndarray) -> XiMetrics:
        """Compute full Ξ(E) = A(t) · κ(t,τ) · C(t) decomposition."""
        if len(returns) < 10 or len(prices) < 10:
            return XiMetrics(0.0, 0.5, 0.0, 0.0, 0.0, 0.0)

        A     = self._amplitude(returns[-self.lookback_short:])
        kappa = self._memory_kernel(returns[-self.lookback_long:])
        C     = self._constraint(prices, returns)

        xi_unsigned = A * kappa * C

        curr_ret = float(returns[-1])
        valence  = 1.0 if curr_ret >= 0 else -1.0
        W        = self._valence_weight(curr_ret)
        xi_signed = valence * xi_unsigned * W

        # Extended Euler normalization: e^(iπ) + √2·φ·C_EMERICK = 0
        # Signals exceeding the Euler envelope are dampened by C_EMERICK factor
        euler_envelope = SQRT2 * PHI * C_EMERICK   # = 1.0 by construction
        if abs(xi_signed) > euler_envelope:
            xi_signed = np.sign(xi_signed) * euler_envelope

        pd = np.sign(xi_signed) * np.log1p(abs(xi_signed))
        pd = float(np.clip(pd, -3.0, 2.0))

        return XiMetrics(
            amplitude=float(A),
            memory_kernel=float(kappa),
            constraint=float(C),
            xi_unsigned=float(xi_unsigned),
            xi_signed=float(xi_signed),
            pd=float(pd)
        )

    def _amplitude(self, rets: np.ndarray) -> float:
        if len(rets) < 2:
            return 0.0
        vol = max(float(np.std(rets)), 0.01)
        return float(np.clip(abs(rets[-1]) / vol, 0.0, 10.0))

    def _memory_kernel(self, rets: np.ndarray) -> float:
        if len(rets) < 3:
            return 0.5
        kpos, kneg = 0.0, 0.0
        for i in range(len(rets)):
            r = float(rets[-1 - i])
            if r >= 0:
                kpos += abs(r) * np.exp(-self.kappa_decay_pos * i)
            else:
                kneg += abs(r) * np.exp(-self.kappa_decay_neg * i)
        total = kpos + kneg
        return 0.5 if total <= 0 else float(np.clip(kneg / total, 0.0, 1.0))

    def _constraint(self, prices: np.ndarray, rets: np.ndarray) -> float:
        if len(prices) < 5 or len(rets) < 5:
            return 0.0
        peak = float(np.max(prices))
        dd   = (peak - float(prices[-1])) / peak if peak > 0 else 0.0
        rs   = rets[-min(len(rets), self.lookback_short):]
        rl   = rets[-min(len(rets), self.lookback_long):]
        v_recent = float(np.std(rs)) if len(rs) >= 2 else 1.0
        v_long   = float(np.std(rl)) if len(rl) >= 2 else 1.0
        ratio    = v_recent / max(v_long, 0.01)
        vol_c    = 1.0 - min(ratio, 1.0)
        return float(np.clip(0.6 * dd + 0.4 * vol_c, 0.0, 1.0))

    def _valence_weight(self, ret_pct: float) -> float:
        if ret_pct > 5.0:    return self.W_EXCEPTIONAL
        if ret_pct > 0.333:  return self.W_GREAT
        if ret_pct > -0.666: return 1.0
        if ret_pct > -5.0:   return self.W_TERRIBLE
        return self.W_WICKED

    # ── GILE Score ────────────────────────────────────────────────────────────

    def compute_gile(
        self,
        returns:        np.ndarray,
        prices:         np.ndarray,
        market_returns: Optional[np.ndarray] = None
    ) -> GILEScore:
        """GILE: G=Goodness, I=Intuition, L=Love, E=Environment."""
        if len(returns) < 30 or len(prices) < 30:
            return GILEScore(0.5, 0.5, 0.5, 0.5, 0.5)

        r20      = returns[-20:]
        mean_ret = float(np.mean(r20))
        std_ret  = max(float(np.std(r20)), 0.01)
        goodness = 1.0 / (1.0 + np.exp(-mean_ret / std_ret))

        ma5  = float(np.mean(prices[-5:]))
        ma15 = float(np.mean(prices[-15:]))
        intuition = 1.0 / (1.0 + np.exp(-((ma5 - ma15) / max(ma15, 0.01)) * 50.0))

        love = 0.5
        if market_returns is not None and len(market_returns) >= 20:
            try:
                corr = float(np.corrcoef(returns[-20:], market_returns[-20:])[0, 1])
                if not np.isnan(corr):
                    love = (corr + 1.0) / 2.0
            except Exception:
                love = 0.5

        m10 = float(np.sum(returns[-10:]))
        m30 = float(np.sum(returns[-30:]))
        env = 1.0 / (1.0 + np.exp(-(m10 * m30) * 0.01))

        w_g, w_i, w_l, w_e = self.gile_weights
        composite = w_g * goodness + w_i * intuition + w_l * love + w_e * env

        return GILEScore(
            goodness=float(goodness),
            intuition=float(intuition),
            love=float(love),
            environment=float(env),
            composite=float(np.clip(composite, 0.0, 1.0))
        )

    # ── Attractor Basin Detection (Theorem A) ─────────────────────────────────

    def detect_bifurcation(self, constraint_history: List[float]) -> BifurcationResult:
        """
        Theorem A (MR Collapse): Detect attractor basin bifurcation.

        Three-phase pattern:
          1. Metastability — system oscillates near regime boundary
          2. Bifurcation spike — abrupt non-linear transition
          3. Post-transition — rapid stabilization in new regime

        This matches the EEG hypnagogic pattern: prolonged alpha/beta oscillation
        → sharp alpha+theta co-spike → collapse into sleep attractor.
        """
        h = list(constraint_history)
        n = len(h)

        if n < 10:
            return BifurcationResult(
                metastability=0.0, abruptness=0.0,
                basin_depth=0.5, in_bifurcation=False,
                crossing_detected=False
            )

        # Emerick threshold — C_EMERICK is the Tralse zone boundary
        threshold = C_EMERICK  # ≈ 0.437

        # Metastability: how many of the last 10 values are near the threshold?
        recent = h[-10:]
        near_threshold = sum(1 for v in recent if abs(v - threshold) < 0.10)
        metastability = float(near_threshold) / 10.0

        # Abruptness: max single-step change relative to recent std
        if n >= 3:
            diffs = [abs(h[i] - h[i-1]) for i in range(max(1, n-5), n)]
            recent_std = max(float(np.std(h[-10:])), 0.001)
            abruptness = float(np.clip(max(diffs) / (recent_std * 3.0), 0.0, 1.0))
        else:
            abruptness = 0.0

        # Basin depth: post-transition stability — low variance after jump
        if n >= 6:
            post_var  = float(np.std(h[-3:]))
            pre_var   = float(np.std(h[-6:-3]))
            basin_depth = float(np.clip(1.0 - (post_var / max(pre_var, 0.001)), 0.0, 1.0))
        else:
            basin_depth = 0.5

        # Crossing detected: abrupt change AND preceded by metastability
        crossing_detected = (abruptness > 0.60) and (metastability > 0.30)

        # In bifurcation: metastability high but no crossing yet
        in_bifurcation = (metastability > 0.40) and not crossing_detected

        return BifurcationResult(
            metastability=metastability,
            abruptness=abruptness,
            basin_depth=basin_depth,
            in_bifurcation=in_bifurcation,
            crossing_detected=crossing_detected
        )

    # ── BOK 8-Mode Regime Classification ─────────────────────────────────────

    def classify_regime(
        self,
        pd:        float,
        constraint: float,
        vol_ratio:  float
    ) -> Tuple[MarketRegime, float, float]:
        """
        BOK 8-Mode regime classification.

        Primary modes (post-bifurcation, stable):
          ARITHMETIC  (G): Clean uptrend or mean-reversion
          ALGEBRAIC   (E): Structural sideways, low volatility
          GEOMETRIC   (I): Fractal break, high volatility, fracture
          ANALYTIC    (L): New trend forming from reset

        Interface modes (bifurcation/transition zone):
          LOGIC         (C1 = G↔E): Trend decelerating into consolidation
          COMBINATORIAL (C2 = G↔I): Trend accelerating toward breakout
          PROBABILISTIC (C3 = L↔I): New trend meeting volatility cluster
          APPLIED       (C4 = E↔L): Consolidation breaking into new trend

        Returns: (regime, confidence, constraint_rate)
        """
        self.constraint_history.append(float(constraint))
        # Bug fix: never let NaN into pd_history — one NaN poisons np.std() for all subsequent tickers
        if not np.isnan(pd) and not np.isinf(pd):
            self.pd_history.append(float(pd))
        self.constraint_history = self.constraint_history[-self.lookback_long:]
        self.pd_history         = self.pd_history[-self.lookback_long:]

        # Rate of constraint change (5-step vs 10-step lookback)
        constraint_rate = 0.0
        if len(self.constraint_history) >= 10:
            recent_c = float(np.mean(self.constraint_history[-5:]))
            older_c  = float(np.mean(self.constraint_history[-10:-5]))
            constraint_rate = recent_c - older_c

        # Detect attractor basin dynamics
        bif = self.detect_bifurcation(self.constraint_history)

        # ── Interface regimes fire during metastability (bifurcation zone) ──
        if bif.in_bifurcation:
            # Which pair of primaries are transitioning?
            if constraint_rate > 0.05 and pd > 0:
                regime = MarketRegime.LOGIC          # G→E: trend slowing
            elif constraint_rate > 0.05 and pd < 0:
                regime = MarketRegime.COMBINATORIAL  # G→I: breakout building
            elif constraint_rate < -0.05 and pd < 0:
                regime = MarketRegime.PROBABILISTIC  # L→I: new trend hits turbulence
            else:
                regime = MarketRegime.APPLIED        # E→L: consolidation breaking
            confidence = float(np.clip(0.40 + bif.metastability * 0.30, 0.40, 0.70))
            self.regime_history.append(regime)
            return regime, confidence, float(constraint_rate)

        # ── Primary regimes fire post-bifurcation ──
        if constraint_rate > 0.10 and vol_ratio > 1.5 and pd < -1.0:
            regime     = MarketRegime.GEOMETRIC
            confidence = float(np.clip(0.50 + abs(constraint_rate) + abs(pd) / 3.0, 0.50, 0.92))

        elif constraint_rate > 0.05 and vol_ratio < 0.7:
            regime     = MarketRegime.ALGEBRAIC
            confidence = float(np.clip(0.50 + constraint_rate * 2.0 + (1.0 - vol_ratio), 0.50, 0.87))

        elif constraint_rate < -0.05 and vol_ratio > 1.0:
            regime     = MarketRegime.ANALYTIC
            confidence = float(np.clip(0.50 + abs(constraint_rate) + (vol_ratio - 1.0) * 0.5, 0.50, 0.82))

        else:
            regime     = MarketRegime.ARITHMETIC
            confidence = float(np.clip(0.70 - abs(constraint_rate) * 2.0, 0.40, 0.90))

        # Basin depth bonus — post-crossing stability increases confidence
        if bif.crossing_detected:
            confidence = float(np.clip(confidence + bif.basin_depth * 0.15, 0.0, 0.95))

        self.regime_history.append(regime)
        self.regime_history = self.regime_history[-self.lookback_long:]
        return regime, float(confidence), float(constraint_rate)

    # ── Epistemic Certainty (EpC) ──────────────────────────────────────────────

    def _compute_epc(self, current_regime: MarketRegime, base_gile: float) -> float:
        """
        Epistemic Certainty: how well-validated is the current pattern?

        EpC rises as:
          - The same regime has appeared consistently (not flip-flopping)
          - GILE has been stable (not oscillating)
          - Basin depth is high (system settled in current regime)

        EpC falls when:
          - Regime has been changing frequently
          - System is in a bifurcation interface mode
        """
        n = len(self.regime_history)
        if n < 5:
            return 0.40  # Insufficient history — Tral-state by default

        # Regime consistency: fraction of recent history in same regime
        recent_regimes = self.regime_history[-min(n, 20):]
        same_count = sum(1 for r in recent_regimes if r == current_regime)
        consistency = float(same_count) / float(len(recent_regimes))

        # Interface regime penalty — bifurcation zones are inherently uncertain
        interface_modes = {
            MarketRegime.LOGIC, MarketRegime.COMBINATORIAL,
            MarketRegime.PROBABILISTIC, MarketRegime.APPLIED
        }
        interface_penalty = 0.20 if current_regime in interface_modes else 0.0

        # GILE stability: low variance in pd history = stable signal
        # Bug fix: filter any stray NaN before calling np.std()
        clean_pd = [x for x in self.pd_history[-10:] if not np.isnan(x) and not np.isinf(x)]
        if len(clean_pd) >= 5:
            pd_std = float(np.std(clean_pd))
            gile_stability = float(np.clip(1.0 - pd_std / 2.0, 0.0, 1.0))
        else:
            gile_stability = 0.50

        epc = 0.50 * consistency + 0.30 * gile_stability + 0.20 * base_gile
        epc = float(np.clip(epc - interface_penalty, 0.0, 1.0))
        return epc

    # ── Signal Generation (Dual-Confidence) ──────────────────────────────────

    def generate_signal(
        self,
        xi_metrics:        XiMetrics,
        gile:              GILEScore,
        regime:            MarketRegime,
        regime_confidence: float,
        bifurcation:       Optional[BifurcationResult] = None
    ) -> Signal:
        """
        Generate trading signal with Dual-Confidence (EC + EpC).

        EC (Exploratory Confidence): directional strength of current signal.
        EpC (Epistemic Certainty): pattern validation depth.
        Tral-state: EC high but EpC low — directionally supported, not established.
        """
        if bifurcation is None:
            bifurcation = BifurcationResult(0.0, 0.0, 0.5, False, False)

        reasons: List[str] = []

        # ── Base action from GILE composite ──────────────────────────────────
        g = gile.composite
        if g > 0.65:
            base, base_ec = "strong_buy", 0.82
            reasons.append(f"GILE {g:.3f} > 0.65 (G-mode: high goodness)")
        elif g > 0.55:
            base, base_ec = "buy", 0.65
            reasons.append(f"GILE {g:.3f} > 0.55")
        elif g > 0.45:
            base, base_ec = "hold", 0.50
        elif g > 0.35:
            base, base_ec = "sell", 0.65
            reasons.append(f"GILE {g:.3f} < 0.45")
        else:
            base, base_ec = "strong_sell", 0.82
            reasons.append(f"GILE {g:.3f} < 0.35")

        # ── BOK regime modulation ─────────────────────────────────────────────
        if regime == MarketRegime.GEOMETRIC:
            return Signal(
                action="strong_sell",
                ec=float(np.clip(regime_confidence, 0.70, 0.95)),
                epc=self._compute_epc(regime, g),
                tral_state=False,
                gile=g, xi_metrics=xi_metrics,
                regime=regime, bifurcation=bifurcation,
                reasons=["GEOMETRIC fracture — exit all positions"]
            )

        if regime == MarketRegime.PROBABILISTIC:
            base_ec *= 0.55
            reasons.append("PROBABILISTIC turbulence — reduced EC")
        elif regime == MarketRegime.ALGEBRAIC:
            if base in ("buy", "strong_buy"):
                base = "hold"
                reasons.append("ALGEBRAIC consolidation — holding, not buying")
            base_ec *= 0.70
        elif regime == MarketRegime.APPLIED:
            base_ec *= 0.65
            reasons.append("APPLIED regime shift — cautious")
        elif regime in (MarketRegime.LOGIC, MarketRegime.COMBINATORIAL):
            base_ec *= 0.80
            reasons.append(f"{regime.value.upper()} bifurcation zone — waiting")
        elif regime == MarketRegime.ARITHMETIC and xi_metrics.pd > 0.5:
            base_ec = float(np.clip(base_ec * 1.20, 0.0, 0.92))
            reasons.append("ARITHMETIC + positive PD — full trend boost")

        # ── Xi overrides ──────────────────────────────────────────────────────
        if xi_metrics.xi_signed < -2.0:
            base, base_ec = "strong_sell", max(base_ec, 0.72)
            reasons.append(f"Ξ override: {xi_metrics.xi_signed:.2f} < -2.0")

        if xi_metrics.memory_kernel > 0.70 and base in ("buy", "strong_buy"):
            base = "hold"
            reasons.append(f"κ negative dominance: {xi_metrics.memory_kernel:.2f}")

        # ── Emerick Constant threshold check ─────────────────────────────────
        tralse_ratio_approx = float(np.clip(abs(xi_metrics.pd) / 3.0, 0.0, 1.0))
        in_tralse_zone = C_EMERICK <= tralse_ratio_approx <= LCC_HIGH
        if in_tralse_zone:
            reasons.append(f"Tralse zone: ratio={tralse_ratio_approx:.3f} ∈ [C_E={C_EMERICK:.3f}, LCC_H={LCC_HIGH:.3f}]")

        # ── Bifurcation effect on EC ──────────────────────────────────────────
        if bifurcation.crossing_detected:
            base_ec = float(np.clip(base_ec + bifurcation.basin_depth * 0.12, 0.0, 0.95))
            reasons.append(f"Basin crossing: depth={bifurcation.basin_depth:.2f}")

        # ── Compute EpC ───────────────────────────────────────────────────────
        ec  = float(np.clip(base_ec, 0.0, 1.0))
        epc = self._compute_epc(regime, g)

        # Tral-state: EC directionally strong but EpC not yet validated
        tral_state = (ec > 0.65) and (epc <= 0.50)
        if tral_state:
            reasons.append(f"TRAL-STATE: EC={ec:.2f} high, EpC={epc:.2f} low (directional, not established)")

        return Signal(
            action=base,
            ec=ec,
            epc=epc,
            tral_state=tral_state,
            gile=g,
            xi_metrics=xi_metrics,
            regime=regime,
            bifurcation=bifurcation,
            reasons=reasons
        )

    # ── Complex Signal (PRIMARY CONSTANTS i integration) ─────────────────────

    def compute_complex_signal(
        self,
        signal:     "Signal",
        returns:    np.ndarray,
        prices:     np.ndarray
    ) -> TIComplexSignal:
        """
        Represent signal in the ℂ-plane: z = EC · e^(iθ).

        Phase angle θ is derived from the ratio of:
          - Price momentum strength (trend component → real axis)
          - Volatility structure departure (orthogonal → imaginary axis)

        The Euler identity e^(iπ) + 1 = 0 means:
          when θ = π (counter-trend), the complex signal magnitude inverts sign
          → natural override to sell, consistent with Euler normalization.

        Only trade when:
          |z| > C_EMERICK       (≈ 0.437 — Tralse zone entry, URB #462)
          AND Re(z) > C_EMERICK/√2 (≈ 0.309 — trend component must be positive)
        """
        ec = float(np.clip(signal.ec, 0.0, 1.0))

        # Real component: normalized price momentum over lookback_short
        if len(returns) >= self.lookback_short:
            mom = float(np.mean(returns[-self.lookback_short:]))
            trend = float(np.tanh(mom * 0.5))   # [-1, 1]
        else:
            trend = 0.0

        # Imaginary component: volatility structure (vol ratio departure from 1.0)
        if len(returns) >= self.lookback_short * 2:
            v_short = float(np.std(returns[-self.lookback_short:]))
            v_long  = float(np.std(returns[-self.lookback_long:]))
            vol_ratio = v_short / max(v_long, 0.01)
            vol_structure = float(np.tanh((vol_ratio - 1.0)))  # [-1, 1]
        else:
            vol_structure = 0.0

        # Phase angle θ from the trend/vol ratio
        theta = float(np.arctan2(vol_structure, trend))   # [-π, π]
        if theta < 0:
            theta += 2 * np.pi                            # normalize to [0, 2π]

        # Complex components
        real = ec * np.cos(theta)
        imag = ec * np.sin(theta)
        magnitude = float(np.sqrt(real**2 + imag**2))    # = ec by construction

        # Quality classification by phase angle
        deg = np.degrees(theta) % 360
        if deg < 22.5 or deg > 337.5:
            quality = "trend_pure"       # θ ≈ 0°  — clean momentum
        elif 22.5 <= deg <= 67.5:
            quality = "balanced"         # θ ≈ 45° — best signal quality
        elif 67.5 < deg <= 112.5:
            quality = "vol_dominant"     # θ ≈ 90° — structure-driven
        elif 157.5 <= deg <= 202.5:
            quality = "counter"          # θ ≈ 180° — Euler inversion (sell)
        else:
            quality = "mixed"

        # Euler inversion check: θ near π → negate real component
        if 135 <= deg <= 225:
            real = -abs(real)            # Euler: e^(iπ) + 1 = 0 forces negative

        tradeable_complex = (
            magnitude > C_EMERICK and
            real > C_EMERICK / SQRT2     # ≈ 0.309
        )

        return TIComplexSignal(
            ec=ec,
            theta=float(theta),
            real=float(real),
            imag=float(imag),
            magnitude=float(magnitude),
            phase_deg=float(deg),
            tradeable_complex=tradeable_complex,
            signal_quality=quality
        )

    # ── Antifragile Score (URB #466 — Antifragile Confirms Tralse) ───────────

    def compute_antifragile_score(
        self,
        stock_returns:  np.ndarray,
        market_returns: Optional[np.ndarray] = None,
        disorder_threshold: float = -2.0    # market daily return % triggering disorder
    ) -> AntifragileScore:
        """
        Compute antifragile score: does this stock IMPROVE during market disorder?

        Disorder period: days when market_returns < disorder_threshold (large down day)
        or when market_returns std in rolling 5d exceeds 2× baseline std.
        If no market_returns provided, uses stock's own drawdown as disorder proxy.

        Antifragile (URB #466):
          - Taleb's Both-And: disorder is False pole AND True-pole activation
          - Tralse resolved IFF stock gains specifically from disorder
          - Paradigm: COP/CVX during geopolitical supply shock (+10–12%)
        """
        n = len(stock_returns)
        if n < 30:
            return AntifragileScore(0.0, 0, 0.0, 0.0, "insufficient_data", False)

        # ── Identify disorder periods ─────────────────────────────────────────
        if market_returns is not None and len(market_returns) == n:
            mkt = np.array(market_returns, dtype=float)
            # Primary disorder: large single-day market loss
            disorder_mask = mkt < disorder_threshold
            # Secondary disorder: rolling 5d vol spike (2× baseline)
            baseline_vol = float(np.std(mkt))
            for i in range(5, n):
                rv = float(np.std(mkt[i-5:i]))
                if rv > 2.0 * max(baseline_vol, 0.01):
                    disorder_mask[i] = True
        else:
            # No market data — use rolling 10d drawdown of stock itself
            disorder_mask = np.zeros(n, dtype=bool)
            baseline_vol = float(np.std(stock_returns))
            for i in range(10, n):
                segment = stock_returns[i-10:i]
                rv = float(np.std(segment))
                m10 = float(np.sum(segment))
                if m10 < -5.0 or rv > 2.5 * max(baseline_vol, 0.01):
                    disorder_mask[i] = True

        # ── Compute conditional means ─────────────────────────────────────────
        disorder_returns = stock_returns[disorder_mask]
        calm_returns     = stock_returns[~disorder_mask]

        disorder_mean = float(np.mean(disorder_returns)) if len(disorder_returns) > 2 else 0.0
        calm_mean     = float(np.mean(calm_returns))     if len(calm_returns) > 2 else 0.0

        antifragile_bonus = disorder_mean - calm_mean
        disorder_periods  = int(np.sum(disorder_mask))

        # ── Classification (Taleb taxonomy in Tralse terms) ──────────────────
        if antifragile_bonus > 0.3:
            classification = "antifragile"    # gains from disorder > threshold
        elif antifragile_bonus > -0.3:
            classification = "resilient"      # roughly neutral in disorder
        else:
            classification = "fragile"        # hurt by disorder

        tralse_resolved = antifragile_bonus > 0.0   # any positive = MR in progress

        return AntifragileScore(
            antifragile_bonus=float(antifragile_bonus),
            disorder_periods=disorder_periods,
            calm_mean=float(calm_mean),
            disorder_mean=float(disorder_mean),
            classification=classification,
            tralse_resolved=tralse_resolved
        )

    # ── Candidate Ranking ─────────────────────────────────────────────────────

    def rank_candidates(
        self,
        candidates: List[Tuple[str, Signal]],
        antifragile_scores: Optional[Dict[str, AntifragileScore]] = None
    ) -> List[Tuple[str, Signal, float]]:
        """
        Rank by composite score: GILE + PD + tradeable bonus + antifragile bonus.

        Antifragile bonus (URB #466): among green-light stocks, prefer those that
        historically perform BETTER during disorder that kills weaker companies.
        The energy majors (COP, CVX, XOM) demonstrated this: +10–12% during
        geopolitical supply disruption that was general market disorder.
        """
        scored = []
        for symbol, signal in candidates:
            af_bonus = 0.0
            if antifragile_scores and symbol in antifragile_scores:
                af = antifragile_scores[symbol]
                if af.classification == "antifragile":
                    af_bonus = float(np.clip(af.antifragile_bonus * 0.05, 0.0, 0.12))
                elif af.classification == "fragile":
                    af_bonus = float(np.clip(af.antifragile_bonus * 0.05, -0.10, 0.0))

            score = (
                (signal.gile - 0.5) +
                0.25 * signal.xi_metrics.pd +
                0.10 * np.tanh(signal.xi_metrics.xi_signed) +
                (0.15 if signal.tradeable else 0.0) +   # Dual-confidence bonus
                af_bonus                                 # Antifragile Tralse bonus
            )
            scored.append((symbol, signal, float(score)))
        scored.sort(key=lambda x: x[2], reverse=True)
        return scored

    # ── Position Sizing ───────────────────────────────────────────────────────

    def calculate_position_size(
        self,
        signal:        "Signal",
        regime:        MarketRegime,
        max_position:  float = 0.15,
        num_positions: int   = 4,
        pd_dist:       Optional[PDDistribution] = None,
        hem_score:      Optional[EVScore] = None,
    ) -> float:
        """
        UOP-guided position sizing (v3 — Unified Optimization Principle).

        The UOP optimizes across ALL GILE + EV dimensions simultaneously.
        Position size reflects not just directional confidence (EC/EpC) but
        the full multi-dimensional coherence of the trade:

          UOP composite = 0.35 × GILE_composite
                        + 0.25 × HEM-Score (Holistic Existence Score)
                        + 0.20 × PD_tt_weight (True-Tralse confirmation)
                        + 0.20 × (1 - PD_dt_weight) (absence of DT)

        Overrides:
          - DT gate active (dt_weight > 0.35): reduce to 25% of base
          - EV-decoupled: reduce to 60% of base (structural watch)
          - Tral-state: reduce to 50% of base (exploratory, not validated)
          - GEOMETRIC regime: 0% (already filtered upstream)
        """
        regime_scale = self.regime_adj.get(regime, 1.0)
        base_weight  = min(max_position, 1.0 / num_positions) * regime_scale

        # UOP composite score
        gile_comp  = signal.gile
        esv        = hem_score.esv if hem_score else 0.5
        tt_w       = pd_dist.tt_weight if pd_dist else 0.5
        dt_w       = pd_dist.dt_weight if pd_dist else 0.0

        uop_composite = float(np.clip(
            0.35 * gile_comp +
            0.25 * esv +
            0.20 * tt_w +
            0.20 * (1.0 - dt_w),
            0.0, 1.0
        ))

        weight = base_weight * uop_composite

        # Override gates (applied multiplicatively, most conservative wins)
        if pd_dist and pd_dist.dt_gate_active:
            weight *= 0.25   # DT gate: near-zero position, MR Level-1 block
        elif hem_score and hem_score.ev_decoupled:
            weight *= 0.60   # EV-decoupled: reduce exposure, structural watch
        elif signal.tral_state:
            weight *= 0.50   # Tral-state: half-size exploratory position

        return float(np.clip(weight, 0.0, max_position))

    # ── TIL Pipeline: EVScore, PDDistribution, MR ──────────────────────────────

    def compute_hem_score(
        self,
        prices: np.ndarray,
        returns: np.ndarray,
        gile: GILEScore,
    ) -> EVScore:
        """
        Compute EVScore — HEM Dimensions for a stock.
        Models the BOK outer loops: the stock's 'existence' in the market.

        HEM-D1 Physical/Energetic:    Volume-weighted price stability proxy
                                     → uses constraint (drawdown + vol ratio)
        HEM-D2 Social/Historical:     52-week high position proxy
                                     → prices[-1] / max(prices[-252:])
        HEM-D3 Aesthetic/Structural:  Chart pattern quality
                                     → coherence of trend structure (1/vol_ratio)
        HEM-D4 Conscious/Experiential: Momentum of momentum
                                     → second derivative of short-term trend

        HEM-Score = EAR output: weighted FDE mean (EAR amplifies what genuinely exists,
        prunes superficial distinctions — Law of Realness from URB #615).
        EV-decoupled: |HEM-Score - GILE_composite| > 0.35
        """
        n = len(prices)
        if n < 30:
            return EVScore(0.5, 0.5, 0.5, 0.5, 0.5, False)

        # HEM-D1: Physical/Energetic — inverse of constraint (low drawdown+vol = high stability)
        c = self._constraint(prices, returns)
        fde1 = float(np.clip(1.0 - c, 0.0, 1.0))

        # HEM-D2: Social/Historical — 52W position proxy
        lookback_52w = min(n, 252)
        price_max_52w = float(np.max(prices[-lookback_52w:]))
        price_min_52w = float(np.min(prices[-lookback_52w:]))
        price_range = price_max_52w - price_min_52w
        fde2 = float(np.clip(
            (prices[-1] - price_min_52w) / max(price_range, 0.01),
            0.0, 1.0
        ))

        # HEM-D3: Aesthetic/Structural — chart pattern coherence
        # (Low short/long vol ratio = cleaner chart = higher structural quality)
        rs = returns[-min(n, 7):]
        rl = returns[-min(n, 30):]
        v_short = max(float(np.std(rs)), 0.001)
        v_long  = max(float(np.std(rl)), 0.001)
        vol_ratio = v_short / v_long
        fde3 = float(np.clip(1.0 / (1.0 + abs(vol_ratio - 1.0)), 0.0, 1.0))

        # HEM-D4: Conscious/Experiential — momentum of momentum (second derivative)
        if len(returns) >= 10:
            mom_recent = float(np.mean(returns[-5:]))
            mom_prior  = float(np.mean(returns[-10:-5]))
            mom_accel  = mom_recent - mom_prior
            # Sigmoid: positive acceleration = high HEM-D4
            fde4 = float(1.0 / (1.0 + np.exp(-mom_accel * 20.0)))
        else:
            fde4 = 0.5

        # HEM-Score = EAR output: amplify what genuinely exists
        # Weights: HEM-D1 (stability) 0.25, HEM-D2 (history) 0.25,
        #          HEM-D3 (structure) 0.30, HEM-D4 (acceleration) 0.20
        esv = float(np.clip(
            0.25 * fde1 + 0.25 * fde2 + 0.30 * fde3 + 0.20 * fde4,
            0.0, 1.0
        ))

        # EV-decoupled: Holistic Existence Matrix and GILE are diverging
        ev_decoupled = abs(esv - gile.composite) > 0.35

        return EVScore(
            fde1_physical=float(fde1),
            fde2_social=float(fde2),
            fde3_aesthetic=float(fde3),
            fde4_conscious=float(fde4),
            esv=float(esv),
            ev_decoupled=ev_decoupled,
        )

    def compute_pd_distribution(
        self,
        xi_metrics:  XiMetrics,
        gile:        GILEScore,
        ev:          EVScore,
        bifurcation: BifurcationResult,
    ) -> PDDistribution:
        """
        Compute PDDistribution — 5-state market truth distribution (TIL/PD).

        MR three-level pipeline (URB #615, #618):
          Level 1 (DT screen): Flag if vol spike + negative memory + bifurcation
          Level 2 (GILE-EV):   Weight TT/TI/TF by both GILE composite and HEM-Score
          Level 3 (convergence): Resolve if dominant > 0.45; derive TIL action

        Truth-state construction:
          TT  (True-Tralse):          GILE high + HEM-Score high + positive PD
          TI  (Tralse-Indeterminate): Near-threshold GILE or high bifurcation
          TF  (Tralse-False):         GILE low or strong negative momentum
          DT  (Double-Tralse):        Volatility spike + negative memory dominant
          EV  (EV-Decoupled):         GILE and HEM-Score diverge significantly
        """
        MR_THRESHOLD = 0.45  # minimum dominant weight for mr_resolved = True
        DT_GATE      = 0.35  # DT weight above this → pause (MR Level-1 gate)

        pd_val   = xi_metrics.pd           # scalar PD in [-3, +2]
        g_comp   = gile.composite          # GILE composite [0,1]
        esv      = ev.esv                  # Existence Scalar Value [0,1]
        kappa    = xi_metrics.memory_kernel  # negative memory dominance [0,1]
        in_bif   = bifurcation.in_bifurcation
        crossed  = bifurcation.crossing_detected
        amp      = xi_metrics.xi_unsigned

        # ── Level 1: DT seed — absence of tradeable truth ──────────────────
        # DT arises when: high negative memory + vol spike + structural fracture
        dt_raw = float(np.clip(
            0.40 * kappa +
            0.30 * float(np.clip(amp - 1.0, 0.0, 1.0)) +   # vol spike
            0.30 * (0.80 if in_bif and xi_metrics.xi_signed < -1.0 else 0.0),
            0.0, 1.0
        ))

        # ── Level 2: HEM-GILE integration ───────────────────────────────────
        # TT weight: GILE composite + positive PD + HEM-Score all supporting
        pd_pos = float(np.clip(pd_val / 2.0, 0.0, 1.0))   # normalize PD to [0,1]
        pd_neg = float(np.clip(-pd_val / 3.0, 0.0, 1.0))  # normalize neg PD

        tt_raw = float(np.clip(
            0.40 * g_comp +
            0.35 * pd_pos +
            0.25 * esv,
            0.0, 1.0
        ))

        # TF weight: inverse GILE + negative PD + high negative memory
        tf_raw = float(np.clip(
            0.35 * (1.0 - g_comp) +
            0.35 * pd_neg +
            0.30 * float(np.clip(kappa - 0.5, 0.0, 1.0)),
            0.0, 1.0
        ))

        # TI weight: near-threshold GILE + bifurcation uncertainty
        tralse_zone = float(np.clip(
            1.0 - 2.0 * abs(g_comp - 0.50),   # peaks at GILE = 0.5
            0.0, 1.0
        ))
        ti_raw = float(np.clip(
            0.50 * tralse_zone +
            0.30 * (0.80 if in_bif else 0.0) +
            0.20 * (0.60 if crossed else 0.0),
            0.0, 1.0
        ))

        # EV weight: existence decoupling
        ev_gap = abs(esv - g_comp)
        ev_raw = float(np.clip(ev_gap / 0.5, 0.0, 1.0))  # normalized: gap > 0.50 → max

        # ── Level 3: Normalize and converge ───────────────────────────────
        total = tt_raw + ti_raw + tf_raw + dt_raw + ev_raw
        if total < 1e-6:
            total = 1.0
        tt = tt_raw / total
        ti = ti_raw / total
        tf = tf_raw / total
        dt = dt_raw / total
        ev = ev_raw / total

        # Resolve dominant state
        state_names  = ["TT", "TI", "TF", "DT", "EV"]
        state_weights = [tt, ti, tf, dt, ev]
        dom_idx  = int(np.argmax(state_weights))
        dominant = state_names[dom_idx]
        dom_w    = state_weights[dom_idx]

        mr_resolved = dom_w > MR_THRESHOLD

        # TIL action from MR:
        #   Level-1 gate (DT screen): dt > DT_GATE → pause regardless
        if dt > DT_GATE:
            til_action = "pause"
        elif dominant == "TT" and mr_resolved:
            til_action = "buy" if tt < 0.70 else "strong_buy"
        elif dominant == "TF" and mr_resolved:
            til_action = "sell" if tf < 0.70 else "strong_sell"
        elif dominant == "TI":
            til_action = "hold"
        elif dominant == "EV":
            til_action = "watch"   # structural watch: EV divergence noted
        else:
            til_action = "hold"    # unresolved MR → conservative default

        return PDDistribution(
            tt_weight=round(tt, 4),
            ti_weight=round(ti, 4),
            tf_weight=round(tf, 4),
            dt_weight=round(dt, 4),
            ev_weight=round(ev, 4),
            dominant=dominant,
            mr_resolved=mr_resolved,
            til_action=til_action,
        )

    def run_til(
        self,
        returns: np.ndarray,
        prices:  np.ndarray,
        market_returns: Optional[np.ndarray] = None,
    ) -> Tuple["Signal", EVScore, PDDistribution]:
        """
        Run the full TIL pipeline (Tralse-Myrion Logic).

        Pipeline: Ξ(E) → GILE → EV → PD → MR → Signal
          1. Compute Xi metrics (Existence Intensity)
          2. Compute GILE score (BOK inner loops)
          3. Compute HEM score  (BOK outer loops)
          4. Inject EV composite into GILE for UOP scoring
          5. Classify BOK regime
          6. Compute PD distribution (5-state truth assignment)
          7. MR Level-1 DT gate: if DT active, override to 'pause'
          8. Generate signal with UOP position sizing

        The UOP (guiding principle) operates throughout: every computation
        optimizes across ALL GILE + EV dimensions simultaneously.

        Returns: (Signal, EVScore, PDDistribution)
        """
        # Step 1: Xi metrics
        xi = self.compute_xi_metrics(returns, prices)

        # Step 2: GILE (BOK inner loops)
        gile = self.compute_gile(returns, prices, market_returns)

        # Step 3: EV (BOK outer loops)
        hem_score = self.compute_hem_score(prices, returns, gile)

        # Step 4: Inject EV composite into GILEScore for UOP scoring
        gile.ev_composite = hem_score.esv

        # Step 5: BOK regime
        vol_ratio = 1.0
        if len(returns) >= self.lookback_long:
            v_short = max(float(np.std(returns[-self.lookback_short:])), 0.001)
            v_long  = max(float(np.std(returns[-self.lookback_long:])), 0.001)
            vol_ratio = v_short / v_long
        regime, regime_conf, _ = self.classify_regime(xi.pd, xi.xi_unsigned, vol_ratio)

        # Step 6: PD distribution (MR input)
        bif = self.detect_bifurcation(self.constraint_history)
        pd_dist = self.compute_pd_distribution(xi, gile, hem_score, bif)

        # Step 7: Generate signal (with MR DT-gate override)
        signal = self.generate_signal(xi, gile, regime, regime_conf, bif)

        # MR Level-1 override: DT gate active → pause regardless of GILE signal
        if pd_dist.dt_gate_active and signal.action in ("buy", "strong_buy"):
            signal.action = "hold"
            signal.ec = float(np.clip(signal.ec * 0.40, 0.0, 1.0))
            signal.reasons.append(
                f"MR DT-gate: dt_weight={pd_dist.dt_weight:.3f} > 0.35 — signal muted"
            )

        # EV-decoupled watch note
        if hem_score.ev_decoupled:
            signal.reasons.append(
                f"EV-decoupled: HEM-Score={hem_score.esv:.3f} vs GILE={gile.composite:.3f} "
                f"(Δ={abs(hem_score.esv - gile.composite):.3f}) — structural watch"
            )

        return signal, hem_score, pd_dist

    # ── Fractal Enhancement ───────────────────────────────────────────────────

    def enhance_with_fractal(self, prices: np.ndarray, existing_signal: Signal) -> Signal:
        """Enhance signal with Fractal Universe analysis (Hurst + Kleiber)."""
        try:
            from fractal_universe_engine import FractalMarketAnalyzer
            analyzer = FractalMarketAnalyzer()
            prices_list = prices.tolist() if hasattr(prices, "tolist") else list(prices)
            if len(prices_list) < 30:
                return existing_signal
            third   = len(prices_list) // 3
            fractal = analyzer.multi_scale_prediction(
                prices_list[-third:],
                prices_list[-2*third:],
                prices_list
            )
            hurst     = fractal.get("weighted_hurst", 0.5)
            coherence = fractal.get("scale_coherence", 0.5)
            boost = 0.0
            if abs(hurst - 0.75) < 0.1: boost += 0.08
            if coherence > 0.7:          boost += 0.05
            direction = fractal.get("direction", "NEUTRAL")
            aligned = (
                (direction in ("BULLISH", "STRONGLY_BULLISH") and existing_signal.action in ("buy", "strong_buy")) or
                (direction in ("BEARISH", "STRONGLY_BEARISH") and existing_signal.action in ("sell", "strong_sell"))
            )
            if aligned: boost += 0.08
            new_reasons = existing_signal.reasons + [f"Fractal: H={hurst:.3f}, Coh={coherence:.3f}"]
            return Signal(
                action=existing_signal.action,
                ec=float(np.clip(existing_signal.ec + boost, 0.0, 1.0)),
                epc=existing_signal.epc,
                tral_state=existing_signal.tral_state,
                gile=existing_signal.gile,
                xi_metrics=existing_signal.xi_metrics,
                regime=existing_signal.regime,
                bifurcation=existing_signal.bifurcation,
                reasons=new_reasons
            )
        except Exception:
            return existing_signal
