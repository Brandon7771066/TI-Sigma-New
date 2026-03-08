"""
GSA CORE ENGINE v2 — TI Sigma BOK Architecture
================================================
Grand Stock Algorithm — Existence Intensity Framework
Ξ(E) = A(t) · κ(t,τ) · C(t) → PD → GILE → Signal

v2 Upgrades (March 2026):
  - Emerick Constant C_EMERICK = 1/(φ√2) ≈ 0.4370 as primary threshold
  - Extended Euler normalization: e^(iπ) + √2·φ·C = 0
  - BOK 8-Mode regime classification (4 primary + 4 interface)
  - Theorem A: Attractor basin bifurcation detection
  - Dual-Confidence Principle: EC (exploratory) + EpC (epistemic)
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
    """Four-dimensional GILE assessment"""
    goodness:    float   # G — risk-adjusted returns
    intuition:   float   # I — trend alignment
    love:        float   # L — market correlation
    environment: float   # E — momentum alignment
    composite:   float   # Weighted combination [0,1]


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
        if len(self.pd_history) >= 10:
            pd_std = float(np.std(self.pd_history[-10:]))
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

    # ── Candidate Ranking ─────────────────────────────────────────────────────

    def rank_candidates(
        self,
        candidates: List[Tuple[str, Signal]]
    ) -> List[Tuple[str, Signal, float]]:
        """Rank by composite score: GILE + PD + tradeable bonus."""
        scored = []
        for symbol, signal in candidates:
            score = (
                (signal.gile - 0.5) +
                0.25 * signal.xi_metrics.pd +
                0.10 * np.tanh(signal.xi_metrics.xi_signed) +
                (0.15 if signal.tradeable else 0.0)    # Dual-confidence bonus
            )
            scored.append((symbol, signal, float(score)))
        scored.sort(key=lambda x: x[2], reverse=True)
        return scored

    # ── Position Sizing ───────────────────────────────────────────────────────

    def calculate_position_size(
        self,
        signal:        Signal,
        regime:        MarketRegime,
        max_position:  float = 0.15,
        num_positions: int   = 4
    ) -> float:
        """
        Position size using Dual-Confidence + BOK regime multiplier.
        Tral-state signals get half-size (directional but not validated).
        """
        regime_scale = self.regime_adj.get(regime, 1.0)
        base_weight  = min(max_position, 1.0 / num_positions) * regime_scale

        # Use composite confidence for sizing
        weight = base_weight * signal.confidence

        # Tral-state: half size — respect the exploratory direction but stay cautious
        if signal.tral_state:
            weight *= 0.50

        return float(np.clip(weight, 0.0, max_position))

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
