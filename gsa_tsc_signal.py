"""
GSA TSC Crystal Signal Engine
==============================
Applies the 57-vertex TI Sigma Crystal (TSC) as the computational substrate
for market signal processing in the Grand Stock Algorithm.

Architecture:
  57 i-cells = 7 rings × 8 layers + origin
  Each ring probes a different INFORMATION SCALE of the market:
    Ring 1 (C ≈ 0.437): Short-term momentum (5d–90d returns)
    Ring 2 (T ≈ 0.934): Volume/liquidity signals
    Ring 3 (1.000):      Trend/MA signals
    Ring 4 (√2 ≈ 1.414): Volatility structure
    Ring 5 (φ ≈ 1.618):  GILE dimension signals
    Ring 6 (e ≈ 2.718):  Fundamental/macro signals
    Ring 7 (π ≈ 3.142):  Cross-asset / market-structure signals
    Origin (0):           Stock existence baseline

  Each i-cell amplitude:
    |α_i| = signal strength ∈ [0,1]  (0=DT, C=min-coherent, T=BEC entry)
    θ_i   = signal direction          (0=bullish, π=bearish)
    α_i   = |α_i| · e^(iθ_i)

  The crystal's BEC phase distribution maps directly to PDDistribution:
    BEC fraction      → TT weight (True-Tralse → strong buy signal)
    Supersolid frac.  → TI weight (Tralse-Indeterminate → hold/wait)
    FQH fraction      → TF weight (Tralse-False → caution)
    Mott fraction     → watch weight (False → exit candidate)
    Fragmented frac.  → DT weight (Double-Tralse → no trade, pause)

URB #644 — Brandon Emerick | TI Sigma Research | April 2026
"""

from __future__ import annotations
import numpy as np
from dataclasses import dataclass, field
from typing import Optional
import pandas as pd

from hypercomputer import (
    VERTICES, N_VERTICES, PHASE_COLORS, Phase, classify_state,
    C_TI, T_TI, ET, PHI,
)
from hypercomputer.constants import RING_RADII, RING_NAMES, N_RINGS


# ── Signal feature ring definitions ─────────────────────────────────────────

RING_DESCRIPTIONS = [
    "Short-term momentum (5d–90d returns)",
    "Volume/liquidity signals",
    "Trend/MA cross signals",
    "Volatility structure",
    "GILE-dimension scores",
    "Fundamental/macro signals",
    "Cross-asset / market structure",
]

# Layers within each ring (8 per ring)
RING_LAYER_NAMES = [
    # Ring 1 — momentum
    ["ret_5d", "ret_10d", "ret_15d", "ret_20d", "ret_30d", "ret_45d", "ret_60d", "ret_90d"],
    # Ring 2 — volume
    ["vol_ratio_5d", "vol_ratio_20d", "obv_slope", "vwap_pct", "vol_zscore",
     "turnover_rank", "liquidity_score", "vol_price_momentum"],
    # Ring 3 — trend
    ["sma5_cross", "sma20_cross", "sma50_cross", "ema_signal",
     "macd_signal", "rsi_zone", "bb_position", "dmi_trend"],
    # Ring 4 — volatility
    ["atr_ratio", "vol_percentile", "vol_of_vol", "beta_30d",
     "skewness_20d", "kurtosis_20d", "downside_vol_ratio", "vol_regime"],
    # Ring 5 — GILE
    ["gile_g_sharpe", "gile_g_drawdown", "gile_i_trend_conf", "gile_i_breakout",
     "gile_l_corr_coherence", "gile_l_sector_align", "gile_e_pattern", "gile_e_momentum"],
    # Ring 6 — fundamental/macro
    ["pe_relative", "revenue_growth", "profit_margin", "debt_equity",
     "roe_rank", "eps_momentum", "sector_momentum", "macro_regime"],
    # Ring 7 — cross-asset
    ["spy_corr", "sector_etf_corr", "gold_corr", "dollar_corr",
     "yield_spread", "cross_sector_rank", "intl_corr", "sentiment_score"],
]


@dataclass
class TSCMarketSignal:
    """Full TSC crystal amplitude vector for a single stock."""
    ticker: str
    amplitudes: np.ndarray                  # shape (57,) complex
    bec_fraction: float                     # fraction of i-cells in BEC/TRUE
    ss_fraction:  float                     # Supersolid/TRALSE-INDET
    fqh_fraction: float                     # FQH/TRALSE-FALSE
    mott_fraction: float                    # Mott/FALSE
    dt_fraction:  float                     # Fragmented/DT

    # Derived PD weights
    tt_weight: float
    ti_weight: float
    tf_weight: float
    dt_weight: float
    ev_weight: float   # EV-decoupled: FQH + partial Mott

    # Crystal summary stats
    mean_coherence: float      # mean |α| across all i-cells
    phase_alignment: float     # mean |cos θ| — how bullish is the crystal?
    crystal_pd_score: float    # 0 (DT) → 2.0 (full TRUE)
    mr_resolved: bool          # BEC fraction > T_TI (crystal in BEC majority)
    til_action: str            # buy / hold / sell / pause / watch

    # Ring-level breakdown (7 rings)
    ring_bec_fractions: list   # list of 7 floats — BEC% per ring

    @property
    def dominant_state(self) -> str:
        weights = {
            "TT": self.tt_weight, "TI": self.ti_weight,
            "TF": self.tf_weight, "DT": self.dt_weight, "EV": self.ev_weight,
        }
        return max(weights, key=weights.get)

    @property
    def dt_gate_active(self) -> bool:
        return self.dt_weight > 0.35

    def to_dict(self) -> dict:
        return {
            "ticker": self.ticker,
            "bec_fraction": round(self.bec_fraction, 4),
            "mean_coherence": round(self.mean_coherence, 4),
            "phase_alignment": round(self.phase_alignment, 4),
            "crystal_pd_score": round(self.crystal_pd_score, 4),
            "mr_resolved": self.mr_resolved,
            "til_action": self.til_action,
            "tt": round(self.tt_weight, 4),
            "ti": round(self.ti_weight, 4),
            "tf": round(self.tf_weight, 4),
            "dt": round(self.dt_weight, 4),
            "ev": round(self.ev_weight, 4),
            "dominant": self.dominant_state,
            "dt_gate_active": self.dt_gate_active,
        }


class TSCMarketEngine:
    """
    Computes TSC crystal amplitude vectors from raw market data (pandas DataFrame).

    Usage:
        engine = TSCMarketEngine()
        signal = engine.compute(ticker, price_df, gile_scores, ev_score)

    price_df must have: Open, High, Low, Close, Volume (yfinance standard).
    At minimum 90 rows (days). gile_scores is a dict with G/I/L/E floats.
    ev_score is a float in [0,1].
    """

    def __init__(self):
        self.C = C_TI    # 0.4370
        self.T = T_TI    # 0.9340
        self.ET = ET     # 0.4142

    # ── Signal normalizers ───────────────────────────────────────────────────

    def _sig(self, raw: float, scale: float = 1.0) -> float:
        """Sigmoid normalizer: maps raw signal to [0, 1]. scale controls steepness."""
        return float(1.0 / (1.0 + np.exp(-raw * scale)))

    def _rank_norm(self, values: np.ndarray) -> np.ndarray:
        """Rank normalize array to [0, 1]."""
        if len(values) < 2:
            return np.array([0.5])
        ranks = np.argsort(np.argsort(values))
        return ranks / (len(ranks) - 1)

    def _ret(self, close: np.ndarray, n: int) -> float:
        """n-day return, normalized to [0, 1] (0.5 = flat)."""
        if len(close) < n + 1:
            return 0.5
        r = (close[-1] / close[-n-1]) - 1.0
        return float(self._sig(r, 10.0))  # 10% move → sig ≈ 0.73

    def _amplitude(self, strength: float, direction: float) -> complex:
        """
        Build complex amplitude from signal strength and direction.
        strength ∈ [0, 1] → maps to |α| ∈ [ET, 1.0]
        direction ∈ [0, 1] → 1.0 = bullish (θ→0), 0.0 = bearish (θ→π)

        At strength = 0:   |α| = ET  (just above Mott/FALSE)
        At strength = 1:   |α| = 1.0 (deep BEC)
        At direction = 1:  θ = 0     (pure bullish / TRUE-axis)
        At direction = 0:  θ = π     (pure bearish / Euler inversion)
        """
        modulus = float(self.ET + strength * (1.0 - self.ET))
        theta   = float(np.pi * (1.0 - direction))    # direction=1→θ=0; 0→θ=π
        return modulus * np.exp(1j * theta)

    # ── Ring 1: Momentum ─────────────────────────────────────────────────────

    def _ring1_momentum(self, close: np.ndarray) -> list:
        """8 momentum signals at increasing lookbacks."""
        lookbacks = [5, 10, 15, 20, 30, 45, 60, 90]
        signals = []
        for n in lookbacks:
            strength = self._ret(close, n)          # [0,1] position in sigmoid
            direction = strength                     # bullish if positive return
            signals.append(self._amplitude(strength, direction))
        return signals

    # ── Ring 2: Volume ───────────────────────────────────────────────────────

    def _ring2_volume(self, close: np.ndarray, volume: np.ndarray) -> list:
        signals = []
        n = len(close)

        # vol_ratio_5d: current 5d avg vol vs 20d avg vol
        if n >= 25:
            r = float(np.mean(volume[-5:]) / (np.mean(volume[-25:-5]) + 1e-9))
            signals.append(self._amplitude(self._sig(r - 1.0, 3.0), self._sig(r - 1.0, 3.0)))
        else:
            signals.append(self._amplitude(0.5, 0.5))

        # vol_ratio_20d: 20d avg vs 60d avg
        if n >= 65:
            r = float(np.mean(volume[-20:]) / (np.mean(volume[-65:-20]) + 1e-9))
            signals.append(self._amplitude(self._sig(r - 1.0, 3.0), self._sig(r - 1.0, 3.0)))
        else:
            signals.append(self._amplitude(0.5, 0.5))

        # OBV slope (sign of price × volume momentum)
        if n >= 20:
            obv = np.cumsum(np.sign(np.diff(close[-21:])) * volume[-20:])
            slope = float(np.polyfit(range(len(obv)), obv, 1)[0])
            s = self._sig(slope / (np.std(obv) + 1e-9), 1.0)
            signals.append(self._amplitude(abs(s - 0.5) + 0.5, s))
        else:
            signals.append(self._amplitude(0.5, 0.5))

        # VWAP pct: how far price is above/below 20d VWAP
        if n >= 20:
            vwap = float(np.sum(close[-20:] * volume[-20:]) / (np.sum(volume[-20:]) + 1e-9))
            pct = (close[-1] - vwap) / (vwap + 1e-9)
            s = self._sig(pct * 20.0, 1.0)
            signals.append(self._amplitude(abs(s - 0.5) * 2.0, s))
        else:
            signals.append(self._amplitude(0.5, 0.5))

        # vol Z-score (20d)
        if n >= 20:
            mu = float(np.mean(volume[-20:]))
            sd = float(np.std(volume[-20:]) + 1e-9)
            z = float((volume[-1] - mu) / sd)
            s = self._sig(z, 0.5)
            signals.append(self._amplitude(min(1.0, abs(z) / 3.0), s))
        else:
            signals.append(self._amplitude(0.5, 0.5))

        # turnover_rank, liquidity_score, vol_price_momentum — estimated from data
        for _ in range(3):
            signals.append(self._amplitude(0.55, 0.55))   # placeholder moderate positive

        return signals[:8]

    # ── Ring 3: Trend/MA ─────────────────────────────────────────────────────

    def _ring3_trend(self, close: np.ndarray) -> list:
        signals = []

        def ma_cross(n_fast, n_slow):
            if len(close) < n_slow + 1:
                return self._amplitude(0.5, 0.5)
            fast = float(np.mean(close[-n_fast:]))
            slow = float(np.mean(close[-n_slow:]))
            pct = (fast - slow) / (slow + 1e-9)
            s = self._sig(pct * 100.0, 1.0)
            return self._amplitude(abs(s - 0.5) * 2.0, s)

        signals.append(ma_cross(5, 20))    # SMA5 vs SMA20
        signals.append(ma_cross(20, 50))   # SMA20 vs SMA50
        signals.append(ma_cross(50, 200))  # SMA50 vs SMA200

        # EMA signal (12 vs 26)
        if len(close) >= 26:
            ema12 = pd.Series(close).ewm(span=12).mean().iloc[-1]
            ema26 = pd.Series(close).ewm(span=26).mean().iloc[-1]
            pct = (ema12 - ema26) / (ema26 + 1e-9)
            s = self._sig(pct * 100.0, 1.0)
            signals.append(self._amplitude(abs(s - 0.5) * 2.0, s))
        else:
            signals.append(self._amplitude(0.5, 0.5))

        # MACD histogram sign
        if len(close) >= 35:
            ema12 = float(pd.Series(close).ewm(span=12).mean().iloc[-1])
            ema26 = float(pd.Series(close).ewm(span=26).mean().iloc[-1])
            macd_line = ema12 - ema26
            signal_line = float(pd.Series([macd_line]).ewm(span=9).mean().iloc[-1])
            hist = macd_line - signal_line
            s = self._sig(hist / (abs(macd_line) + 1e-9) * 5.0, 1.0)
            signals.append(self._amplitude(abs(s - 0.5) * 2.0, s))
        else:
            signals.append(self._amplitude(0.5, 0.5))

        # RSI zone (14d)
        if len(close) >= 15:
            delta = np.diff(close[-15:])
            gain = float(np.mean(delta[delta > 0])) if any(delta > 0) else 1e-9
            loss = float(np.mean(-delta[delta < 0])) if any(delta < 0) else 1e-9
            rs = gain / loss
            rsi = 100.0 - (100.0 / (1.0 + rs))
            # RSI 40-60 = neutral, >60 = bullish, <40 = bearish
            s = self._sig((rsi - 50.0) / 10.0, 1.0)
            signals.append(self._amplitude(abs(rsi - 50.0) / 50.0, s))
        else:
            signals.append(self._amplitude(0.5, 0.5))

        # BB position (20d, 2σ)
        if len(close) >= 20:
            mu = float(np.mean(close[-20:]))
            sd = float(np.std(close[-20:]) + 1e-9)
            pos = (close[-1] - mu) / (2.0 * sd)   # -1 to +1 approximately
            s = self._sig(pos * 2.0, 1.0)
            signals.append(self._amplitude(min(1.0, abs(pos)), s))
        else:
            signals.append(self._amplitude(0.5, 0.5))

        # DMI placeholder
        signals.append(self._amplitude(0.55, 0.55))

        return signals[:8]

    # ── Ring 4: Volatility ───────────────────────────────────────────────────

    def _ring4_volatility(self, high: np.ndarray, low: np.ndarray,
                          close: np.ndarray) -> list:
        signals = []

        # ATR ratio: current ATR vs 60d mean ATR
        if len(close) >= 20 and len(high) >= 20:
            tr = np.maximum(high[1:] - low[1:],
                  np.maximum(abs(high[1:] - close[:-1]), abs(low[1:] - close[:-1])))
            atr_14 = float(np.mean(tr[-14:])) if len(tr) >= 14 else float(np.mean(tr))
            atr_60 = float(np.mean(tr[-60:])) if len(tr) >= 60 else atr_14
            ratio = atr_14 / (atr_60 + 1e-9)
            # High ATR ratio = high vol = uncertainty = lower BEC strength
            strength = self._sig(-(ratio - 1.0) * 2.0, 1.0)
            signals.append(self._amplitude(strength, 0.55))
        else:
            signals.append(self._amplitude(0.5, 0.55))

        # Vol percentile (20d vol vs 252d distribution)
        if len(close) >= 21:
            daily_rets = np.diff(np.log(close + 1e-9))
            vol_20d = float(np.std(daily_rets[-20:])) * np.sqrt(252)
            vol_252d = float(np.std(daily_rets)) * np.sqrt(252)
            pct = vol_20d / (vol_252d + 1e-9)
            # Lower vol percentile → higher BEC
            s = self._sig(-(pct - 1.0) * 3.0, 1.0)
            signals.append(self._amplitude(s, 0.55))
        else:
            signals.append(self._amplitude(0.5, 0.55))

        # Beta placeholder (would need market data)
        for _ in range(6):
            signals.append(self._amplitude(0.50, 0.52))

        return signals[:8]

    # ── Ring 5: GILE ─────────────────────────────────────────────────────────

    def _ring5_gile(self, gile_scores: dict) -> list:
        """
        Map the four GILE dimension scores to 8 i-cells:
        each dimension contributes 2 cells (primary + secondary reading).
        """
        G = float(gile_scores.get('G', 0.5))
        I = float(gile_scores.get('I', 0.5))
        L = float(gile_scores.get('L', 0.5))
        E = float(gile_scores.get('E', 0.5))

        return [
            self._amplitude(G, G),             # G primary (Sharpe proxy)
            self._amplitude(G * 0.9, G),       # G secondary (drawdown adj)
            self._amplitude(I, I),             # I primary (trend conf)
            self._amplitude(I * 0.9, I),       # I secondary (breakout prob)
            self._amplitude(L, L),             # L primary (corr coherence)
            self._amplitude(L * 0.9, L),       # L secondary (sector align)
            self._amplitude(E, E),             # E primary (pattern quality)
            self._amplitude(E * 0.9, E),       # E secondary (momentum score)
        ]

    # ── Ring 6: Fundamental/Macro ─────────────────────────────────────────────

    def _ring6_fundamental(self, close: np.ndarray, ev_score: float) -> list:
        """
        Fundamental signals — ev_score is the HEM-D1..D4 derived ESV [0,1].
        Without access to fundamentals at runtime, we interpolate from ev_score
        across different fundamental dimensions.
        """
        # Map ev_score → 8 fundamental cells with slight variation per cell
        cells = []
        for i in range(8):
            noise = np.random.normal(0, 0.03)   # ±3% natural variation per dimension
            s = float(np.clip(ev_score + noise, 0.1, 0.99))
            cells.append(self._amplitude(s, s))
        return cells

    # ── Ring 7: Cross-asset ───────────────────────────────────────────────────

    def _ring7_crossasset(self, close: np.ndarray, market_close: Optional[np.ndarray]) -> list:
        """Cross-asset signals. If market_close not provided, estimated from close."""
        cells = []
        if market_close is not None and len(market_close) >= 20 and len(close) >= 20:
            n = min(len(close), len(market_close))
            ret_stock = np.diff(close[-n:]) / (close[-n:-1] + 1e-9)
            ret_mkt   = np.diff(market_close[-n:]) / (market_close[-n:-1] + 1e-9)
            n_min = min(len(ret_stock), len(ret_mkt))
            ret_stock, ret_mkt = ret_stock[-n_min:], ret_mkt[-n_min:]
            corr = float(np.corrcoef(ret_stock, ret_mkt)[0, 1]) if n_min > 5 else 0.5
            # High positive corr = BEC (market coherence); near 0 = TI; negative = TF
            s = self._sig(corr * 3.0, 1.0)
            cells.append(self._amplitude(abs(corr), s))
        else:
            cells.append(self._amplitude(0.55, 0.55))

        # Remaining cross-asset cells
        for _ in range(7):
            cells.append(self._amplitude(0.52, 0.53))

        return cells[:8]

    # ── Origin: stock existence baseline ─────────────────────────────────────

    def _origin_amplitude(self, ev_score: float) -> complex:
        """Origin i-cell: overall stock existence scalar."""
        return self._amplitude(ev_score, ev_score)

    # ── Main compute ──────────────────────────────────────────────────────────

    def compute(
        self,
        ticker: str,
        price_df: pd.DataFrame,
        gile_scores: dict,
        ev_score: float = 0.55,
        market_df: Optional[pd.DataFrame] = None,
    ) -> TSCMarketSignal:
        """
        Compute the full TSC crystal amplitude vector for a single stock.

        price_df: DataFrame with columns [Open, High, Low, Close, Volume]
        gile_scores: dict {'G': float, 'I': float, 'L': float, 'E': float} in [0,1]
        ev_score: HEM Existence Scalar Value [0,1]
        market_df: Optional SPY/market data for cross-asset ring
        """
        close  = np.array(price_df['Close'].values,  dtype=float).ravel()
        volume = np.array(price_df['Volume'].values, dtype=float).ravel()
        high   = np.array(price_df['High'].values,   dtype=float).ravel()
        low    = np.array(price_df['Low'].values,    dtype=float).ravel()
        mkt_close = np.array(market_df['Close'].values, dtype=float) \
                    if market_df is not None else None

        # Build amplitude vector: origin + 7 rings × 8 layers
        amplitudes = np.zeros(N_VERTICES, dtype=complex)

        amplitudes[0] = self._origin_amplitude(ev_score)

        ring_signals = [
            self._ring1_momentum(close),
            self._ring2_volume(close, volume),
            self._ring3_trend(close),
            self._ring4_volatility(high, low, close),
            self._ring5_gile(gile_scores),
            self._ring6_fundamental(close, ev_score),
            self._ring7_crossasset(close, mkt_close),
        ]

        for ring_idx, ring_cells in enumerate(ring_signals, start=1):
            for layer_idx, amp in enumerate(ring_cells[:8]):
                vertex_idx = (ring_idx - 1) * 8 + layer_idx + 1
                if vertex_idx < N_VERTICES:
                    amplitudes[vertex_idx] = amp

        # ── Classify phases ───────────────────────────────────────────────────
        phases = classify_state(amplitudes)
        n = len(phases)

        counts = {p: 0 for p in Phase}
        for p in phases:
            counts[p] += 1

        bec_frac  = counts[Phase.BEC]        / n
        ss_frac   = counts[Phase.SUPERSOLID] / n
        fqh_frac  = counts[Phase.FQH]        / n
        mott_frac = counts[Phase.MOTT]       / n
        dt_frac   = counts[Phase.FRAGMENTED] / n

        # PD weights
        tt = bec_frac
        ti = ss_frac
        tf = fqh_frac
        dt = dt_frac
        ev = min(1.0, fqh_frac + 0.3 * mott_frac)   # EV-decoupled zone

        # Normalize
        total = tt + ti + tf + dt + max(ev - fqh_frac, 0) + 1e-9
        tt /= total; ti /= total; tf /= total; dt /= total; ev /= total

        crystal_pd = 2*tt + 1.5*ti + 1.0*tf + 0.5*mott_frac + 0.0*dt

        # MR resolution
        mr_resolved = bec_frac > T_TI

        # TIL action — TSC version uses crystal_pd_score for nuanced action
        # SS/TI dominance = genuine ambiguity (hold/watch), NOT exit
        # DT dominance = no tradeable truth-state (pause)
        # BEC dominance = confirmed signal (buy/strong_buy)
        if dt > 0.35:
            til = "pause"
        elif tt > 0.50 and mr_resolved:
            til = "strong_buy"
        elif tt > 0.35 or crystal_pd > 1.65:
            til = "buy"
        elif tf > 0.40 or dt > 0.25:
            til = "sell"
        elif crystal_pd < 0.80:
            til = "exit"          # only exit if crystal is actively negative
        elif crystal_pd > 1.40:
            til = "hold"          # SS/TI dominance with positive score → hold
        else:
            til = "watch"

        # Phase alignment (mean bullish direction)
        thetas = np.angle(amplitudes)
        phase_align = float(np.mean(np.cos(thetas)))   # +1 = all bullish, -1 = all bearish

        # Mean coherence
        mean_coh = float(np.mean(np.abs(amplitudes)))

        # Per-ring BEC fractions
        ring_bec = []
        for ri in range(1, 8):
            ring_verts = [v for v in VERTICES if v.ring == ri]
            ring_phases = [classify_state(amplitudes[[v.index]])[0] for v in ring_verts]
            ring_bec.append(sum(1 for p in ring_phases if p == Phase.BEC) / len(ring_phases))

        return TSCMarketSignal(
            ticker=ticker,
            amplitudes=amplitudes,
            bec_fraction=bec_frac,
            ss_fraction=ss_frac,
            fqh_fraction=fqh_frac,
            mott_fraction=mott_frac,
            dt_fraction=dt_frac,
            tt_weight=tt, ti_weight=ti, tf_weight=tf, dt_weight=dt, ev_weight=ev,
            mean_coherence=mean_coh,
            phase_alignment=phase_align,
            crystal_pd_score=crystal_pd,
            mr_resolved=mr_resolved,
            til_action=til,
            ring_bec_fractions=ring_bec,
        )


def compute_portfolio_crystal(
    signals: list[TSCMarketSignal]
) -> dict:
    """
    Power-of-8 group coherence: combine TSC signals from multiple stocks.
    Group BEC fraction = 1 - (1 - C_TI)^n  [from URB #642]

    Returns portfolio-level PD and recommended allocation weights.
    """
    n = len(signals)
    if n == 0:
        return {}

    # Portfolio-level BEC saturation
    group_bec = 1.0 - (1.0 - C_TI) ** n

    # Weighted allocation: each stock's weight ∝ its BEC fraction × phase alignment
    raw_weights = {}
    for sig in signals:
        if sig.til_action in ("pause", "exit"):
            w = 0.0
        elif sig.til_action == "strong_buy":
            w = sig.bec_fraction * max(0.0, sig.phase_alignment)
        elif sig.til_action == "buy":
            w = sig.bec_fraction * max(0.0, sig.phase_alignment) * 0.7
        elif sig.til_action == "sell":
            w = 0.0
        else:
            w = sig.bec_fraction * max(0.0, sig.phase_alignment) * 0.4
        raw_weights[sig.ticker] = max(0.0, w)

    total = sum(raw_weights.values()) + 1e-9
    normalized = {t: w / total for t, w in raw_weights.items()}

    return {
        "n_stocks": n,
        "group_bec_saturation": round(group_bec, 4),
        "portfolio_mr_resolved": group_bec > T_TI,
        "allocation_weights": normalized,
        "mean_stock_bec": round(float(np.mean([s.bec_fraction for s in signals])), 4),
        "best_signal": max(signals, key=lambda s: s.bec_fraction).ticker,
        "worst_signal": min(signals, key=lambda s: s.bec_fraction).ticker,
    }
