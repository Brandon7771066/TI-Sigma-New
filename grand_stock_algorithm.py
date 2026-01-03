"""
GRAND STOCK ALGORITHM (GSA) - TI Framework
Ξ Metrics: Amplitude (A), Memory Kernel (κ), Constraint (C)
Regime Classification: Expansion/Compression/Fracture/Reset
Author: Brandon Charles Emerick | Date: December 14, 2025
"""

import numpy as np
import pandas as pd
from datetime import datetime, timedelta
from dataclasses import dataclass, field
from typing import Dict, List, Optional, Tuple, Any
from enum import Enum
import yfinance as yf
import os

class MarketRegime(Enum):
    EXPANSION = "expansion"
    COMPRESSION = "compression"
    FRACTURE = "fracture"
    RESET = "reset"

class TradingSignal(Enum):
    STRONG_BUY = "strong_buy"
    BUY = "buy"
    HOLD = "hold"
    SELL = "sell"
    STRONG_SELL = "strong_sell"

SACRED_MIN, SACRED_MAX = -0.666, 0.333

@dataclass
class XiMetrics:
    amplitude: float = 0.0
    memory_kernel: float = 0.0
    constraint: float = 0.0
    xi_unsigned: float = 0.0
    xi_signed: float = 0.0
    pd_score: float = 0.0

@dataclass
class RegimeState:
    regime: MarketRegime = MarketRegime.EXPANSION
    confidence: float = 0.0
    constraint_rate: float = 0.0
    memory_asymmetry: float = 0.0
    pd_shape: str = "broad"

@dataclass
class TradingDecision:
    signal: TradingSignal = TradingSignal.HOLD
    confidence: float = 0.0
    xi_metrics: XiMetrics = field(default_factory=XiMetrics)
    regime: RegimeState = field(default_factory=RegimeState)
    gile_score: float = 0.0
    reasoning: str = ""

@dataclass
class BacktestResult:
    start_date: datetime = None
    end_date: datetime = None
    initial_capital: float = 100000
    final_value: float = 100000
    total_return_pct: float = 0.0
    cagr: float = 0.0
    sharpe_ratio: float = 0.0
    max_drawdown: float = 0.0
    win_rate: float = 0.0
    total_trades: int = 0
    winning_trades: int = 0

class MarketDataPipeline:
    def __init__(self, cache_dir: str = "data/stock_cache"):
        self.cache_dir = cache_dir
        os.makedirs(cache_dir, exist_ok=True)
        self.data_cache: Dict[str, pd.DataFrame] = {}

    def fetch_data(self, ticker: str, start_date: str = None, end_date: str = None, use_cache: bool = True) -> Optional[pd.DataFrame]:
        if start_date is None:
            start_date = (datetime.now() - timedelta(days=365*5)).strftime('%Y-%m-%d')
        if end_date is None:
            end_date = datetime.now().strftime('%Y-%m-%d')
        cache_key = f"{ticker}_{start_date}_{end_date}"
        cache_file = os.path.join(self.cache_dir, f"{cache_key}.csv")
        if use_cache and cache_key in self.data_cache:
            return self.data_cache[cache_key]
        if use_cache and os.path.exists(cache_file):
            try:
                df = pd.read_csv(cache_file, index_col=0, parse_dates=True)
                self.data_cache[cache_key] = df
                return df
            except Exception:
                pass
        try:
            stock = yf.Ticker(ticker)
            df = stock.history(start=start_date, end=end_date)
            if df.empty:
                return None
            df['Return'] = df['Close'].pct_change() * 100
            df['LogReturn'] = np.log(df['Close'] / df['Close'].shift(1)) * 100
            df.to_csv(cache_file)
            self.data_cache[cache_key] = df
            return df
        except Exception as e:
            print(f"Error fetching {ticker}: {e}")
            return None

    def fetch_multiple(self, tickers: List[str], start_date: str = None, end_date: str = None) -> Dict[str, pd.DataFrame]:
        return {t: df for t in tickers if (df := self.fetch_data(t, start_date, end_date)) is not None and not df.empty}

class ExistenceIntensityEngine:
    def __init__(self, lookback_short: int = 7, lookback_long: int = 30):
        self.lookback_short = lookback_short
        self.lookback_long = lookback_long
        self.kappa_decay_positive = 0.1
        self.kappa_decay_negative = 0.05
        self.W_GREAT, self.W_TERRIBLE = 1.0, 2.0
        self.W_EXCEPTIONAL, self.W_WICKED = 1.5, 6.0

    def calculate_amplitude(self, returns: np.ndarray) -> float:
        if len(returns) < 2:
            return 0.0
        current_return = abs(returns[-1]) if len(returns) > 0 else 0
        volatility = max(np.std(returns) if len(returns) > 1 else 1.0, 0.01)
        return float(np.clip(current_return / volatility, 0, 10))

    def calculate_memory_kernel(self, returns: np.ndarray) -> float:
        if len(returns) < 3:
            return 0.5
        pos_rets, neg_rets = returns[returns > 0], returns[returns < 0]
        kappa_pos = sum(abs(r) * np.exp(-self.kappa_decay_positive * i) for i, r in enumerate(pos_rets))
        kappa_neg = sum(abs(r) * np.exp(-self.kappa_decay_negative * i) for i, r in enumerate(neg_rets))
        total = kappa_pos + kappa_neg
        return float(np.clip(kappa_neg / total, 0, 1)) if total > 0 else 0.5

    def calculate_constraint(self, prices: np.ndarray, returns: np.ndarray) -> float:
        if len(prices) < 5:
            return 0.0
        peak = np.max(prices)
        drawdown = (peak - prices[-1]) / peak if peak > 0 else 0
        recent_vol = np.std(returns[-self.lookback_short:]) if len(returns) >= self.lookback_short else 1.0
        long_vol = np.std(returns[-self.lookback_long:]) if len(returns) >= self.lookback_long else 1.0
        vol_constraint = 1 - min(recent_vol / max(long_vol, 0.01), 1)
        return float(np.clip(0.6 * drawdown + 0.4 * vol_constraint, 0, 1))

    def calculate_valence_weight(self, return_pct: float) -> float:
        if return_pct > 5.0: return self.W_EXCEPTIONAL
        elif return_pct > 0.333: return self.W_GREAT
        elif return_pct > -0.666: return 1.0
        elif return_pct > -5.0: return self.W_TERRIBLE
        else: return self.W_WICKED

    def compute_xi(self, df: pd.DataFrame) -> XiMetrics:
        if df is None or len(df) < 10:
            return XiMetrics()
        returns = df['Return'].dropna().values
        prices = df['Close'].values
        if len(returns) < 5:
            return XiMetrics()
        A = self.calculate_amplitude(returns[-self.lookback_short:])
        kappa = self.calculate_memory_kernel(returns[-self.lookback_long:])
        C = self.calculate_constraint(prices[-self.lookback_long:], returns[-self.lookback_long:])
        xi_unsigned = A * kappa * C
        current_return = returns[-1] if len(returns) > 0 else 0
        valence = 1 if current_return >= 0 else -1
        xi_signed = valence * xi_unsigned * self.calculate_valence_weight(current_return)
        pd_score = float(np.clip(np.sign(xi_signed) * np.log1p(abs(xi_signed)), -3, 2))
        return XiMetrics(amplitude=A, memory_kernel=kappa, constraint=C, xi_unsigned=xi_unsigned, xi_signed=xi_signed, pd_score=pd_score)

class RegimeClassifier:
    def __init__(self, lookback: int = 60):
        self.lookback = lookback
        self.constraint_history: List[float] = []
        self.pd_history: List[float] = []

    def classify_regime(self, xi_metrics: XiMetrics, returns: np.ndarray) -> RegimeState:
        if len(returns) < 10:
            return RegimeState(regime=MarketRegime.EXPANSION, confidence=0.3)
        self.constraint_history.append(xi_metrics.constraint)
        self.pd_history.append(xi_metrics.pd_score)
        if len(self.constraint_history) > self.lookback:
            self.constraint_history = self.constraint_history[-self.lookback:]
        if len(self.pd_history) > self.lookback:
            self.pd_history = self.pd_history[-self.lookback:]
        constraint_rate = 0.0
        if len(self.constraint_history) >= 5:
            recent_c = np.mean(self.constraint_history[-5:])
            older_c = np.mean(self.constraint_history[-10:-5]) if len(self.constraint_history) >= 10 else recent_c
            constraint_rate = recent_c - older_c
        pd_shape = "broad"
        if len(self.pd_history) >= 10:
            pd_std = np.std(self.pd_history[-10:])
            pd_skew = self._calculate_skew(self.pd_history[-20:]) if len(self.pd_history) >= 20 else 0
            if pd_std > 1.0: pd_shape = "heavy_tail"
            elif pd_std < 0.3: pd_shape = "narrow"
            elif abs(pd_skew) < 0.3: pd_shape = "symmetric"
        recent_vol = np.std(returns[-10:]) if len(returns) >= 10 else 1.0
        long_vol = np.std(returns[-30:]) if len(returns) >= 30 else 1.0
        vol_ratio = recent_vol / max(long_vol, 0.01)
        regime, confidence = MarketRegime.EXPANSION, 0.5
        if constraint_rate > 0.1 and recent_vol > long_vol * 1.5 and xi_metrics.pd_score < -1:
            regime, confidence = MarketRegime.FRACTURE, min(0.9, 0.5 + abs(constraint_rate) + abs(xi_metrics.pd_score) / 3)
        elif constraint_rate > 0.05 and vol_ratio < 0.7:
            regime, confidence = MarketRegime.COMPRESSION, min(0.8, 0.5 + constraint_rate * 2 + (1 - vol_ratio))
        elif constraint_rate < -0.05 and recent_vol > long_vol:
            regime, confidence = MarketRegime.RESET, min(0.8, 0.5 + abs(constraint_rate) + (vol_ratio - 1) * 0.5)
        else:
            confidence = max(0.4, 0.7 - abs(constraint_rate) * 2)
        return RegimeState(regime=regime, confidence=confidence, constraint_rate=constraint_rate, memory_asymmetry=xi_metrics.memory_kernel, pd_shape=pd_shape)

    def _calculate_skew(self, values: List[float]) -> float:
        if len(values) < 3: return 0.0
        arr = np.array(values)
        mean, std = np.mean(arr), np.std(arr)
        return float(np.mean(((arr - mean) / std) ** 3)) if std > 0 else 0.0

class GILEScorer:
    def __init__(self):
        self.w_goodness, self.w_intuition, self.w_love, self.w_environment = 0.20, 0.25, 0.25, 0.30

    def calculate_gile(self, df: pd.DataFrame, market_df: Optional[pd.DataFrame] = None) -> float:
        if df is None or len(df) < 20:
            return 0.5
        returns = df['Return'].dropna().values
        mean_ret = np.mean(returns[-20:]) if len(returns) >= 20 else 0
        std_ret = np.std(returns[-20:]) if len(returns) >= 20 else 1
        g_score = 1 / (1 + np.exp(-mean_ret / max(std_ret, 0.01)))
        i_score = 0.5
        if len(returns) >= 15:
            short_ma, long_ma = np.mean(df['Close'].values[-5:]), np.mean(df['Close'].values[-15:])
            i_score = 1 / (1 + np.exp(-(short_ma - long_ma) / max(long_ma, 0.01) * 50))
        l_score = 0.5
        if market_df is not None and len(market_df) >= 20:
            market_returns = market_df['Return'].dropna().values[-20:]
            stock_returns = returns[-20:]
            if len(market_returns) == len(stock_returns):
                try:
                    corr = np.corrcoef(market_returns, stock_returns)[0, 1]
                    l_score = (corr + 1) / 2
                except: pass
        e_score = 0.5
        if len(returns) >= 30:
            m30, m10 = np.sum(returns[-30:]), np.sum(returns[-10:])
            e_score = 1 / (1 + np.exp(-(m10 * m30) * 0.01))
        return float(np.clip(self.w_goodness * g_score + self.w_intuition * i_score + self.w_love * l_score + self.w_environment * e_score, 0, 1))

class GrandStockAlgorithm:
    def __init__(self, initial_capital: float = 100000):
        self.data_pipeline = MarketDataPipeline()
        self.xi_engine = ExistenceIntensityEngine()
        self.regime_classifier = RegimeClassifier()
        self.gile_scorer = GILEScorer()
        self.initial_capital = initial_capital
        self.capital = initial_capital
        self.positions: Dict[str, float] = {}
        self.max_position_size = 0.15
        self.regime_adjustments = {MarketRegime.EXPANSION: 1.0, MarketRegime.COMPRESSION: 0.5, MarketRegime.FRACTURE: 0.0, MarketRegime.RESET: 0.3}

    def analyze(self, ticker: str, market_ticker: str = "SPY") -> TradingDecision:
        df = self.data_pipeline.fetch_data(ticker)
        market_df = self.data_pipeline.fetch_data(market_ticker)
        if df is None or len(df) < 30:
            return TradingDecision(signal=TradingSignal.HOLD, confidence=0.0, reasoning=f"Insufficient data for {ticker}")
        returns = df['Return'].dropna().values
        xi_metrics = self.xi_engine.compute_xi(df)
        regime_state = self.regime_classifier.classify_regime(xi_metrics, returns)
        gile_score = self.gile_scorer.calculate_gile(df, market_df)
        signal, confidence, reasoning = self._generate_signal(xi_metrics, regime_state, gile_score, returns)
        return TradingDecision(signal=signal, confidence=confidence, xi_metrics=xi_metrics, regime=regime_state, gile_score=gile_score, reasoning=reasoning)

    def _generate_signal(self, xi: XiMetrics, regime: RegimeState, gile: float, returns: np.ndarray) -> Tuple[TradingSignal, float, str]:
        reasons = []
        if regime.regime == MarketRegime.FRACTURE:
            return (TradingSignal.STRONG_SELL, regime.confidence, f"FRACTURE regime - exit all (C_rate={regime.constraint_rate:.3f})")
        if gile > 0.65: base_signal, base_conf = TradingSignal.STRONG_BUY, 0.8; reasons.append(f"High GILE ({gile:.2f})")
        elif gile > 0.55: base_signal, base_conf = TradingSignal.BUY, 0.6; reasons.append(f"Good GILE ({gile:.2f})")
        elif gile > 0.45: base_signal, base_conf = TradingSignal.HOLD, 0.5; reasons.append(f"Neutral GILE ({gile:.2f})")
        elif gile > 0.35: base_signal, base_conf = TradingSignal.SELL, 0.6; reasons.append(f"Weak GILE ({gile:.2f})")
        else: base_signal, base_conf = TradingSignal.STRONG_SELL, 0.8; reasons.append(f"Poor GILE ({gile:.2f})")
        if regime.regime == MarketRegime.COMPRESSION:
            if base_signal in [TradingSignal.BUY, TradingSignal.STRONG_BUY]:
                base_signal = TradingSignal.HOLD; reasons.append("COMPRESSION - reducing exposure")
            base_conf *= 0.7
        elif regime.regime == MarketRegime.RESET:
            base_conf *= 0.6; reasons.append("RESET - reduced conviction")
        elif regime.regime == MarketRegime.EXPANSION and xi.pd_score > 0.5:
            base_conf = min(base_conf * 1.2, 0.9); reasons.append("EXPANSION with positive PD")
        if xi.xi_signed < -2.0:
            base_signal, base_conf = TradingSignal.STRONG_SELL, max(base_conf, 0.7); reasons.append(f"Strong negative Ξ ({xi.xi_signed:.2f})")
        if xi.memory_kernel > 0.7:
            if base_signal in [TradingSignal.BUY, TradingSignal.STRONG_BUY]: base_signal = TradingSignal.HOLD
            reasons.append(f"High κ_neg ({xi.memory_kernel:.2f})")
        return base_signal, base_conf, " | ".join(reasons)

    def backtest(self, tickers: List[str], start_date: str, end_date: str, market_ticker: str = "SPY") -> BacktestResult:
        print(f"\nGSA BACKTEST: {start_date} to {end_date}")
        data = self.data_pipeline.fetch_multiple(tickers, start_date, end_date)
        market_data = self.data_pipeline.fetch_data(market_ticker, start_date, end_date)
        if not data: return BacktestResult()
        all_dates = None
        for df in data.values():
            all_dates = set(df.index) if all_dates is None else all_dates.intersection(set(df.index))
        if not all_dates: return BacktestResult()
        dates = sorted(list(all_dates))
        capital = self.initial_capital
        positions = {t: 0.0 for t in tickers}
        portfolio_values = [capital]
        trades = []
        for i, date in enumerate(dates[60:], start=60):
            current_data = {t: df.loc[:date].tail(60) for t, df in data.items() if date in df.index}
            if not current_data:
                portfolio_values.append(portfolio_values[-1]); continue
            signals = {}
            for ticker, df in current_data.items():
                if len(df) < 30: continue
                returns = df['Return'].dropna().values
                xi = self.xi_engine.compute_xi(df)
                regime = self.regime_classifier.classify_regime(xi, returns)
                market_slice = market_data.loc[:date].tail(60) if market_data is not None else None
                gile = self.gile_scorer.calculate_gile(df, market_slice)
                signal, conf, _ = self._generate_signal(xi, regime, gile, returns)
                signals[ticker] = {'signal': signal, 'confidence': conf, 'gile': gile, 'regime': regime.regime, 'xi': xi}
            for ticker, sig in signals.items():
                target = 0.0
                if sig['signal'] == TradingSignal.STRONG_BUY: target = self.max_position_size * 1.2
                elif sig['signal'] == TradingSignal.BUY: target = self.max_position_size * 0.8
                elif sig['signal'] == TradingSignal.HOLD: target = positions.get(ticker, 0.0)
                target *= self.regime_adjustments.get(sig['regime'], 1.0) * sig['confidence']
                old = positions.get(ticker, 0.0)
                if abs(target - old) > 0.01:
                    trades.append({'date': date, 'ticker': ticker, 'signal': sig['signal'].value})
                positions[ticker] = target
            daily_ret = sum(w * (current_data[t]['Return'].iloc[-1] / 100) for t, w in positions.items() if t in current_data and len(current_data[t]) > 0 and not np.isnan(current_data[t]['Return'].iloc[-1]))
            capital *= (1 + daily_ret)
            portfolio_values.append(capital)
        portfolio_series = pd.Series(portfolio_values)
        returns_series = portfolio_series.pct_change().dropna()
        total_return = (capital - self.initial_capital) / self.initial_capital * 100
        years = len(dates) / 252
        cagr = ((capital / self.initial_capital) ** (1/max(years, 0.1)) - 1) * 100 if years > 0 else 0
        sharpe = (returns_series.mean() / returns_series.std()) * np.sqrt(252) if len(returns_series) > 0 and returns_series.std() > 0 else 0.0
        rolling_max = portfolio_series.expanding().max()
        max_dd = abs(((portfolio_series - rolling_max) / rolling_max).min()) * 100 if len(portfolio_series) > 0 else 0
        total_trades = len(trades)
        winning = sum(1 for t in trades if 'buy' in t['signal'].lower())
        print(f"Final: ${capital:,.0f} | Return: {total_return:+.1f}% | CAGR: {cagr:.1f}% | Sharpe: {sharpe:.2f} | MaxDD: {max_dd:.1f}%")
        return BacktestResult(start_date=datetime.strptime(start_date, '%Y-%m-%d'), end_date=datetime.strptime(end_date, '%Y-%m-%d'), initial_capital=self.initial_capital, final_value=capital, total_return_pct=total_return, cagr=cagr, sharpe_ratio=sharpe, max_drawdown=max_dd, win_rate=winning/max(total_trades,1)*100, total_trades=total_trades, winning_trades=winning)

    def validate_crisis(self, crisis_name: str, crisis_dates: Tuple[str, str], market_ticker: str = "SPY") -> Dict:
        start, end = crisis_dates
        df = self.data_pipeline.fetch_data(market_ticker, start, end)
        if df is None or len(df) < 30: return {}
        regimes = []
        for i in range(30, len(df)):
            slice_df = df.iloc[:i+1]
            xi = self.xi_engine.compute_xi(slice_df)
            regime = self.regime_classifier.classify_regime(xi, slice_df['Return'].dropna().values)
            regimes.append({'date': slice_df.index[-1], 'regime': regime.regime.value})
        regime_vals = [r['regime'] for r in regimes]
        has_fracture = 'fracture' in regime_vals
        fracture_date = regimes[regime_vals.index('fracture')]['date'] if has_fracture else None
        print(f"{crisis_name}: Fracture={'Yes' if has_fracture else 'No'}" + (f" on {fracture_date}" if fracture_date else ""))
        return {'crisis': crisis_name, 'fracture_detected': has_fracture, 'fracture_date': str(fracture_date) if fracture_date else None}

def run_gsa_demo():
    print("\n" + "="*50 + "\nGRAND STOCK ALGORITHM (GSA) DEMO\n" + "="*50)
    gsa = GrandStockAlgorithm(initial_capital=100000)
    for ticker in ["AAPL", "NVDA"]:
        d = gsa.analyze(ticker)
        print(f"{ticker}: {d.signal.value} ({d.confidence:.0%}) | GILE: {d.gile_score:.2f} | Regime: {d.regime.regime.value}")
    gsa.backtest(["AAPL", "MSFT", "GOOGL", "NVDA", "TSLA", "META", "AMZN"], "2020-01-01", "2024-12-01")
    gsa.validate_crisis("COVID 2020", ("2020-01-01", "2020-06-01"))
    gsa.validate_crisis("Bear 2022", ("2021-11-01", "2022-12-01"))
    print("="*50 + "\n")

class TIOptionsPricingEngine:
    """
    TI-Enhanced Options Pricing Module
    Integrates GILE metrics with Black-Scholes for superior pricing
    
    Key Enhancements:
    - GILE-adjusted implied volatility
    - Causation threshold confirmation for trade entry
    - Regime-based option strategy selection
    """
    
    def __init__(self, gsa: GrandStockAlgorithm = None):
        self.gsa = gsa or GrandStockAlgorithm()
        self.risk_free_rate = 0.05  # 5% annual rate
    
    @staticmethod
    def _norm_cdf(x: float) -> float:
        """Standard normal CDF using math.erf (no scipy required)"""
        import math
        return 0.5 * (1 + math.erf(x / math.sqrt(2)))
    
    @staticmethod
    def _norm_pdf(x: float) -> float:
        """Standard normal PDF using numpy (no scipy required)"""
        return np.exp(-0.5 * x**2) / np.sqrt(2 * np.pi)
    
    def black_scholes(self, S: float, K: float, T: float, r: float, sigma: float, 
                      option_type: str = 'call') -> Dict[str, float]:
        """
        Standard Black-Scholes pricing (numpy-only, no scipy dependency)
        
        Args:
            S: Current stock price
            K: Strike price
            T: Time to expiration (years)
            r: Risk-free rate
            sigma: Volatility
            option_type: 'call' or 'put'
        """
        if K <= 0 or T <= 0 or sigma <= 0:
            return {'price': 0, 'delta': 0, 'gamma': 0, 'vega': 0, 'theta': 0, 'd1': 0, 'd2': 0}
        
        d1 = (np.log(S/K) + (r + 0.5*sigma**2)*T) / (sigma*np.sqrt(T))
        d2 = d1 - sigma*np.sqrt(T)
        
        if option_type.lower() == 'call':
            price = S*self._norm_cdf(d1) - K*np.exp(-r*T)*self._norm_cdf(d2)
            delta = self._norm_cdf(d1)
        else:
            price = K*np.exp(-r*T)*self._norm_cdf(-d2) - S*self._norm_cdf(-d1)
            delta = self._norm_cdf(d1) - 1
        
        gamma = self._norm_pdf(d1) / (S*sigma*np.sqrt(T))
        vega = S*self._norm_pdf(d1)*np.sqrt(T) / 100
        theta = (-S*self._norm_pdf(d1)*sigma/(2*np.sqrt(T)) - r*K*np.exp(-r*T)*self._norm_cdf(d2 if option_type == 'call' else -d2)) / 365
        
        return {
            'price': price,
            'delta': delta,
            'gamma': gamma,
            'vega': vega,
            'theta': theta,
            'd1': d1,
            'd2': d2
        }
    
    def gile_adjusted_volatility(self, ticker: str, base_iv: float) -> Dict[str, Any]:
        """
        Adjust implied volatility using GILE metrics
        
        High GILE = Lower uncertainty = Lower IV adjustment
        Low GILE = Higher uncertainty = Higher IV adjustment
        """
        decision = self.gsa.analyze(ticker)
        gile = decision.gile_score
        regime = decision.regime.regime
        xi = decision.xi_metrics
        
        adjustment_factor = 1.0
        
        if gile > 0.65:
            adjustment_factor = 0.90
            reasoning = "High GILE coherence reduces uncertainty"
        elif gile > 0.55:
            adjustment_factor = 0.95
            reasoning = "Good GILE suggests normal volatility"
        elif gile > 0.45:
            adjustment_factor = 1.00
            reasoning = "Neutral GILE - no adjustment"
        elif gile > 0.35:
            adjustment_factor = 1.10
            reasoning = "Low GILE increases uncertainty"
        else:
            adjustment_factor = 1.25
            reasoning = "Poor GILE suggests heightened risk"
        
        if regime == MarketRegime.FRACTURE:
            adjustment_factor *= 1.30
            reasoning += " | FRACTURE regime adds volatility"
        elif regime == MarketRegime.COMPRESSION:
            adjustment_factor *= 1.15
            reasoning += " | COMPRESSION may precede breakout"
        elif regime == MarketRegime.EXPANSION:
            adjustment_factor *= 0.95
            reasoning += " | EXPANSION suggests trending behavior"
        
        if xi.memory_kernel > 0.6:
            adjustment_factor *= 1.10
            reasoning += " | High memory kernel adds persistence"
        
        adjusted_iv = base_iv * adjustment_factor
        
        return {
            'base_iv': base_iv,
            'adjusted_iv': adjusted_iv,
            'adjustment_factor': adjustment_factor,
            'gile_score': gile,
            'regime': regime.value,
            'reasoning': reasoning,
            'causation_confirmed': gile >= 0.85
        }
    
    def price_option_with_ti(self, ticker: str, strike: float, expiry_days: int,
                             option_type: str = 'call', base_iv: float = 0.30) -> Dict[str, Any]:
        """
        Price an option using TI-enhanced methodology
        """
        df = self.gsa.data_pipeline.fetch_data(ticker)
        if df is None or df.empty:
            return {'error': f'No data for {ticker}'}
        
        current_price = df['Close'].iloc[-1]
        T = expiry_days / 365
        
        vol_analysis = self.gile_adjusted_volatility(ticker, base_iv)
        adjusted_iv = vol_analysis['adjusted_iv']
        
        bs_standard = self.black_scholes(current_price, strike, T, self.risk_free_rate, base_iv, option_type)
        bs_ti = self.black_scholes(current_price, strike, T, self.risk_free_rate, adjusted_iv, option_type)
        
        decision = self.gsa.analyze(ticker)
        
        if option_type == 'call':
            if decision.signal in [TradingSignal.STRONG_BUY, TradingSignal.BUY]:
                trade_recommendation = 'BUY CALL'
            elif decision.signal in [TradingSignal.STRONG_SELL, TradingSignal.SELL]:
                trade_recommendation = 'AVOID or SELL CALL'
            else:
                trade_recommendation = 'NEUTRAL'
        else:
            if decision.signal in [TradingSignal.STRONG_SELL, TradingSignal.SELL]:
                trade_recommendation = 'BUY PUT'
            elif decision.signal in [TradingSignal.STRONG_BUY, TradingSignal.BUY]:
                trade_recommendation = 'AVOID or SELL PUT'
            else:
                trade_recommendation = 'NEUTRAL'
        
        return {
            'ticker': ticker,
            'current_price': current_price,
            'strike': strike,
            'expiry_days': expiry_days,
            'option_type': option_type,
            'standard_pricing': bs_standard,
            'ti_pricing': bs_ti,
            'volatility_analysis': vol_analysis,
            'trade_recommendation': trade_recommendation,
            'gsa_signal': decision.signal.value,
            'confidence': decision.confidence,
            'regime': decision.regime.regime.value,
            'gile_score': decision.gile_score
        }
    
    def recommend_strategy(self, ticker: str, capital: float = 10000) -> Dict[str, Any]:
        """
        Recommend optimal options strategy based on TI analysis
        """
        decision = self.gsa.analyze(ticker)
        regime = decision.regime.regime
        gile = decision.gile_score
        confidence = decision.confidence
        
        strategies = []
        
        if regime == MarketRegime.EXPANSION:
            if decision.signal == TradingSignal.STRONG_BUY:
                strategies.append({
                    'name': 'Long Call',
                    'rationale': 'EXPANSION + STRONG_BUY = Bullish momentum',
                    'risk': 'Limited to premium',
                    'reward': 'Unlimited upside',
                    'ti_score': gile * confidence
                })
                strategies.append({
                    'name': 'Bull Call Spread',
                    'rationale': 'Defined risk bullish play',
                    'risk': 'Net debit',
                    'reward': 'Capped but defined',
                    'ti_score': gile * confidence * 0.9
                })
            elif decision.signal == TradingSignal.STRONG_SELL:
                strategies.append({
                    'name': 'Long Put',
                    'rationale': 'EXPANSION + STRONG_SELL = Reversal likely',
                    'risk': 'Limited to premium',
                    'reward': 'Substantial if reverses',
                    'ti_score': (1 - gile) * confidence
                })
        
        elif regime == MarketRegime.COMPRESSION:
            strategies.append({
                'name': 'Iron Condor',
                'rationale': 'COMPRESSION = Low volatility, range-bound',
                'risk': 'Wings define max loss',
                'reward': 'Premium collection',
                'ti_score': 0.7 if 0.45 < gile < 0.55 else 0.5
            })
            strategies.append({
                'name': 'Calendar Spread',
                'rationale': 'Benefit from time decay during compression',
                'risk': 'Net debit',
                'reward': 'Time value differential',
                'ti_score': 0.6
            })
        
        elif regime == MarketRegime.FRACTURE:
            strategies.append({
                'name': 'Long Straddle',
                'rationale': 'FRACTURE = High volatility expected',
                'risk': 'Premium of both legs',
                'reward': 'Unlimited in either direction',
                'ti_score': 0.8
            })
            strategies.append({
                'name': 'Protective Put',
                'rationale': 'FRACTURE = Hedge existing positions',
                'risk': 'Premium cost',
                'reward': 'Downside protection',
                'ti_score': 0.75
            })
        
        elif regime == MarketRegime.RESET:
            strategies.append({
                'name': 'Cash Secured Put',
                'rationale': 'RESET = Wait for stabilization, sell puts at support',
                'risk': 'Must buy shares at strike',
                'reward': 'Premium income',
                'ti_score': 0.6 if gile > 0.5 else 0.4
            })
        
        if not strategies:
            strategies.append({
                'name': 'No Trade',
                'rationale': 'TI metrics do not support a clear strategy',
                'risk': 'N/A',
                'reward': 'Capital preservation',
                'ti_score': 0.0
            })
        
        strategies.sort(key=lambda x: x['ti_score'], reverse=True)
        
        return {
            'ticker': ticker,
            'capital': capital,
            'gsa_analysis': {
                'signal': decision.signal.value,
                'confidence': confidence,
                'gile': gile,
                'regime': regime.value
            },
            'recommended_strategies': strategies,
            'top_recommendation': strategies[0] if strategies else None
        }


def run_gsa_demo():
    print("\n" + "="*50 + "\nGRAND STOCK ALGORITHM (GSA) DEMO\n" + "="*50)
    gsa = GrandStockAlgorithm(initial_capital=100000)
    for ticker in ["AAPL", "NVDA"]:
        d = gsa.analyze(ticker)
        print(f"{ticker}: {d.signal.value} ({d.confidence:.0%}) | GILE: {d.gile_score:.2f} | Regime: {d.regime.regime.value}")
    gsa.backtest(["AAPL", "MSFT", "GOOGL", "NVDA", "TSLA", "META", "AMZN"], "2020-01-01", "2024-12-01")
    gsa.validate_crisis("COVID 2020", ("2020-01-01", "2020-06-01"))
    gsa.validate_crisis("Bear 2022", ("2021-11-01", "2022-12-01"))
    
    print("\n" + "="*50 + "\nTI OPTIONS PRICING DEMO\n" + "="*50)
    options_engine = TIOptionsPricingEngine(gsa)
    
    for ticker in ["AAPL", "NVDA"]:
        print(f"\n{ticker} Options Analysis:")
        df = gsa.data_pipeline.fetch_data(ticker)
        if df is not None and not df.empty:
            current_price = df['Close'].iloc[-1]
            strike = current_price * 1.05  # 5% OTM call
            result = options_engine.price_option_with_ti(ticker, strike=strike, expiry_days=30, option_type='call', base_iv=0.30)
            if 'error' not in result:
                print(f"  Current: ${result['current_price']:.2f} | Strike: ${strike:.2f}")
                print(f"  Standard BS: ${result['standard_pricing']['price']:.2f}")
                print(f"  TI-Adjusted: ${result['ti_pricing']['price']:.2f}")
                print(f"  Recommendation: {result['trade_recommendation']}")
        
        strategy = options_engine.recommend_strategy(ticker)
        if strategy['top_recommendation']:
            print(f"  Top Strategy: {strategy['top_recommendation']['name']}")
            print(f"  Rationale: {strategy['top_recommendation']['rationale']}")
    
    print("="*50 + "\n")


if __name__ == "__main__":
    run_gsa_demo()
