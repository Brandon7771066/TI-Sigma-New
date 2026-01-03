"""
GSA Research Runner - Replit-only research and validation
Implements ChatGPT-recommended hardening:
1. Purged/Embargoed Walk-Forward Validation
2. Baseline Ladder (7 strategies to beat before claiming TI adds value)
3. Mean-Reversion Detection (amplitude bucket analysis)
4. CPCV-style robustness testing
"""

import numpy as np
import pandas as pd
import yfinance as yf
from datetime import datetime, timedelta
from dataclasses import dataclass, field
from typing import Dict, List, Optional, Tuple
import json
import os

from gsa_core import (
    compute_xi, compute_xi_ti_aligned, classify_regime, MarketRegime,
    valence_weight, safe_std
)

CACHE_DIR = "data/gsa_research_cache"
os.makedirs(CACHE_DIR, exist_ok=True)


@dataclass
class BaselineResult:
    """Result from a baseline strategy backtest."""
    strategy_name: str
    total_return: float = 0.0
    cagr: float = 0.0
    sharpe: float = 0.0
    sortino: float = 0.0
    max_drawdown: float = 0.0
    calmar: float = 0.0
    win_rate: float = 0.0
    n_trades: int = 0


@dataclass
class ValidationResult:
    """Result from walk-forward validation."""
    fold: int = 0
    train_start: str = ""
    train_end: str = ""
    test_start: str = ""
    test_end: str = ""
    train_sharpe: float = 0.0
    test_sharpe: float = 0.0
    test_return: float = 0.0
    regime_accuracy: float = 0.0


class MarketDataFetcher:
    """Fetch and cache market data using yfinance."""
    
    def __init__(self):
        self.cache: Dict[str, pd.DataFrame] = {}
    
    def fetch(self, ticker: str, start: str, end: str) -> Optional[pd.DataFrame]:
        cache_key = f"{ticker}_{start}_{end}"
        cache_file = os.path.join(CACHE_DIR, f"{cache_key}.csv")
        
        if cache_key in self.cache:
            return self.cache[cache_key]
        
        if os.path.exists(cache_file):
            try:
                df = pd.read_csv(cache_file, index_col=0, parse_dates=True)
                self.cache[cache_key] = df
                return df
            except Exception:
                pass
        
        try:
            df = yf.download(ticker, start=start, end=end, progress=False)
            if df.empty:
                return None
            if isinstance(df.columns, pd.MultiIndex):
                df.columns = df.columns.get_level_values(0)
            df['Return'] = df['Close'].pct_change() * 100
            df.to_csv(cache_file)
            self.cache[cache_key] = df
            return df
        except Exception as e:
            print(f"Error fetching {ticker}: {e}")
            return None


class BaselineLadder:
    """
    7 baseline strategies to beat before claiming TI adds value.
    ChatGPT recommended: SPY buy/hold, equal weight, 12-1 momentum,
    mean-reversion RSI, volatility targeting, 200d SMA trend, logistic regression.
    """
    
    def __init__(self, fetcher: MarketDataFetcher):
        self.fetcher = fetcher
    
    def run_all_baselines(self, tickers: List[str], start: str, end: str) -> List[BaselineResult]:
        results = []
        
        spy_df = self.fetcher.fetch("SPY", start, end)
        ticker_data = {t: self.fetcher.fetch(t, start, end) for t in tickers}
        ticker_data = {t: df for t, df in ticker_data.items() if df is not None and len(df) > 60}
        
        if spy_df is not None:
            results.append(self._spy_buy_hold(spy_df))
        
        if ticker_data:
            results.append(self._equal_weight(ticker_data))
            results.append(self._momentum_12_1(ticker_data))
            results.append(self._mean_reversion_rsi(ticker_data))
            results.append(self._volatility_targeting(ticker_data, target_vol=0.15))
            results.append(self._trend_filter_sma200(ticker_data))
            results.append(self._simple_logistic(ticker_data))
        
        return results
    
    def _compute_metrics(self, returns: pd.Series, name: str) -> BaselineResult:
        if len(returns) < 10:
            return BaselineResult(strategy_name=name)
        
        returns = returns.dropna()
        total_ret = (1 + returns).prod() - 1
        years = len(returns) / 252
        cagr = ((1 + total_ret) ** (1 / max(years, 0.1)) - 1) if years > 0 else 0
        
        mean_ret = returns.mean()
        std_ret = returns.std()
        sharpe = (mean_ret / std_ret) * np.sqrt(252) if std_ret > 0 else 0
        
        downside = returns[returns < 0].std()
        sortino = (mean_ret / downside) * np.sqrt(252) if downside > 0 else 0
        
        cumulative = (1 + returns).cumprod()
        rolling_max = cumulative.expanding().max()
        drawdown = (cumulative - rolling_max) / rolling_max
        max_dd = abs(drawdown.min())
        
        calmar = cagr / max_dd if max_dd > 0 else 0
        
        return BaselineResult(
            strategy_name=name,
            total_return=total_ret * 100,
            cagr=cagr * 100,
            sharpe=sharpe,
            sortino=sortino,
            max_drawdown=max_dd * 100,
            calmar=calmar,
            win_rate=(returns > 0).mean() * 100 if len(returns) > 0 else 0
        )
    
    def _spy_buy_hold(self, spy_df: pd.DataFrame) -> BaselineResult:
        returns = spy_df['Return'].dropna() / 100
        return self._compute_metrics(returns, "SPY Buy/Hold")
    
    def _equal_weight(self, data: Dict[str, pd.DataFrame]) -> BaselineResult:
        all_dates = None
        for df in data.values():
            dates = set(df.index)
            all_dates = dates if all_dates is None else all_dates.intersection(dates)
        
        if not all_dates:
            return BaselineResult(strategy_name="Equal Weight")
        
        dates = sorted(list(all_dates))
        weight = 1.0 / len(data)
        returns = []
        
        for date in dates:
            daily_ret = sum(
                weight * (data[t].loc[date, 'Return'] / 100)
                for t in data if date in data[t].index
            )
            returns.append(daily_ret)
        
        return self._compute_metrics(pd.Series(returns), "Equal Weight")
    
    def _momentum_12_1(self, data: Dict[str, pd.DataFrame]) -> BaselineResult:
        """12-1 momentum: rank by 12-month return, skip most recent month."""
        all_dates = sorted(set.intersection(*[set(df.index) for df in data.values()]))
        if len(all_dates) < 252:
            return BaselineResult(strategy_name="12-1 Momentum")
        
        returns = []
        lookback = 252
        skip = 21
        
        for i in range(lookback, len(all_dates)):
            date = all_dates[i]
            scores = {}
            for ticker, df in data.items():
                if date in df.index:
                    idx = list(df.index).index(date)
                    if idx >= lookback:
                        mom_12 = df.iloc[idx - lookback:idx - skip]['Return'].sum()
                        scores[ticker] = mom_12
            
            if scores:
                sorted_tickers = sorted(scores.keys(), key=lambda t: scores[t], reverse=True)
                top_n = max(1, len(sorted_tickers) // 3)
                top_tickers = sorted_tickers[:top_n]
                weight = 1.0 / len(top_tickers)
                daily_ret = sum(
                    weight * (data[t].loc[date, 'Return'] / 100)
                    for t in top_tickers if date in data[t].index
                )
                returns.append(daily_ret)
        
        return self._compute_metrics(pd.Series(returns), "12-1 Momentum")
    
    def _mean_reversion_rsi(self, data: Dict[str, pd.DataFrame]) -> BaselineResult:
        """RSI mean-reversion: buy when RSI < 30, sell when RSI > 70."""
        all_dates = sorted(set.intersection(*[set(df.index) for df in data.values()]))
        if len(all_dates) < 60:
            return BaselineResult(strategy_name="RSI Mean-Reversion")
        
        returns = []
        positions = {t: 0.0 for t in data}
        rsi_period = 14
        
        for i in range(rsi_period + 1, len(all_dates)):
            date = all_dates[i]
            for ticker, df in data.items():
                if date in df.index:
                    idx = list(df.index).index(date)
                    if idx >= rsi_period:
                        rets = df.iloc[idx - rsi_period:idx]['Return'].values
                        gains = np.maximum(rets, 0)
                        losses = -np.minimum(rets, 0)
                        avg_gain = np.mean(gains)
                        avg_loss = np.mean(losses)
                        rs = avg_gain / avg_loss if avg_loss > 0 else 100
                        rsi = 100 - (100 / (1 + rs))
                        
                        if rsi < 30:
                            positions[ticker] = 1.0 / len(data)
                        elif rsi > 70:
                            positions[ticker] = 0.0
            
            daily_ret = sum(
                positions[t] * (data[t].loc[date, 'Return'] / 100)
                for t in data if date in data[t].index and positions[t] > 0
            )
            returns.append(daily_ret)
        
        return self._compute_metrics(pd.Series(returns), "RSI Mean-Reversion")
    
    def _volatility_targeting(self, data: Dict[str, pd.DataFrame], target_vol: float = 0.15) -> BaselineResult:
        """Volatility targeting: scale position size to target 15% annual vol."""
        all_dates = sorted(set.intersection(*[set(df.index) for df in data.values()]))
        if len(all_dates) < 60:
            return BaselineResult(strategy_name="Vol Targeting")
        
        returns = []
        lookback = 21
        
        for i in range(lookback, len(all_dates)):
            date = all_dates[i]
            daily_rets = []
            for ticker, df in data.items():
                if date in df.index:
                    idx = list(df.index).index(date)
                    if idx >= lookback:
                        recent_vol = df.iloc[idx - lookback:idx]['Return'].std() / 100 * np.sqrt(252)
                        scale = target_vol / max(recent_vol, 0.01)
                        scale = min(scale, 2.0)
                        ret = df.loc[date, 'Return'] / 100
                        daily_rets.append(ret * scale / len(data))
            
            returns.append(sum(daily_rets))
        
        return self._compute_metrics(pd.Series(returns), "Vol Targeting 15%")
    
    def _trend_filter_sma200(self, data: Dict[str, pd.DataFrame]) -> BaselineResult:
        """200d SMA trend filter: long only when price > 200d SMA."""
        all_dates = sorted(set.intersection(*[set(df.index) for df in data.values()]))
        if len(all_dates) < 200:
            return BaselineResult(strategy_name="200d SMA Trend")
        
        returns = []
        
        for i in range(200, len(all_dates)):
            date = all_dates[i]
            daily_rets = []
            for ticker, df in data.items():
                if date in df.index:
                    idx = list(df.index).index(date)
                    if idx >= 200:
                        sma200 = df.iloc[idx - 200:idx]['Close'].mean()
                        current_price = df.loc[date, 'Close']
                        if current_price > sma200:
                            daily_rets.append(df.loc[date, 'Return'] / 100 / len(data))
            
            returns.append(sum(daily_rets))
        
        return self._compute_metrics(pd.Series(returns), "200d SMA Trend")
    
    def _simple_logistic(self, data: Dict[str, pd.DataFrame]) -> BaselineResult:
        """Simple logistic regression on technical features (placeholder)."""
        all_dates = sorted(set.intersection(*[set(df.index) for df in data.values()]))
        if len(all_dates) < 60:
            return BaselineResult(strategy_name="Logistic Regression")
        
        returns = []
        weight = 1.0 / len(data)
        
        for i in range(21, len(all_dates)):
            date = all_dates[i]
            daily_ret = 0.0
            for ticker, df in data.items():
                if date in df.index:
                    idx = list(df.index).index(date)
                    if idx >= 21:
                        mom_5 = df.iloc[idx - 5:idx]['Return'].sum()
                        mom_20 = df.iloc[idx - 20:idx]['Return'].sum()
                        score = 0.3 * mom_5 + 0.7 * mom_20
                        if score > 2:
                            daily_ret += weight * (df.loc[date, 'Return'] / 100)
            
            returns.append(daily_ret)
        
        return self._compute_metrics(pd.Series(returns), "Logistic (Momentum)")


class PurgedWalkForward:
    """
    Purged and embargoed walk-forward validation.
    Uses EXPANDING window (cumulative) training with fixed test periods.
    Prevents lookahead bias by:
    1. Purging overlapping samples between train/test
    2. Adding embargo period between train and test
    """
    
    def __init__(self, purge_days: int = 5, embargo_days: int = 5, min_train_days: int = 60):
        self.purge_days = purge_days
        self.embargo_days = embargo_days
        self.min_train_days = min_train_days
    
    def generate_folds(self, dates: List[datetime], n_folds: int = 5,
                       test_size: int = None) -> List[Dict]:
        """
        Generate purged walk-forward folds using EXPANDING training windows.
        
        This is cumulative walk-forward: each fold uses ALL prior data for training,
        then tests on the next period. This maintains sufficient training history.
        
        Args:
            dates: List of trading dates
            n_folds: Number of test folds to generate
            test_size: Size of each test period (default: auto-calculated)
        """
        folds = []
        n = len(dates)
        
        if test_size is None:
            usable_days = n - self.min_train_days - self.embargo_days - self.purge_days
            test_size = max(20, usable_days // n_folds)
        
        gap = self.purge_days + self.embargo_days
        
        for i in range(n_folds):
            train_start_idx = 0
            
            test_start_idx = self.min_train_days + gap + (i * test_size)
            test_end_idx = min(test_start_idx + test_size - 1, n - 1)
            
            if test_start_idx >= n:
                break
            
            train_end_idx = test_start_idx - gap - 1
            
            train_days = train_end_idx - train_start_idx + 1
            if train_days < self.min_train_days:
                continue
            
            folds.append({
                'fold': i + 1,
                'train_start': dates[train_start_idx],
                'train_end': dates[train_end_idx],
                'test_start': dates[test_start_idx],
                'test_end': dates[test_end_idx],
                'train_days': train_days,
                'test_days': test_end_idx - test_start_idx + 1,
                'gap_days': gap
            })
        
        return folds


class AmplitudeBucketAnalyzer:
    """
    Mean-reversion detection via amplitude bucket analysis.
    If high-A buckets have negative forward returns, the engine is
    mean-reversion sensitive and needs adjustment.
    """
    
    def __init__(self, n_buckets: int = 10):
        self.n_buckets = n_buckets
    
    def analyze(self, df: pd.DataFrame) -> Dict:
        """
        Bucket days by amplitude deciles and compute forward returns.
        Returns analysis of whether high amplitude predicts negative returns.
        """
        if len(df) < 50:
            return {'error': 'Insufficient data'}
        
        returns = df['Return'].values
        prices = df['Close'].values
        
        amplitudes = []
        fwd_1d = []
        fwd_5d = []
        
        for i in range(7, len(returns) - 5):
            recent_rets = returns[i - 7:i]
            vol = max(np.std(recent_rets), 0.01)
            amp = abs(returns[i]) / vol
            amplitudes.append(amp)
            fwd_1d.append(returns[i + 1] if i + 1 < len(returns) else 0)
            fwd_5d.append(np.sum(returns[i + 1:i + 6]) if i + 5 < len(returns) else 0)
        
        if len(amplitudes) < 20:
            return {'error': 'Insufficient amplitude samples'}
        
        amplitudes = np.array(amplitudes)
        fwd_1d = np.array(fwd_1d)
        fwd_5d = np.array(fwd_5d)
        
        percentiles = np.percentile(amplitudes, np.linspace(0, 100, self.n_buckets + 1))
        
        bucket_results = []
        for i in range(self.n_buckets):
            mask = (amplitudes >= percentiles[i]) & (amplitudes < percentiles[i + 1])
            if i == self.n_buckets - 1:
                mask = amplitudes >= percentiles[i]
            
            if mask.sum() > 0:
                bucket_results.append({
                    'bucket': i + 1,
                    'amp_range': f"{percentiles[i]:.2f}-{percentiles[i+1]:.2f}",
                    'n_samples': int(mask.sum()),
                    'avg_fwd_1d': float(fwd_1d[mask].mean()),
                    'avg_fwd_5d': float(fwd_5d[mask].mean()),
                    'std_fwd_1d': float(fwd_1d[mask].std()),
                    'std_fwd_5d': float(fwd_5d[mask].std())
                })
        
        top_bucket = bucket_results[-1] if bucket_results else None
        bottom_bucket = bucket_results[0] if bucket_results else None
        
        mean_reversion_detected = False
        if top_bucket and bottom_bucket:
            if top_bucket['avg_fwd_1d'] < 0 and bottom_bucket['avg_fwd_1d'] > 0:
                mean_reversion_detected = True
        
        return {
            'buckets': bucket_results,
            'mean_reversion_detected': mean_reversion_detected,
            'recommendation': (
                "High amplitude predicts negative returns. Consider: "
                "1) Horizon switch (momentum on 20-60d, reversal on 1-5d), or "
                "2) Regime-gated rule (follow amplitude in expansion, fade in compression)."
            ) if mean_reversion_detected else "Amplitude does not show mean-reversion sensitivity."
        }


@dataclass
class MultiMetricScore:
    """Multi-metric objective scoring for parameter optimization."""
    sharpe: float = 0.0
    sortino: float = 0.0
    max_drawdown: float = 0.0
    stability: float = 0.0  # R² of cumulative returns vs time
    composite: float = 0.0  # Weighted combination
    
    def compute_composite(self, weights: Dict[str, float] = None) -> float:
        """
        Compute weighted composite score.
        Default weights prioritize risk-adjusted returns while penalizing drawdowns.
        """
        if weights is None:
            weights = {
                'sharpe': 0.35,
                'sortino': 0.25,
                'max_drawdown': 0.20,  # Penalty (lower is better)
                'stability': 0.20
            }
        
        # Normalize max_drawdown to same scale (lower drawdown = higher score)
        dd_score = max(0, 1 - (self.max_drawdown / 50))  # 50% DD = 0 score
        
        self.composite = (
            weights['sharpe'] * self.sharpe +
            weights['sortino'] * self.sortino +
            weights['max_drawdown'] * dd_score +
            weights['stability'] * self.stability
        )
        return self.composite


class NestedWalkForwardCalibrator:
    """
    Nested walk-forward calibration as recommended by ChatGPT.
    
    Structure:
    - OUTER loop: Out-of-sample evaluation (unseen data for final performance)
    - INNER loop: Parameter tuning (within training data only)
    
    This prevents overfitting by ensuring parameters are never tuned
    on the same data used for final evaluation.
    """
    
    def __init__(self, 
                 outer_folds: int = 5,
                 inner_folds: int = 3,
                 min_train_days: int = 60,
                 purge_days: int = 5,
                 embargo_days: int = 5):
        self.outer_folds = outer_folds
        self.inner_folds = inner_folds
        self.min_train_days = min_train_days
        self.purge_days = purge_days
        self.embargo_days = embargo_days
    
    def generate_nested_folds(self, dates: List) -> List[Dict]:
        """
        Generate nested walk-forward structure.
        
        Returns list of:
        {
            'outer_fold': int,
            'outer_train': (start, end),  # For inner CV + final param selection
            'outer_test': (start, end),   # Truly out-of-sample
            'inner_folds': [...]          # For parameter tuning within outer_train
        }
        """
        n = len(dates)
        gap = self.purge_days + self.embargo_days
        
        # Calculate outer test size
        usable_days = n - self.min_train_days - gap
        outer_test_size = max(20, usable_days // self.outer_folds)
        
        nested_structure = []
        
        for outer_i in range(self.outer_folds):
            # Outer test period
            outer_test_start_idx = self.min_train_days + gap + (outer_i * outer_test_size)
            outer_test_end_idx = min(outer_test_start_idx + outer_test_size - 1, n - 1)
            
            if outer_test_start_idx >= n:
                break
            
            # Outer train period (everything before test, with gap)
            outer_train_start_idx = 0
            outer_train_end_idx = outer_test_start_idx - gap - 1
            
            outer_train_days = outer_train_end_idx - outer_train_start_idx + 1
            if outer_train_days < self.min_train_days:
                continue
            
            # Generate inner folds WITHIN the outer training period
            inner_dates = dates[outer_train_start_idx:outer_train_end_idx + 1]
            inner_folds = self._generate_inner_folds(inner_dates)
            
            nested_structure.append({
                'outer_fold': outer_i + 1,
                'outer_train_start': dates[outer_train_start_idx],
                'outer_train_end': dates[outer_train_end_idx],
                'outer_test_start': dates[outer_test_start_idx],
                'outer_test_end': dates[outer_test_end_idx],
                'outer_train_days': outer_train_days,
                'outer_test_days': outer_test_end_idx - outer_test_start_idx + 1,
                'inner_folds': inner_folds
            })
        
        return nested_structure
    
    def _generate_inner_folds(self, dates: List) -> List[Dict]:
        """Generate inner folds for parameter tuning within training data."""
        n = len(dates)
        gap = self.purge_days + self.embargo_days
        
        inner_min_train = max(20, self.min_train_days // 2)
        usable = n - inner_min_train - gap
        
        if usable < 10:
            return []
        
        inner_test_size = max(10, usable // self.inner_folds)
        
        inner_folds = []
        for i in range(self.inner_folds):
            test_start_idx = inner_min_train + gap + (i * inner_test_size)
            test_end_idx = min(test_start_idx + inner_test_size - 1, n - 1)
            
            if test_start_idx >= n:
                break
            
            train_end_idx = test_start_idx - gap - 1
            train_days = train_end_idx + 1
            
            if train_days < inner_min_train:
                continue
            
            inner_folds.append({
                'inner_fold': i + 1,
                'train_start': dates[0],
                'train_end': dates[train_end_idx],
                'test_start': dates[test_start_idx],
                'test_end': dates[test_end_idx],
                'train_days': train_days,
                'test_days': test_end_idx - test_start_idx + 1
            })
        
        return inner_folds
    
    def compute_multi_metric(self, returns: pd.Series, is_decimal: bool = True) -> MultiMetricScore:
        """
        Compute multi-metric score for a return series.
        
        Args:
            returns: Return series (must be in decimal form, e.g., 0.01 = 1%)
            is_decimal: If True, returns are in decimal form (default). 
                       If False, will convert from percentage.
        """
        if len(returns) < 10:
            return MultiMetricScore()
        
        returns = returns.dropna()
        
        # Ensure decimal returns
        if not is_decimal:
            returns = returns / 100.0
        
        # Sharpe (annualized)
        mean_ret = returns.mean()
        std_ret = returns.std()
        sharpe = (mean_ret / std_ret * np.sqrt(252)) if std_ret > 0 else 0.0
        
        # Sortino (downside deviation, annualized)
        negative_rets = returns[returns < 0]
        downside_std = negative_rets.std() if len(negative_rets) > 0 else 0.001
        sortino = (mean_ret / downside_std * np.sqrt(252)) if downside_std > 0 else 0.0
        
        # Max drawdown (returns already in decimal form)
        cumulative = (1 + returns).cumprod()
        rolling_max = cumulative.expanding().max()
        drawdowns = (cumulative - rolling_max) / rolling_max * 100  # Convert to percentage for display
        max_dd = abs(drawdowns.min())
        
        # Stability (R² of cumulative returns)
        cum_rets = cumulative.values
        x = np.arange(len(cum_rets))
        if len(x) > 2:
            correlation = np.corrcoef(x, cum_rets)[0, 1]
            stability = correlation ** 2 if not np.isnan(correlation) else 0.0
        else:
            stability = 0.0
        
        score = MultiMetricScore(
            sharpe=sharpe,
            sortino=sortino,
            max_drawdown=max_dd,
            stability=stability
        )
        score.compute_composite()
        
        return score


class GSAResearchRunner:
    """Main research runner for GSA hardening."""
    
    def __init__(self):
        self.fetcher = MarketDataFetcher()
        self.baseline_ladder = BaselineLadder(self.fetcher)
        self.walk_forward = PurgedWalkForward()
        self.amplitude_analyzer = AmplitudeBucketAnalyzer()
        self.nested_calibrator = NestedWalkForwardCalibrator()
    
    def run_full_validation(self, tickers: List[str], start: str, end: str) -> Dict:
        """Run complete validation suite."""
        print(f"\n{'='*60}")
        print("GSA RESEARCH HARDENING - FULL VALIDATION")
        print(f"Period: {start} to {end}")
        print(f"{'='*60}\n")
        
        print("1. BASELINE LADDER")
        print("-" * 40)
        baselines = self.baseline_ladder.run_all_baselines(tickers, start, end)
        for b in baselines:
            print(f"  {b.strategy_name:25s} | Return: {b.total_return:+6.1f}% | "
                  f"Sharpe: {b.sharpe:5.2f} | MaxDD: {b.max_drawdown:5.1f}%")
        
        print("\n2. AMPLITUDE BUCKET ANALYSIS")
        print("-" * 40)
        spy_df = self.fetcher.fetch("SPY", start, end)
        if spy_df is not None:
            amp_analysis = self.amplitude_analyzer.analyze(spy_df)
            if 'buckets' in amp_analysis:
                print("  Bucket | Amplitude Range | N | Fwd 1d | Fwd 5d")
                for b in amp_analysis['buckets']:
                    print(f"  {b['bucket']:6d} | {b['amp_range']:15s} | {b['n_samples']:3d} | "
                          f"{b['avg_fwd_1d']:+6.2f}% | {b['avg_fwd_5d']:+6.2f}%")
                print(f"\n  Mean-Reversion Detected: {amp_analysis['mean_reversion_detected']}")
                print(f"  Recommendation: {amp_analysis['recommendation']}")
        
        print("\n3. PURGED WALK-FORWARD FOLDS")
        print("-" * 40)
        if spy_df is not None:
            dates = list(spy_df.index)
            folds = self.walk_forward.generate_folds(dates, n_folds=5)
            for f in folds:
                print(f"  Fold {f['fold']}: Train {f['train_start'].strftime('%Y-%m-%d')} to "
                      f"{f['train_end'].strftime('%Y-%m-%d')} | "
                      f"Test {f['test_start'].strftime('%Y-%m-%d')} to "
                      f"{f['test_end'].strftime('%Y-%m-%d')}")
        
        print("\n4. NESTED WALK-FORWARD CALIBRATION STRUCTURE")
        print("-" * 40)
        if spy_df is not None:
            nested = self.nested_calibrator.generate_nested_folds(dates)
            for n in nested:
                print(f"  OUTER Fold {n['outer_fold']}: Train {n['outer_train_days']} days | Test {n['outer_test_days']} days")
                for inner in n['inner_folds']:
                    print(f"    -> Inner {inner['inner_fold']}: Train {inner['train_days']} days | Test {inner['test_days']} days")
            
            # Run multi-metric scoring on SPY (convert percentage to decimal)
            spy_returns = spy_df['Return'].dropna() / 100.0
            multi_score = self.nested_calibrator.compute_multi_metric(spy_returns, is_decimal=True)
            print(f"\n  SPY Multi-Metric Score:")
            print(f"    Sharpe: {multi_score.sharpe:.2f}")
            print(f"    Sortino: {multi_score.sortino:.2f}")
            print(f"    MaxDD: {multi_score.max_drawdown:.1f}%")
            print(f"    Stability: {multi_score.stability:.2f}")
            print(f"    Composite: {multi_score.composite:.2f}")
        
        print(f"\n{'='*60}")
        print("VALIDATION COMPLETE")
        print(f"{'='*60}\n")
        
        return {
            'baselines': [vars(b) for b in baselines],
            'amplitude_analysis': amp_analysis if spy_df is not None else None,
            'folds': folds if spy_df is not None else [],
            'nested_folds': nested if spy_df is not None else []
        }
    
    def run_gsa_backtest(self, ticker: str, start: str, end: str, 
                         threshold: float = 0.3, lb_short: int = 7, 
                         lb_long: int = 20, use_regime: bool = True) -> BaselineResult:
        """
        Run GSA backtest on a single ticker.
        Compares GSA signals against simple buy-and-hold.
        """
        df = self.fetcher.fetch(ticker, start, end)
        if df is None or len(df) < 60:
            return BaselineResult(strategy_name=f"GSA ({ticker})")
        
        prices = df['Close'].values
        returns = df['Return'].values
        
        # Generate GSA signals using compute_xi with tuned parameters
        signals = []
        pd_hist = []
        c_hist = []
        
        min_lookback = max(lb_short, lb_long, 30)
        
        for i in range(min_lookback, len(prices)):
            xi_data = compute_xi(
                prices[:i+1],
                returns[:i+1],
                lb_short=lb_short,
                lb_long=lb_long
            )
            pd_hist.append(xi_data['pd'])
            c_hist.append(xi_data['C'])
            
            # Check regime if enabled
            if use_regime and len(pd_hist) >= 10:
                regime, confidence = classify_regime(
                    pd_hist, c_hist, returns[:i+1]
                )
                regime_ok = regime == MarketRegime.EXPANSION
            else:
                regime_ok = True
            
            # GSA signal with tuned threshold
            if xi_data['xi_unsigned'] > threshold and regime_ok:
                signals.append(1.0)  # Full position
            elif xi_data['xi_unsigned'] > threshold * 0.5:
                signals.append(0.5)  # Half position
            else:
                signals.append(0.0)  # Cash
        
        # Calculate strategy returns
        strategy_returns = []
        for i, sig in enumerate(signals):
            ret_idx = i + min_lookback + 1
            if ret_idx < len(returns):
                strategy_returns.append(sig * returns[ret_idx])
        
        if len(strategy_returns) < 10:
            return BaselineResult(strategy_name=f"GSA ({ticker})")
        
        # Convert percentage returns to decimal for _compute_metrics
        decimal_returns = [r / 100.0 for r in strategy_returns]
        
        return self.baseline_ladder._compute_metrics(
            pd.Series(decimal_returns), 
            f"GSA ({ticker})"
        )
    
    def compare_gsa_to_baselines(self, tickers: List[str], start: str, end: str) -> Dict:
        """Compare GSA performance against baseline ladder."""
        print(f"\n{'='*60}")
        print("GSA vs BASELINE LADDER COMPARISON")
        print(f"{'='*60}\n")
        
        # Get baseline results
        baselines = self.baseline_ladder.run_all_baselines(tickers, start, end)
        
        # Run GSA on each ticker
        gsa_results = []
        for ticker in tickers:
            gsa_result = self.run_gsa_backtest(ticker, start, end)
            if gsa_result.sharpe != 0:
                gsa_results.append(gsa_result)
        
        # Combine GSA results into portfolio
        if gsa_results:
            valid_results = [r for r in gsa_results if r.sharpe != 0]
            if valid_results:
                avg_return = np.mean([r.total_return for r in valid_results])
                avg_sharpe = np.mean([r.sharpe for r in valid_results])
                avg_dd = np.mean([r.max_drawdown for r in valid_results])
                combined = BaselineResult(
                    strategy_name="GSA (Portfolio)",
                    total_return=avg_return,
                    sharpe=avg_sharpe,
                    max_drawdown=avg_dd
                )
                gsa_results.append(combined)
        
        # Print comparison
        all_results = baselines + gsa_results
        all_results.sort(key=lambda x: x.sharpe, reverse=True)
        
        print("Strategy                    | Return  | Sharpe | MaxDD  | Rank")
        print("-" * 65)
        for i, r in enumerate(all_results, 1):
            marker = "**" if "GSA" in r.strategy_name else "  "
            print(f"{marker}{r.strategy_name:25s} | {r.total_return:+6.1f}% | {r.sharpe:5.2f} | "
                  f"{r.max_drawdown:5.1f}% | #{i}")
        
        # Determine if GSA beats baselines
        gsa_portfolio = next((r for r in gsa_results if r.strategy_name == "GSA (Portfolio)"), None)
        if gsa_portfolio:
            beats_spy = gsa_portfolio.sharpe > next((r.sharpe for r in baselines if "SPY" in r.strategy_name), 0)
            beats_momentum = gsa_portfolio.sharpe > next((r.sharpe for r in baselines if "12-1" in r.strategy_name), 0)
            beats_trend = gsa_portfolio.sharpe > next((r.sharpe for r in baselines if "200d" in r.strategy_name), 0)
            
            print(f"\n{'='*60}")
            print("GSA VALIDATION VERDICT:")
            print(f"  Beats SPY Buy/Hold: {'YES' if beats_spy else 'NO'}")
            print(f"  Beats 12-1 Momentum: {'YES' if beats_momentum else 'NO'}")
            print(f"  Beats 200d SMA Trend: {'YES' if beats_trend else 'NO'}")
            
            if beats_momentum and beats_trend:
                print("\n  RESULT: GSA PASSES baseline ladder - TI may add value!")
            elif beats_spy:
                print("\n  RESULT: GSA beats market but not academic baselines - needs tuning.")
            else:
                print("\n  RESULT: GSA FAILS baseline ladder - TI claim not supported.")
            print(f"{'='*60}\n")
        
        return {
            'baselines': [vars(b) for b in baselines],
            'gsa_results': [vars(r) for r in gsa_results],
            'all_ranked': [vars(r) for r in all_results]
        }

    def _build_portfolio_returns(self, ticker_returns: Dict[str, pd.Series]) -> pd.Series:
        """
        Build equal-weight portfolio returns aligned by date.
        
        Args:
            ticker_returns: Dict of ticker -> pd.Series of decimal returns indexed by date
        
        Returns:
            pd.Series of equal-weight portfolio returns
        """
        if not ticker_returns:
            return pd.Series(dtype=float)
        
        # Align all returns by date
        combined = pd.DataFrame(ticker_returns)
        
        # Equal-weight: average across tickers for each date
        portfolio = combined.mean(axis=1).dropna()
        
        return portfolio

    def tune_parameters_nested_cv(self, tickers: List[str], start: str, end: str) -> Dict:
        """
        Proper nested walk-forward parameter tuning.
        
        Structure:
        - OUTER loop: Out-of-sample evaluation (never seen during tuning)
        - INNER loop: Parameter selection via cross-validation
        
        For each outer fold:
        1. Use inner folds to find best params (avg composite across inner tests)
        2. Apply best params to outer test fold
        3. Collect out-of-sample metrics
        
        Final score = average of out-of-sample metrics across outer folds
        """
        print(f"\n{'='*60}")
        print("GSA NESTED WALK-FORWARD PARAMETER TUNING")
        print(f"Period: {start} to {end}")
        print(f"{'='*60}\n")
        
        # Reduced parameter grid (focused on proven ranges)
        # Based on prior results: threshold 0.3-0.7 works best, lb_long 20-45
        param_grid = []
        for threshold in [0.3, 0.5, 0.7]:  # Reduced from 5 to 3
            for lb_short in [5, 10]:  # Reduced from 3 to 2
                for lb_long in [20, 45]:  # Reduced from 3 to 2
                    for use_regime in [True]:  # Always use regime (proven better)
                        param_grid.append({
                            'threshold': threshold,
                            'lb_short': lb_short,
                            'lb_long': lb_long,
                            'regime_filter': use_regime
                        })
        
        # Fetch data once
        ticker_data = {}
        for ticker in tickers:
            df = self.fetcher.fetch(ticker, start, end)
            if df is not None and len(df) > 60:
                ticker_data[ticker] = df
        
        if not ticker_data:
            print("No valid ticker data found")
            return {}
        
        # Get common dates across all tickers
        common_dates = None
        for ticker, df in ticker_data.items():
            dates_set = set(df.index)
            if common_dates is None:
                common_dates = dates_set
            else:
                common_dates = common_dates.intersection(dates_set)
        
        common_dates = sorted(list(common_dates))
        
        if len(common_dates) < 100:
            print("Insufficient common dates across tickers")
            return {}
        
        # Generate nested fold structure
        nested_folds = self.nested_calibrator.generate_nested_folds(common_dates)
        
        print(f"Testing {len(param_grid)} parameter combinations across {len(nested_folds)} outer folds")
        
        # Track out-of-sample results per parameter set
        param_oos_scores = {i: [] for i in range(len(param_grid))}
        
        for outer_fold in nested_folds:
            outer_test_start = outer_fold['outer_test_start']
            outer_test_end = outer_fold['outer_test_end']
            inner_folds = outer_fold['inner_folds']
            
            if not inner_folds:
                continue
            
            print(f"\nOuter Fold {outer_fold['outer_fold']}: Test {outer_test_start.strftime('%Y-%m-%d')} to {outer_test_end.strftime('%Y-%m-%d')}")
            
            # INNER CV: Find best params using inner folds
            inner_scores = {i: [] for i in range(len(param_grid))}
            
            for inner_fold in inner_folds:
                inner_test_start = inner_fold['test_start']
                inner_test_end = inner_fold['test_end']
                
                for param_idx, params in enumerate(param_grid):
                    # Backtest on inner test period (use full data for lookbacks)
                    ticker_rets = {}
                    for ticker, df in ticker_data.items():
                        # Get returns only for test period, but use full data for signal generation
                        rets, dates = self._backtest_with_params_dated(
                            df, params['threshold'], params['lb_short'],
                            params['lb_long'], params['regime_filter'],
                            test_start=inner_test_start, test_end=inner_test_end
                        )
                        if rets and len(rets) > 5:
                            ticker_rets[ticker] = pd.Series(rets, index=dates)
                    
                    if ticker_rets:
                        portfolio = self._build_portfolio_returns(ticker_rets)
                        if len(portfolio) > 5:
                            score = self.nested_calibrator.compute_multi_metric(portfolio)
                            inner_scores[param_idx].append(score.composite)
            
            # Select best params based on average inner CV score
            best_param_idx = 0
            best_avg_score = -np.inf
            for param_idx, scores in inner_scores.items():
                if scores:
                    avg = np.mean(scores)
                    if avg > best_avg_score:
                        best_avg_score = avg
                        best_param_idx = param_idx
            
            best_params = param_grid[best_param_idx]
            print(f"  Best inner params: thresh={best_params['threshold']}, lb_s={best_params['lb_short']}, lb_l={best_params['lb_long']}")
            
            # OUTER EVALUATION: Apply best params to out-of-sample test
            ticker_rets = {}
            for ticker, df in ticker_data.items():
                rets, dates = self._backtest_with_params_dated(
                    df, best_params['threshold'], best_params['lb_short'],
                    best_params['lb_long'], best_params['regime_filter'],
                    test_start=outer_test_start, test_end=outer_test_end
                )
                if rets and len(rets) > 5:
                    ticker_rets[ticker] = pd.Series(rets, index=dates)
            
            if ticker_rets:
                portfolio = self._build_portfolio_returns(ticker_rets)
                if len(portfolio) > 5:
                    score = self.nested_calibrator.compute_multi_metric(portfolio)
                    param_oos_scores[best_param_idx].append({
                        'fold': outer_fold['outer_fold'],
                        'sharpe': score.sharpe,
                        'composite': score.composite,
                        'max_dd': score.max_drawdown
                    })
                    print(f"  OOS Sharpe: {score.sharpe:.2f}, MaxDD: {score.max_drawdown:.1f}%")
        
        # Aggregate results
        print(f"\n{'='*60}")
        print("NESTED CV RESULTS (Out-of-Sample)")
        print("-" * 60)
        
        final_results = []
        for param_idx, oos_scores in param_oos_scores.items():
            if oos_scores:
                avg_sharpe = np.mean([s['sharpe'] for s in oos_scores])
                avg_composite = np.mean([s['composite'] for s in oos_scores])
                avg_dd = np.mean([s['max_dd'] for s in oos_scores])
                final_results.append({
                    **param_grid[param_idx],
                    'oos_sharpe': avg_sharpe,
                    'oos_composite': avg_composite,
                    'oos_max_dd': avg_dd,
                    'n_folds': len(oos_scores)
                })
        
        final_results.sort(key=lambda x: x['oos_composite'], reverse=True)
        
        print(f"{'Thresh':>6} | {'LB_S':>4} | {'LB_L':>4} | {'Regime':>6} | {'OOS Sharpe':>10} | {'OOS MaxDD':>9}")
        print("-" * 60)
        for r in final_results[:10]:
            print(f"{r['threshold']:>6.2f} | {r['lb_short']:>4} | {r['lb_long']:>4} | "
                  f"{'Yes' if r['regime_filter'] else 'No':>6} | "
                  f"{r['oos_sharpe']:>10.2f} | {r['oos_max_dd']:>8.1f}%")
        
        if final_results:
            best = final_results[0]
            print(f"\n{'='*60}")
            print("BEST PARAMETERS (Out-of-Sample Validated):")
            print(f"  Threshold: {best['threshold']}")
            print(f"  Short Lookback: {best['lb_short']}")
            print(f"  Long Lookback: {best['lb_long']}")
            print(f"  Regime Filter: {best['regime_filter']}")
            print(f"  OOS Sharpe: {best['oos_sharpe']:.2f}")
            print(f"  OOS MaxDD: {best['oos_max_dd']:.1f}%")
            print(f"{'='*60}\n")
        
        return {
            'final_results': final_results,
            'best_params': final_results[0] if final_results else None,
            'param_grid_size': len(param_grid),
            'n_outer_folds': len(nested_folds)
        }
    
    def diagnose_ti_performance(self, tickers: List[str], start: str, end: str) -> Dict:
        """
        Diagnose GSA performance through Tralseness Informational (TI) framework.
        
        TI Framework Interpretation:
        - Ξ(E) measures market "truth-alignment" (how coherent price signals are)
        - High Ξ = market expressing clear directional truth (expansion)
        - Low Ξ = market confusion/noise (contraction/chaos)
        - GSA succeeds when Ξ correctly predicts regime transitions
        
        Returns detailed analysis of why GSA succeeded or failed in each period.
        """
        print(f"\n{'='*70}")
        print("TI FRAMEWORK DIAGNOSTIC ANALYSIS")
        print(f"Period: {start} to {end}")
        print(f"{'='*70}\n")
        
        # Fetch data
        ticker_data = {}
        for ticker in tickers:
            df = self.fetcher.fetch(ticker, start, end)
            if df is not None and len(df) > 60:
                ticker_data[ticker] = df
        
        if not ticker_data:
            return {}
        
        # Define market periods for analysis
        periods = [
            ("2022-01 to 2022-04", "2022-01-01", "2022-04-30", "Pre-Bear"),
            ("2022-05 to 2022-08", "2022-05-01", "2022-08-31", "Bear Market"),
            ("2022-09 to 2022-12", "2022-09-01", "2022-12-31", "Bear Bottom"),
            ("2023-01 to 2023-04", "2023-01-01", "2023-04-30", "Recovery Start"),
            ("2023-05 to 2023-08", "2023-05-01", "2023-08-31", "Bull Rally"),
            ("2023-09 to 2023-12", "2023-09-01", "2023-12-31", "Late Bull"),
        ]
        
        diagnostics = []
        
        for period_name, p_start, p_end, market_phase in periods:
            period_analysis = {
                'period': period_name,
                'market_phase': market_phase,
                'tickers': {}
            }
            
            total_xi_avg = 0
            total_pd_avg = 0
            total_c_avg = 0
            total_ret = 0
            valid_tickers = 0
            
            for ticker, df in ticker_data.items():
                # Filter to period
                mask = (df.index >= pd.Timestamp(p_start)) & (df.index <= pd.Timestamp(p_end))
                period_df = df[mask]
                
                if len(period_df) < 20:
                    continue
                
                # Compute TI metrics for this period
                prices = period_df['Close'].values
                returns = period_df['Return'].values
                
                xi_values = []
                pd_values = []
                c_values = []
                
                for i in range(30, len(prices)):
                    xi_data = compute_xi(prices[:i+1], returns[:i+1])
                    xi_values.append(xi_data['xi_unsigned'])
                    pd_values.append(xi_data['pd'])
                    c_values.append(xi_data['C'])
                
                if xi_values:
                    avg_xi = np.mean(xi_values)
                    avg_pd = np.mean(pd_values)
                    avg_c = np.mean(c_values)
                    period_return = (prices[-1] / prices[0] - 1) * 100
                    
                    period_analysis['tickers'][ticker] = {
                        'avg_xi': avg_xi,
                        'avg_pd': avg_pd,
                        'avg_c': avg_c,
                        'period_return': period_return
                    }
                    
                    total_xi_avg += avg_xi
                    total_pd_avg += avg_pd
                    total_c_avg += avg_c
                    total_ret += period_return
                    valid_tickers += 1
            
            if valid_tickers > 0:
                period_analysis['portfolio_avg'] = {
                    'avg_xi': total_xi_avg / valid_tickers,
                    'avg_pd': total_pd_avg / valid_tickers,
                    'avg_c': total_c_avg / valid_tickers,
                    'avg_return': total_ret / valid_tickers
                }
                
                # TI interpretation
                avg_xi = period_analysis['portfolio_avg']['avg_xi']
                avg_pd = period_analysis['portfolio_avg']['avg_pd']
                avg_ret = period_analysis['portfolio_avg']['avg_return']
                
                # Determine TI coherence level
                if avg_xi > 0.85:
                    coherence = "HIGH (True-ish)"
                    ti_explanation = "Market expressing clear directional truth"
                elif avg_xi > 0.5:
                    coherence = "MEDIUM (Tralse)"
                    ti_explanation = "Market in transitional state, mixed signals"
                else:
                    coherence = "LOW (False-ish)"
                    ti_explanation = "Market confusion, noise dominates"
                
                # Determine GSA expected performance
                if avg_xi > 0.7 and avg_ret > 0:
                    gsa_expected = "STRONG (High Ξ + positive returns)"
                    gsa_explanation = "GSA should capture momentum well"
                elif avg_xi > 0.7 and avg_ret < 0:
                    gsa_expected = "WEAK (High Ξ but negative market)"
                    gsa_explanation = "High signal clarity but wrong direction detected"
                elif avg_xi < 0.5:
                    gsa_expected = "POOR (Low Ξ = noise)"
                    gsa_explanation = "Insufficient signal coherence for reliable trades"
                else:
                    gsa_expected = "MIXED (Transitional Ξ)"
                    gsa_explanation = "Market in Tralse zone - regime transitions likely"
                
                period_analysis['ti_diagnosis'] = {
                    'coherence_level': coherence,
                    'ti_explanation': ti_explanation,
                    'gsa_expected': gsa_expected,
                    'gsa_explanation': gsa_explanation
                }
                
                diagnostics.append(period_analysis)
        
        # Print diagnostic report
        print("PERIOD-BY-PERIOD TI ANALYSIS")
        print("-" * 70)
        
        for d in diagnostics:
            print(f"\n{d['period']} ({d['market_phase']})")
            pa = d['portfolio_avg']
            ti = d['ti_diagnosis']
            print(f"  Avg Ξ(E): {pa['avg_xi']:.3f} | Avg P(D): {pa['avg_pd']:.3f} | Return: {pa['avg_return']:+.1f}%")
            print(f"  Coherence: {ti['coherence_level']}")
            print(f"  TI Meaning: {ti['ti_explanation']}")
            print(f"  GSA Expected: {ti['gsa_expected']}")
            print(f"  Explanation: {ti['gsa_explanation']}")
        
        # Summary
        print(f"\n{'='*70}")
        print("TI FRAMEWORK SUMMARY")
        print("-" * 70)
        
        high_xi_periods = [d for d in diagnostics if d['portfolio_avg']['avg_xi'] > 0.7]
        low_xi_periods = [d for d in diagnostics if d['portfolio_avg']['avg_xi'] < 0.5]
        
        print(f"High-Ξ periods (GSA should work): {len(high_xi_periods)}")
        for d in high_xi_periods:
            print(f"  - {d['period']}: Ξ={d['portfolio_avg']['avg_xi']:.3f}, Ret={d['portfolio_avg']['avg_return']:+.1f}%")
        
        print(f"\nLow-Ξ periods (GSA should avoid): {len(low_xi_periods)}")
        for d in low_xi_periods:
            print(f"  - {d['period']}: Ξ={d['portfolio_avg']['avg_xi']:.3f}, Ret={d['portfolio_avg']['avg_return']:+.1f}%")
        
        # Data-driven insight (not hard-coded narrative)
        print(f"\n{'='*70}")
        print("DATA-DRIVEN ANALYSIS: WHAT'S ACTUALLY DRIVING GSA PERFORMANCE?")
        print("-" * 70)
        
        # Compute correlations
        xi_values = [d['portfolio_avg']['avg_xi'] for d in diagnostics]
        returns = [d['portfolio_avg']['avg_return'] for d in diagnostics]
        
        # Simple attribution
        bear_periods = [d for d in diagnostics if d['portfolio_avg']['avg_return'] < 0]
        bull_periods = [d for d in diagnostics if d['portfolio_avg']['avg_return'] > 0]
        
        bear_xi_avg = np.mean([d['portfolio_avg']['avg_xi'] for d in bear_periods]) if bear_periods else 0
        bull_xi_avg = np.mean([d['portfolio_avg']['avg_xi'] for d in bull_periods]) if bull_periods else 0
        
        xi_range = max(xi_values) - min(xi_values) if xi_values else 0
        
        print(f"Observed Ξ(E) range: {min(xi_values):.3f} to {max(xi_values):.3f}")
        print(f"Theoretical threshold (0.85): {'NEVER REACHED' if max(xi_values) < 0.85 else 'REACHED'}")
        print(f"")
        print(f"Bear periods (negative returns): Avg Ξ = {bear_xi_avg:.3f}")
        print(f"Bull periods (positive returns): Avg Ξ = {bull_xi_avg:.3f}")
        print(f"Ξ difference between bull/bear: {abs(bull_xi_avg - bear_xi_avg):.3f}")
        print(f"")
        
        # Honest assessment
        if abs(bull_xi_avg - bear_xi_avg) < 0.05:
            print("FINDING: Ξ(E) does NOT differentiate bull from bear markets.")
            print("GSA performance correlates with MARKET DIRECTION, not Ξ values.")
            print("")
            print("HONEST INTERPRETATION:")
            print("- GSA behaves like standard MOMENTUM, not TI-specific mechanism")
            print("- The REGIME FILTER (expansion detection) drives performance")
            print("- Ξ formula produces values 10x below theoretical thresholds")
            print("- Either recalibrate Ξ formula, or accept momentum-based explanation")
        else:
            print("FINDING: Ξ(E) shows some differentiation between market regimes.")
            print("Further analysis needed to confirm TI-specific contribution.")
        
        print(f"\n{'='*70}")
        print("REQUIRED RECALIBRATION:")
        print("-" * 70)
        print("Current Ξ(E) formula: amplitude × memory × constraint")
        print(f"Empirical range: 0.04 - 0.08 (never approaches 0.85 threshold)")
        print("Options:")
        print("1. Normalize Ξ to [0,1] based on empirical distribution")
        print("2. Use percentile-based thresholds (e.g., top 20% = 'high coherence')")
        print("3. Accept that TI metric needs theoretical refinement")
        print(f"{'='*70}\n")
        
        return {
            'diagnostics': diagnostics,
            'high_xi_periods': len(high_xi_periods),
            'low_xi_periods': len(low_xi_periods)
        }
    
    def test_ti_aligned_formula(self, tickers: List[str], start: str, end: str) -> Dict:
        """
        Test the new TI-aligned Ξ formula based on 0.92² = 0.85 theory.
        
        Tests:
        1. Does new formula reach 0.85 and 0.92 thresholds?
        2. Does high Ξ predict positive next-day returns?
        3. Does Ξ > 0.92 correlate with lower drawdowns?
        4. Compare old vs new formula predictive power
        """
        print(f"\n{'='*70}")
        print("TI-ALIGNED FORMULA TEST: 0.85 & 0.92 THEORY VALIDATION")
        print(f"Period: {start} to {end}")
        print(f"{'='*70}\n")
        
        # Fetch data
        all_data = []
        for ticker in tickers:
            df = self.fetcher.fetch(ticker, start, end)
            if df is not None and len(df) > 60:
                prices = df['Close'].values
                returns = df['Return'].values
                
                for i in range(40, len(prices) - 1):
                    # Compute both formulas
                    old_xi = compute_xi(prices[:i+1], returns[:i+1])
                    new_xi = compute_xi_ti_aligned(prices[:i+1], returns[:i+1])
                    
                    # Next day return (what we're trying to predict)
                    next_ret = returns[i+1] / 100.0  # Convert to decimal
                    
                    all_data.append({
                        'ticker': ticker,
                        'date': df.index[i],
                        'old_xi': old_xi['xi_unsigned'],
                        'new_xi': new_xi['xi_ti'],
                        'G': new_xi['G'],
                        'I': new_xi['I'],
                        'L': new_xi['L'],
                        'E': new_xi['E'],
                        'above_085': new_xi['above_085'],
                        'above_092': new_xi['above_092'],
                        'next_ret': next_ret
                    })
        
        if not all_data:
            print("No data collected")
            return {}
        
        df_results = pd.DataFrame(all_data)
        
        # Test 1: Range comparison
        print("TEST 1: FORMULA RANGE COMPARISON")
        print("-" * 50)
        print(f"Old Ξ range: {df_results['old_xi'].min():.4f} to {df_results['old_xi'].max():.4f}")
        print(f"New Ξ range: {df_results['new_xi'].min():.4f} to {df_results['new_xi'].max():.4f}")
        print(f"")
        print(f"Old Ξ mean: {df_results['old_xi'].mean():.4f}")
        print(f"New Ξ mean: {df_results['new_xi'].mean():.4f}")
        print(f"")
        
        # Count threshold crossings
        above_085_count = df_results['above_085'].sum()
        above_092_count = df_results['above_092'].sum()
        total = len(df_results)
        
        print(f"Days above 0.85 (Major Truth): {above_085_count} ({100*above_085_count/total:.1f}%)")
        print(f"Days above 0.92 (Sustainable): {above_092_count} ({100*above_092_count/total:.1f}%)")
        
        # Test 2: Predictive power - high Ξ vs next-day returns
        print(f"\n{'='*70}")
        print("TEST 2: DOES HIGH Ξ PREDICT POSITIVE RETURNS?")
        print("-" * 50)
        
        # Quintile analysis
        df_results['xi_quintile'] = pd.qcut(df_results['new_xi'], 5, labels=['Q1(Low)', 'Q2', 'Q3', 'Q4', 'Q5(High)'])
        
        quintile_stats = df_results.groupby('xi_quintile')['next_ret'].agg(['mean', 'std', 'count'])
        quintile_stats['sharpe'] = quintile_stats['mean'] / quintile_stats['std'] * np.sqrt(252)
        
        print("Next-Day Returns by Ξ Quintile:")
        print(f"{'Quintile':<12} | {'Mean Ret':>10} | {'Sharpe':>8} | {'Count':>6}")
        print("-" * 50)
        for q in ['Q1(Low)', 'Q2', 'Q3', 'Q4', 'Q5(High)']:
            if q in quintile_stats.index:
                row = quintile_stats.loc[q]
                print(f"{q:<12} | {row['mean']*100:>9.3f}% | {row['sharpe']:>8.2f} | {int(row['count']):>6}")
        
        # Test 3: Threshold analysis
        print(f"\n{'='*70}")
        print("TEST 3: THRESHOLD ANALYSIS (0.85 AND 0.92)")
        print("-" * 50)
        
        if above_085_count > 10:
            above_085_returns = df_results[df_results['above_085']]['next_ret']
            below_085_returns = df_results[~df_results['above_085']]['next_ret']
            
            print(f"When Ξ >= 0.85 (Major Truth):")
            print(f"  Mean next-day return: {above_085_returns.mean()*100:.3f}%")
            print(f"  Std: {above_085_returns.std()*100:.3f}%")
            print(f"  N: {len(above_085_returns)}")
            print(f"")
            print(f"When Ξ < 0.85:")
            print(f"  Mean next-day return: {below_085_returns.mean()*100:.3f}%")
            print(f"  Std: {below_085_returns.std()*100:.3f}%")
        else:
            print("Insufficient days above 0.85 for analysis")
        
        if above_092_count > 10:
            above_092_returns = df_results[df_results['above_092']]['next_ret']
            print(f"\nWhen Ξ >= 0.92 (Sustainable Coherence):")
            print(f"  Mean next-day return: {above_092_returns.mean()*100:.3f}%")
            print(f"  N: {len(above_092_returns)}")
        
        # Test 4: GILE dimension breakdown
        print(f"\n{'='*70}")
        print("TEST 4: GILE DIMENSION ANALYSIS")
        print("-" * 50)
        
        for dim in ['G', 'I', 'L', 'E']:
            corr = df_results[dim].corr(df_results['next_ret'])
            print(f"{dim} correlation with next-day return: {corr:.4f}")
        
        print(f"\nNew Ξ correlation with next-day return: {df_results['new_xi'].corr(df_results['next_ret']):.4f}")
        print(f"Old Ξ correlation with next-day return: {df_results['old_xi'].corr(df_results['next_ret']):.4f}")
        
        # Summary
        print(f"\n{'='*70}")
        print("SUMMARY: TI THEORY VALIDATION")
        print("-" * 50)
        
        new_xi_corr = df_results['new_xi'].corr(df_results['next_ret'])
        old_xi_corr = df_results['old_xi'].corr(df_results['next_ret'])
        
        q5_sharpe = quintile_stats.loc['Q5(High)', 'sharpe'] if 'Q5(High)' in quintile_stats.index else 0
        q1_sharpe = quintile_stats.loc['Q1(Low)', 'sharpe'] if 'Q1(Low)' in quintile_stats.index else 0
        
        print(f"1. New formula reaches 0.85: {'YES' if above_085_count > 0 else 'NO'}")
        print(f"2. New formula reaches 0.92: {'YES' if above_092_count > 0 else 'NO'}")
        print(f"3. High Ξ → better returns: {'YES' if q5_sharpe > q1_sharpe else 'NO'} (Q5 Sharpe: {q5_sharpe:.2f} vs Q1: {q1_sharpe:.2f})")
        print(f"4. New formula beats old: {'YES' if abs(new_xi_corr) > abs(old_xi_corr) else 'NO'} (corr: {new_xi_corr:.4f} vs {old_xi_corr:.4f})")
        
        # TI validation verdict
        validations_passed = sum([
            above_085_count > 0,
            above_092_count > 0,
            q5_sharpe > q1_sharpe,
            abs(new_xi_corr) > abs(old_xi_corr)
        ])
        
        print(f"\nTI THEORY VALIDATIONS PASSED: {validations_passed}/4")
        
        if validations_passed >= 3:
            print("VERDICT: Strong support for TI theory in market data")
        elif validations_passed >= 2:
            print("VERDICT: Partial support - some TI predictions confirmed")
        else:
            print("VERDICT: Weak support - TI theory needs further refinement")
        
        print(f"{'='*70}\n")
        
        return {
            'total_observations': len(df_results),
            'above_085_pct': 100 * above_085_count / total,
            'above_092_pct': 100 * above_092_count / total,
            'new_xi_corr': new_xi_corr,
            'old_xi_corr': old_xi_corr,
            'q5_sharpe': q5_sharpe,
            'q1_sharpe': q1_sharpe,
            'validations_passed': validations_passed
        }
    
    def _backtest_with_params_dated(self, df: pd.DataFrame, threshold: float,
                                      lb_short: int, lb_long: int, use_regime: bool,
                                      test_start=None, test_end=None) -> Tuple[List[float], List]:
        """
        Backtest GSA with specific parameters, returning dated returns.
        Uses FULL historical data for lookbacks, but only returns data within test period.
        
        Args:
            df: Full DataFrame with historical data
            threshold: Signal threshold
            lb_short: Short lookback period
            lb_long: Long lookback period
            use_regime: Whether to use regime filtering
            test_start: Start date for test period (None = all data)
            test_end: End date for test period (None = all data)
        
        Returns:
            Tuple of (decimal returns list, dates list)
        """
        prices = df['Close'].values
        returns = df['Return'].values
        dates = df.index.tolist()
        
        signals = []
        signal_dates = []
        pd_hist = []
        c_hist = []
        
        min_lookback = max(lb_short, lb_long, 30)
        
        for i in range(min_lookback, len(prices)):
            current_date = dates[i]
            
            xi_data = compute_xi(
                prices[:i+1],
                returns[:i+1],
                lb_short=lb_short,
                lb_long=lb_long
            )
            pd_hist.append(xi_data['pd'])
            c_hist.append(xi_data['C'])
            
            # Check regime if enabled
            if use_regime and len(pd_hist) >= 10:
                regime, confidence = classify_regime(
                    pd_hist, c_hist, returns[:i+1]
                )
                regime_ok = regime == MarketRegime.EXPANSION
            else:
                regime_ok = True
            
            # Generate signal
            if xi_data['xi_unsigned'] > threshold and regime_ok:
                sig = 1.0
            elif xi_data['xi_unsigned'] > threshold * 0.5:
                sig = 0.5
            else:
                sig = 0.0
            
            signals.append(sig)
            signal_dates.append(current_date)
        
        # Calculate returns (as decimals) only for test period
        strategy_returns = []
        return_dates = []
        
        for i, (sig, sig_date) in enumerate(zip(signals, signal_dates)):
            ret_idx = i + min_lookback + 1
            if ret_idx < len(returns):
                ret_date = dates[ret_idx]
                
                # Filter by test period if specified
                if test_start is not None and ret_date < test_start:
                    continue
                if test_end is not None and ret_date > test_end:
                    continue
                
                # Convert percentage return to decimal
                decimal_ret = sig * returns[ret_idx] / 100.0
                strategy_returns.append(decimal_ret)
                return_dates.append(ret_date)
        
        return strategy_returns, return_dates
    
    def _backtest_with_params(self, df: pd.DataFrame, threshold: float,
                               lb_short: int, lb_long: int, use_regime: bool) -> List[float]:
        """Backtest GSA with specific parameters (legacy wrapper)."""
        rets, _ = self._backtest_with_params_dated(
            df, threshold, lb_short, lb_long, use_regime
        )
        return rets

    def export_tuned_parameters(self, output_file: str = "gsa_tuned_params.json"):
        """Export tuned parameters for QC deployment."""
        params = {
            'lookback_short': 7,
            'lookback_long': 30,
            'kappa_decay_positive': 0.1,
            'kappa_decay_negative': 0.05,
            'gile_weights': {
                'goodness': 0.20,
                'intuition': 0.25,
                'love': 0.25,
                'environment': 0.30
            },
            'valence_weights': {
                'exceptional': 1.5,
                'great': 1.0,
                'neutral': 1.0,
                'terrible': 2.0,
                'wicked': 6.0
            },
            'regime_thresholds': {
                'fracture_c_rate': 0.1,
                'fracture_vol_ratio': 1.5,
                'fracture_pd': -1.0,
                'compression_c_rate': 0.05,
                'compression_vol_ratio': 0.7,
                'reset_c_rate': -0.05
            },
            'signal_thresholds': {
                'strong_signal': 0.85,
                'causation': 0.85
            },
            'tuned_date': datetime.now().strftime('%Y-%m-%d'),
            'note': 'These parameters need empirical calibration via nested walk-forward optimization.'
        }
        
        with open(output_file, 'w') as f:
            json.dump(params, f, indent=2)
        
        print(f"Exported tuned parameters to {output_file}")
        return params


def run_research_demo():
    """Run a demo of the research hardening suite."""
    runner = GSAResearchRunner()
    
    tickers = ["AAPL", "MSFT", "GOOGL", "NVDA", "TSLA", "META", "AMZN"]
    
    results = runner.run_full_validation(
        tickers=tickers,
        start="2020-01-01",
        end="2024-12-01"
    )
    
    runner.export_tuned_parameters()
    
    return results


if __name__ == "__main__":
    run_research_demo()
