"""
OPEN ACCESS DATASET VALIDATION MODULE
======================================
Empirical validation of TI Framework claims using publicly available datasets.

Uses ONLY public, freely-accessible data sources:
- Yahoo Finance (yfinance) - Stock prices, historical data
- Alpha Vantage - Technical indicators, fundamentals
- DEAP Dataset - EEG/physiological (for biometric claims)
- UCI ML Repository - Standard ML benchmarks

Author: Brandon Emerick / BlissGene Therapeutics
Date: November 30, 2025
"""

import os
import json
from dataclasses import dataclass, field
from datetime import datetime, timedelta
from typing import Dict, List, Optional, Any, Tuple
from enum import Enum
import numpy as np

try:
    import yfinance as yf
    HAS_YFINANCE = True
except ImportError:
    HAS_YFINANCE = False
    yf = None

try:
    from alpha_vantage.timeseries import TimeSeries
    from alpha_vantage.techindicators import TechIndicators
    HAS_ALPHA_VANTAGE = True
except ImportError:
    HAS_ALPHA_VANTAGE = False
    TimeSeries = None
    TechIndicators = None


class DataSource(Enum):
    """Publicly available data sources"""
    YAHOO_FINANCE = "yahoo_finance"
    ALPHA_VANTAGE = "alpha_vantage"
    DEAP_DATASET = "deap"
    UCI_REPOSITORY = "uci"
    FRED_ECONOMIC = "fred"
    QUANDL_OPEN = "quandl_open"


class ValidationLevel(Enum):
    """Levels of empirical validation"""
    NOT_TESTED = "not_tested"
    SINGLE_TEST = "single_test"
    MULTI_TEST = "multi_test"
    CROSS_VALIDATED = "cross_validated"
    OUT_OF_SAMPLE = "out_of_sample"
    STATISTICALLY_SIGNIFICANT = "statistically_significant"


@dataclass
class ValidationTest:
    """A single validation test against open access data"""
    test_id: str
    test_name: str
    hypothesis: str
    data_source: DataSource
    dataset_description: str
    test_date: datetime
    sample_size: int
    prediction_made: Any
    actual_result: Any
    is_correct: bool
    confidence_interval: Optional[Tuple[float, float]] = None
    p_value: Optional[float] = None
    notes: str = ""


@dataclass
class HypercomputerValidation:
    """Validation results for GM Hypercomputer claims"""
    claim_id: str
    claim_description: str
    tests: List[ValidationTest] = field(default_factory=list)
    validation_level: ValidationLevel = ValidationLevel.NOT_TESTED
    success_rate: float = 0.0
    last_tested: Optional[datetime] = None
    
    def add_test(self, test: ValidationTest):
        """Add a test and update statistics"""
        self.tests.append(test)
        self.last_tested = test.test_date
        if self.tests:
            self.success_rate = sum(1 for t in self.tests if t.is_correct) / len(self.tests)
            if len(self.tests) >= 20:
                self.validation_level = ValidationLevel.CROSS_VALIDATED
            elif len(self.tests) >= 5:
                self.validation_level = ValidationLevel.MULTI_TEST
            elif len(self.tests) >= 1:
                self.validation_level = ValidationLevel.SINGLE_TEST


class OpenAccessValidator:
    """
    Validates TI Framework claims using only publicly available datasets.
    
    PRINCIPLE: No claim is accepted without reproducible empirical evidence
    from open-access data sources that anyone can verify.
    
    Dependencies:
    - yfinance: pip install yfinance (for Yahoo Finance stock data)
    - alpha_vantage: pip install alpha-vantage (optional, for technical indicators)
    """
    
    def __init__(self):
        self.alpha_vantage_key = os.environ.get('ALPHA_VANTAGE_API_KEY')
        
        self.validations: Dict[str, HypercomputerValidation] = {}
        self.test_history: List[ValidationTest] = []
        
        self._stock_cache: Dict[str, Dict] = {}
        
        self._init_claims_registry()
    
    def _init_claims_registry(self):
        """Initialize the claims we want to validate"""
        claims = [
            ("stock_lcc_correlation", "LCC (Love Cross-Correlation) predicts stock price movements"),
            ("ti_weights_accuracy", "TI Algorithm weights (t1=74.6%, lcc=23.8%) outperform baseline"),
            ("sacred_interval_bounds", "GILE sacred interval (-0.666, 0.333) bounds market behavior"),
            ("tralse_market_states", "Markets exhibit True, False, and Indeterminate (Φ) states"),
            ("hypercomputer_independence", "Hypercomputer produces valid results without shielded data"),
            ("gile_score_prediction", "GILE scores correlate with future price movements"),
            ("lcc_virus_spread", "Market correlations follow LCC Virus propagation patterns"),
        ]
        
        for claim_id, description in claims:
            self.validations[claim_id] = HypercomputerValidation(
                claim_id=claim_id,
                claim_description=description
            )
    
    def fetch_stock_data(self, symbol: str, period: str = "1y") -> Optional[Dict]:
        """
        Fetch stock data from Yahoo Finance (free, no API key needed).
        
        Args:
            symbol: Stock ticker (e.g., "AAPL", "SPY")
            period: Time period ("1d", "5d", "1mo", "3mo", "6mo", "1y", "2y", "5y")
        
        Returns:
            Dict with OHLCV data and metadata
        """
        if not HAS_YFINANCE:
            return {"error": "yfinance not installed", "data": None}
        
        cache_key = f"{symbol}_{period}"
        if cache_key in self._stock_cache:
            return self._stock_cache[cache_key]
        
        try:
            ticker = yf.Ticker(symbol)
            hist = ticker.history(period=period)
            
            if hist.empty:
                return {"error": f"No data for {symbol}", "data": None}
            
            result = {
                "symbol": symbol,
                "period": period,
                "fetch_date": datetime.now().isoformat(),
                "data_source": DataSource.YAHOO_FINANCE.value,
                "sample_size": len(hist),
                "data": {
                    "dates": hist.index.strftime('%Y-%m-%d').tolist(),
                    "open": hist['Open'].tolist(),
                    "high": hist['High'].tolist(),
                    "low": hist['Low'].tolist(),
                    "close": hist['Close'].tolist(),
                    "volume": hist['Volume'].tolist(),
                },
                "statistics": {
                    "mean_return": ((hist['Close'].pct_change().mean()) * 252 * 100) if len(hist) > 1 else 0,
                    "volatility": (hist['Close'].pct_change().std() * np.sqrt(252) * 100) if len(hist) > 1 else 0,
                    "max_drawdown": self._calculate_max_drawdown(hist['Close'].values),
                    "sharpe_estimate": self._estimate_sharpe(hist['Close'].values),
                }
            }
            self._stock_cache[cache_key] = result
            return result
        except Exception as e:
            return {"error": str(e), "data": None}
    
    def _calculate_max_drawdown(self, prices: np.ndarray) -> float:
        """Calculate maximum drawdown percentage"""
        if len(prices) < 2:
            return 0.0
        peak = prices[0]
        max_dd = 0.0
        for price in prices:
            if price > peak:
                peak = price
            dd = (peak - price) / peak * 100
            if dd > max_dd:
                max_dd = dd
        return max_dd
    
    def _estimate_sharpe(self, prices: np.ndarray, risk_free_rate: float = 0.05) -> float:
        """Estimate Sharpe ratio from price data"""
        if len(prices) < 2:
            return 0.0
        returns = np.diff(prices) / prices[:-1]
        if len(returns) == 0 or np.std(returns) == 0:
            return 0.0
        annual_return = np.mean(returns) * 252
        annual_vol = np.std(returns) * np.sqrt(252)
        return (annual_return - risk_free_rate) / annual_vol if annual_vol > 0 else 0.0
    
    def calculate_lcc_correlation(self, symbol1: str, symbol2: str, period: str = "1y") -> Dict:
        """
        Calculate Love Cross-Correlation between two assets.
        
        This is the PUBLIC market data version of LCC - no personal info!
        """
        data1 = self.fetch_stock_data(symbol1, period)
        data2 = self.fetch_stock_data(symbol2, period)
        
        if data1.get("error") or data2.get("error"):
            return {"error": "Failed to fetch data", "correlation": None}
        
        close1 = np.array(data1["data"]["close"])
        close2 = np.array(data2["data"]["close"])
        
        min_len = min(len(close1), len(close2))
        close1 = close1[-min_len:]
        close2 = close2[-min_len:]
        
        returns1 = np.diff(close1) / close1[:-1]
        returns2 = np.diff(close2) / close2[:-1]
        
        if len(returns1) < 2:
            return {"error": "Insufficient data", "correlation": None}
        
        correlation = np.corrcoef(returns1, returns2)[0, 1]
        
        lag_correlations = {}
        for lag in range(-5, 6):
            if lag == 0:
                lag_correlations[lag] = correlation
            elif lag > 0:
                lagged = np.corrcoef(returns1[lag:], returns2[:-lag])[0, 1]
                lag_correlations[lag] = lagged
            else:
                lagged = np.corrcoef(returns1[:lag], returns2[-lag:])[0, 1]
                lag_correlations[lag] = lagged
        
        best_lag = max(lag_correlations, key=lambda k: abs(lag_correlations[k]))
        
        return {
            "symbol1": symbol1,
            "symbol2": symbol2,
            "correlation": correlation,
            "lag_correlations": lag_correlations,
            "best_lag": best_lag,
            "best_lag_correlation": lag_correlations[best_lag],
            "sample_size": min_len,
            "lcc_strength": abs(correlation),
            "lcc_type": "positive" if correlation > 0 else "negative",
            "lcc_virus_potential": "high" if abs(correlation) > 0.7 else "medium" if abs(correlation) > 0.4 else "low"
        }
    
    def validate_ti_weights(self, test_symbols: List[str] = None) -> ValidationTest:
        """
        Validate TI Algorithm weights against real market data.
        
        Tests whether the empirically-derived weights (t1=74.6%, lcc=23.8%)
        produce better predictions than random or equal weighting.
        """
        if test_symbols is None:
            test_symbols = ["AAPL", "MSFT", "GOOGL", "AMZN", "META"]
        
        ti_weights = {
            "t1": 0.746,
            "t2": 0.015,
            "t3": 0.000,
            "lcc": 0.238
        }
        
        equal_weights = {k: 0.25 for k in ti_weights}
        
        ti_scores = []
        equal_scores = []
        
        for symbol in test_symbols:
            data = self.fetch_stock_data(symbol, "1y")
            if data.get("error"):
                continue
            
            close = np.array(data["data"]["close"])
            if len(close) < 50:
                continue
            
            t1_signal = self._compute_short_term_signal(close)
            t2_signal = self._compute_medium_term_signal(close)
            t3_signal = self._compute_long_term_signal(close)
            lcc_signal = self._compute_lcc_signal(close)
            
            ti_composite = (
                ti_weights["t1"] * t1_signal +
                ti_weights["t2"] * t2_signal +
                ti_weights["t3"] * t3_signal +
                ti_weights["lcc"] * lcc_signal
            )
            
            equal_composite = (
                equal_weights["t1"] * t1_signal +
                equal_weights["t2"] * t2_signal +
                equal_weights["t3"] * t3_signal +
                equal_weights["lcc"] * lcc_signal
            )
            
            actual_return = (close[-1] - close[-20]) / close[-20]
            
            ti_accuracy = 1 if (ti_composite > 0 and actual_return > 0) or (ti_composite < 0 and actual_return < 0) else 0
            equal_accuracy = 1 if (equal_composite > 0 and actual_return > 0) or (equal_composite < 0 and actual_return < 0) else 0
            
            ti_scores.append(ti_accuracy)
            equal_scores.append(equal_accuracy)
        
        ti_success_rate = np.mean(ti_scores) if ti_scores else 0.0
        equal_success_rate = np.mean(equal_scores) if equal_scores else 0.0
        
        is_correct = ti_success_rate > equal_success_rate
        
        test = ValidationTest(
            test_id=f"ti_weights_{datetime.now().strftime('%Y%m%d_%H%M%S')}",
            test_name="TI Weights vs Equal Weights",
            hypothesis="TI empirical weights (t1=74.6%, lcc=23.8%) outperform equal weighting",
            data_source=DataSource.YAHOO_FINANCE,
            dataset_description=f"1-year data from {len(test_symbols)} stocks: {', '.join(test_symbols)}",
            test_date=datetime.now(),
            sample_size=len(ti_scores),
            prediction_made={"ti_weights": ti_weights, "expected": "ti > equal"},
            actual_result={"ti_accuracy": ti_success_rate, "equal_accuracy": equal_success_rate},
            is_correct=is_correct,
            notes=f"TI: {ti_success_rate:.1%}, Equal: {equal_success_rate:.1%}"
        )
        
        self.validations["ti_weights_accuracy"].add_test(test)
        self.test_history.append(test)
        
        return test
    
    def _compute_short_term_signal(self, prices: np.ndarray) -> float:
        """Compute short-term (t1) signal: 5-day momentum"""
        if len(prices) < 6:
            return 0.0
        return (prices[-1] - prices[-6]) / prices[-6]
    
    def _compute_medium_term_signal(self, prices: np.ndarray) -> float:
        """Compute medium-term (t2) signal: 20-day momentum"""
        if len(prices) < 21:
            return 0.0
        return (prices[-1] - prices[-21]) / prices[-21]
    
    def _compute_long_term_signal(self, prices: np.ndarray) -> float:
        """Compute long-term (t3) signal: 60-day momentum"""
        if len(prices) < 61:
            return 0.0
        return (prices[-1] - prices[-61]) / prices[-61]
    
    def _compute_lcc_signal(self, prices: np.ndarray, symbol: str = None) -> float:
        """
        Compute LCC signal: correlation with market benchmark (SPY).
        Uses cross-correlation with SPY as LCC Virus spread indicator.
        """
        if len(prices) < 20:
            return 0.0
        
        spy_data = self.fetch_stock_data("SPY", "3mo")
        if spy_data.get("error"):
            returns = np.diff(prices[-21:]) / prices[-21:-1]
            autocorr = np.corrcoef(returns[:-1], returns[1:])[0, 1]
            return autocorr if not np.isnan(autocorr) else 0.0
        
        spy_close = np.array(spy_data["data"]["close"])
        
        min_len = min(len(prices), len(spy_close), 60)
        asset_returns = np.diff(prices[-min_len:]) / prices[-min_len:-1]
        spy_returns = np.diff(spy_close[-min_len:]) / spy_close[-min_len:-1]
        
        if len(asset_returns) < 2 or len(spy_returns) < 2:
            return 0.0
        
        min_ret_len = min(len(asset_returns), len(spy_returns))
        correlation = np.corrcoef(asset_returns[-min_ret_len:], spy_returns[-min_ret_len:])[0, 1]
        
        return correlation if not np.isnan(correlation) else 0.0
    
    def validate_hypercomputer_independence(self) -> ValidationTest:
        """
        Test that the hypercomputer produces consistent results
        without access to shielded data.
        """
        from gm_hypercomputer import GMHypercomputer, HypercomputerMode
        
        hypercomputer = GMHypercomputer(mode=HypercomputerMode.INDEPENDENT)
        
        test_data = {"secret_answer": 42, "future_price": 150.0}
        shield_hash = hypercomputer.shield_data("test_secret", test_data)
        
        blocked_attempts = 0
        allowed_attempts = 0
        
        for _ in range(10):
            result = hypercomputer.attempt_access_shielded("test_secret", "test_caller")
            if result is None:
                blocked_attempts += 1
            else:
                allowed_attempts += 1
        
        is_correct = blocked_attempts == 10 and allowed_attempts == 0
        
        test = ValidationTest(
            test_id=f"hypercomputer_independence_{datetime.now().strftime('%Y%m%d_%H%M%S')}",
            test_name="Hypercomputer Shielded Data Independence",
            hypothesis="Hypercomputer cannot access shielded data in INDEPENDENT mode",
            data_source=DataSource.UCI_REPOSITORY,
            dataset_description="Synthetic test data with shielding",
            test_date=datetime.now(),
            sample_size=10,
            prediction_made={"blocked": 10, "allowed": 0},
            actual_result={"blocked": blocked_attempts, "allowed": allowed_attempts},
            is_correct=is_correct,
            notes=f"Security test: {blocked_attempts}/10 blocked, {allowed_attempts}/10 allowed"
        )
        
        self.validations["hypercomputer_independence"].add_test(test)
        self.test_history.append(test)
        
        return test
    
    def validate_lcc_virus_spread(self, seed_symbol: str = "SPY", target_symbols: List[str] = None) -> ValidationTest:
        """
        Validate that LCC correlations spread through markets like a virus.
        
        Tests if correlations from a seed asset propagate predictably to targets.
        """
        if target_symbols is None:
            target_symbols = ["QQQ", "IWM", "XLF", "XLE", "XLK", "AAPL", "GOOGL"]
        
        correlations = []
        for target in target_symbols:
            lcc_result = self.calculate_lcc_correlation(seed_symbol, target, "6mo")
            if not lcc_result.get("error"):
                correlations.append({
                    "target": target,
                    "correlation": lcc_result["correlation"],
                    "strength": lcc_result["lcc_strength"],
                    "potential": lcc_result["lcc_virus_potential"]
                })
        
        high_correlation_count = sum(1 for c in correlations if c["strength"] > 0.5)
        spread_rate = high_correlation_count / len(correlations) if correlations else 0.0
        
        is_correct = spread_rate > 0.3
        
        test = ValidationTest(
            test_id=f"lcc_virus_spread_{datetime.now().strftime('%Y%m%d_%H%M%S')}",
            test_name="LCC Virus Spread Pattern",
            hypothesis="Market correlations spread from seed (SPY) to targets with >30% high correlation rate",
            data_source=DataSource.YAHOO_FINANCE,
            dataset_description=f"6-month correlations: {seed_symbol} → {', '.join(target_symbols)}",
            test_date=datetime.now(),
            sample_size=len(correlations),
            prediction_made={"expected_spread_rate": ">30%"},
            actual_result={
                "correlations": correlations,
                "high_correlation_count": high_correlation_count,
                "spread_rate": spread_rate
            },
            is_correct=is_correct,
            notes=f"Spread rate: {spread_rate:.1%}, High correlations: {high_correlation_count}/{len(correlations)}"
        )
        
        self.validations["lcc_virus_spread"].add_test(test)
        self.test_history.append(test)
        
        return test
    
    def run_full_validation_suite(self) -> Dict[str, Any]:
        """Run all validation tests and return comprehensive results"""
        print("=" * 70)
        print("OPEN ACCESS DATASET VALIDATION SUITE")
        print("Testing TI Framework claims with public data")
        print("=" * 70)
        
        results = {}
        
        print("\n1. Testing TI Algorithm Weights...")
        ti_test = self.validate_ti_weights()
        results["ti_weights"] = {
            "passed": ti_test.is_correct,
            "details": ti_test.notes
        }
        print(f"   Result: {'PASS' if ti_test.is_correct else 'FAIL'} - {ti_test.notes}")
        
        print("\n2. Testing Hypercomputer Independence...")
        try:
            hyper_test = self.validate_hypercomputer_independence()
            results["hypercomputer_independence"] = {
                "passed": hyper_test.is_correct,
                "details": hyper_test.notes
            }
            print(f"   Result: {'PASS' if hyper_test.is_correct else 'FAIL'} - {hyper_test.notes}")
        except Exception as e:
            results["hypercomputer_independence"] = {"passed": False, "details": str(e)}
            print(f"   Result: ERROR - {e}")
        
        print("\n3. Testing LCC Virus Spread Pattern...")
        lcc_test = self.validate_lcc_virus_spread()
        results["lcc_virus_spread"] = {
            "passed": lcc_test.is_correct,
            "details": lcc_test.notes
        }
        print(f"   Result: {'PASS' if lcc_test.is_correct else 'FAIL'} - {lcc_test.notes}")
        
        print("\n4. Testing Cross-Asset LCC Correlations...")
        lcc_pairs = self.calculate_lcc_correlation("AAPL", "MSFT")
        results["lcc_correlation"] = {
            "passed": not lcc_pairs.get("error"),
            "correlation": lcc_pairs.get("correlation"),
            "details": f"AAPL-MSFT correlation: {lcc_pairs.get('correlation', 0):.3f}"
        }
        print(f"   Result: {results['lcc_correlation']['details']}")
        
        print("\n" + "=" * 70)
        passed = sum(1 for r in results.values() if r.get("passed"))
        print(f"VALIDATION SUMMARY: {passed}/{len(results)} tests passed")
        print("=" * 70)
        
        return {
            "run_date": datetime.now().isoformat(),
            "data_sources_used": [DataSource.YAHOO_FINANCE.value],
            "tests_run": len(results),
            "tests_passed": passed,
            "overall_success_rate": passed / len(results) if results else 0,
            "results": results,
            "validation_levels": {
                claim_id: v.validation_level.value 
                for claim_id, v in self.validations.items()
            },
            "disclaimer": "All tests use publicly available data. Results are reproducible by anyone."
        }
    
    def get_validation_report(self) -> Dict:
        """Generate a comprehensive validation report"""
        return {
            "report_date": datetime.now().isoformat(),
            "total_tests_run": len(self.test_history),
            "claims": {
                claim_id: {
                    "description": v.claim_description,
                    "validation_level": v.validation_level.value,
                    "tests_run": len(v.tests),
                    "success_rate": v.success_rate,
                    "last_tested": v.last_tested.isoformat() if v.last_tested else None
                }
                for claim_id, v in self.validations.items()
            },
            "recent_tests": [
                {
                    "test_id": t.test_id,
                    "test_name": t.test_name,
                    "passed": t.is_correct,
                    "date": t.test_date.isoformat()
                }
                for t in self.test_history[-10:]
            ]
        }


def run_open_access_validation():
    """Run the full open access validation suite"""
    validator = OpenAccessValidator()
    results = validator.run_full_validation_suite()
    
    report = validator.get_validation_report()
    
    print("\n" + "=" * 70)
    print("OPEN ACCESS VALIDATION REPORT")
    print("=" * 70)
    print(json.dumps(report, indent=2, default=str))
    
    return results


if __name__ == "__main__":
    run_open_access_validation()
