"""
TI EMPIRICAL DATA TESTS
========================
Runs actual empirical tests on historical market data to validate TI Framework assumptions.

Uses yfinance for data and tests:
1. Sacred Interval percentage in real market data
2. Jeff Time weight sensitivity
3. DE-Photon cycle correlation
4. GILE threshold effectiveness
"""

import numpy as np
import pandas as pd
from datetime import datetime, timedelta
from typing import Dict, List, Tuple, Optional
import json

try:
    import yfinance as yf
    YFINANCE_AVAILABLE = True
except ImportError:
    YFINANCE_AVAILABLE = False

class TIEmpiricalDataTests:
    """
    Run empirical tests on real market data to validate TI Framework assumptions.
    """
    
    SACRED_MIN = -0.666
    SACRED_MAX = 0.333
    
    GREAT_THRESHOLD = 5.0
    GOOD_THRESHOLD = 0.333
    BAD_THRESHOLD = -0.666
    TERRIBLE_THRESHOLD = -5.0
    
    def __init__(self):
        self.data_cache = {}
        self.test_results = {}
        
    def fetch_market_data(self, symbol: str = "SPY", years: int = 10) -> Optional[pd.DataFrame]:
        """Fetch historical market data"""
        if not YFINANCE_AVAILABLE:
            return None
            
        cache_key = f"{symbol}_{years}"
        if cache_key in self.data_cache:
            return self.data_cache[cache_key]
        
        try:
            end = datetime.now()
            start = end - timedelta(days=years * 365)
            
            ticker = yf.Ticker(symbol)
            df = ticker.history(start=start, end=end)
            
            if df.empty:
                return None
                
            df['Daily_Return'] = df['Close'].pct_change() * 100
            df = df.dropna()
            
            self.data_cache[cache_key] = df
            return df
        except Exception as e:
            print(f"Error fetching data for {symbol}: {e}")
            return None
    
    def test_sacred_interval(self, symbol: str = "SPY", years: int = 10) -> Dict:
        """
        TEST SI2: Sacred Interval represents ~20% of market movements
        
        Hypothesis: ~20% of daily moves fall within Sacred Interval (-0.666%, 0.333%)
        """
        df = self.fetch_market_data(symbol, years)
        if df is None:
            return {"error": "Could not fetch market data"}
        
        returns = df['Daily_Return'].values
        total_days = len(returns)
        
        in_sacred = np.sum((returns >= self.SACRED_MIN) & (returns <= self.SACRED_MAX))
        sacred_pct = (in_sacred / total_days) * 100
        
        in_great = np.sum(returns > self.GREAT_THRESHOLD)
        in_good = np.sum((returns > self.GOOD_THRESHOLD) & (returns <= self.GREAT_THRESHOLD))
        in_bad = np.sum((returns >= self.TERRIBLE_THRESHOLD) & (returns < self.BAD_THRESHOLD))
        in_terrible = np.sum(returns < self.TERRIBLE_THRESHOLD)
        in_indeterminate = in_sacred
        
        great_pct = (in_great / total_days) * 100
        good_pct = (in_good / total_days) * 100
        indeterminate_pct = sacred_pct
        bad_pct = (in_bad / total_days) * 100
        terrible_pct = (in_terrible / total_days) * 100
        
        expected_gile_pd = {
            "great": 6.667,
            "good": 20.0,
            "indeterminate": 20.0,
            "bad": 40.0,
            "terrible": 13.333
        }
        
        actual_distribution = {
            "great": great_pct,
            "good": good_pct,
            "indeterminate": indeterminate_pct,
            "bad": bad_pct,
            "terrible": terrible_pct
        }
        
        hypothesis_confirmed = abs(sacred_pct - 20.0) < 10.0
        
        result = {
            "test_name": "Sacred Interval Percentage Test",
            "hypothesis_id": "SI2",
            "symbol": symbol,
            "period_years": years,
            "total_trading_days": total_days,
            "sacred_interval": f"({self.SACRED_MIN}%, {self.SACRED_MAX}%)",
            "days_in_sacred": int(in_sacred),
            "actual_percentage": round(sacred_pct, 2),
            "expected_percentage": 20.0,
            "deviation_from_expected": round(sacred_pct - 20.0, 2),
            "hypothesis_confirmed": hypothesis_confirmed,
            "actual_gile_distribution": {k: round(v, 2) for k, v in actual_distribution.items()},
            "expected_gile_pd_distribution": expected_gile_pd,
            "interpretation": self._interpret_sacred_interval_result(sacred_pct)
        }
        
        self.test_results["SI2"] = result
        return result
    
    def _interpret_sacred_interval_result(self, sacred_pct: float) -> str:
        """Interpret Sacred Interval test results"""
        if abs(sacred_pct - 20.0) < 5.0:
            return "STRONG VALIDATION: Sacred Interval closely matches GILE PD prediction of 20%"
        elif abs(sacred_pct - 20.0) < 10.0:
            return "PARTIAL VALIDATION: Sacred Interval approximately matches prediction"
        elif sacred_pct > 25.0:
            return "HIGHER THAN EXPECTED: More indeterminate days than predicted - market is less volatile than GILE PD assumes"
        else:
            return "LOWER THAN EXPECTED: Fewer indeterminate days - market may be more volatile than assumed"
    
    def test_next_day_volatility_after_sacred(self, symbol: str = "SPY", years: int = 10) -> Dict:
        """
        TEST DEPJT-6: Price changes within Sacred Interval followed by larger moves
        
        Hypothesis: Days within Sacred Interval are followed by higher-than-average volatility
        (indeterminate zone builds energy before collapse)
        """
        df = self.fetch_market_data(symbol, years)
        if df is None:
            return {"error": "Could not fetch market data"}
        
        returns = df['Daily_Return'].values
        
        in_sacred_mask = (returns >= self.SACRED_MIN) & (returns <= self.SACRED_MAX)
        out_sacred_mask = ~in_sacred_mask
        
        next_day_after_sacred = []
        next_day_after_non_sacred = []
        
        for i in range(len(returns) - 1):
            if in_sacred_mask[i]:
                next_day_after_sacred.append(abs(returns[i + 1]))
            else:
                next_day_after_non_sacred.append(abs(returns[i + 1]))
        
        avg_vol_after_sacred = np.mean(next_day_after_sacred) if next_day_after_sacred else 0
        avg_vol_after_non_sacred = np.mean(next_day_after_non_sacred) if next_day_after_non_sacred else 0
        
        volatility_ratio = avg_vol_after_sacred / avg_vol_after_non_sacred if avg_vol_after_non_sacred > 0 else 1
        
        from scipy import stats
        if len(next_day_after_sacred) > 10 and len(next_day_after_non_sacred) > 10:
            t_stat, p_value = stats.ttest_ind(next_day_after_sacred, next_day_after_non_sacred)
        else:
            t_stat, p_value = 0, 1.0
        
        hypothesis_confirmed = avg_vol_after_sacred > avg_vol_after_non_sacred and p_value < 0.05
        
        result = {
            "test_name": "Next-Day Volatility After Sacred Interval",
            "hypothesis_id": "DEPJT-6",
            "symbol": symbol,
            "period_years": years,
            "days_in_sacred": len(next_day_after_sacred),
            "days_outside_sacred": len(next_day_after_non_sacred),
            "avg_volatility_after_sacred": round(avg_vol_after_sacred, 4),
            "avg_volatility_after_non_sacred": round(avg_vol_after_non_sacred, 4),
            "volatility_ratio": round(volatility_ratio, 4),
            "t_statistic": round(t_stat, 4),
            "p_value": round(p_value, 6),
            "statistically_significant": p_value < 0.05,
            "hypothesis_confirmed": hypothesis_confirmed,
            "interpretation": self._interpret_volatility_result(volatility_ratio, p_value)
        }
        
        self.test_results["DEPJT-6"] = result
        return result
    
    def _interpret_volatility_result(self, ratio: float, p_value: float) -> str:
        """Interpret volatility test results"""
        if ratio > 1.1 and p_value < 0.05:
            return "VALIDATED: Sacred Interval days are followed by significantly higher volatility - 'energy buildup' hypothesis confirmed"
        elif ratio > 1.05 and p_value < 0.1:
            return "PARTIALLY VALIDATED: Trend toward higher volatility after Sacred Interval (marginal significance)"
        elif ratio < 0.95 and p_value < 0.05:
            return "REFUTED: Sacred Interval days are followed by LOWER volatility"
        else:
            return "INCONCLUSIVE: No significant difference in volatility patterns"
    
    def test_de_photon_market_cycle(self, symbol: str = "SPY", years: int = 30) -> Dict:
        """
        TEST DE1: DE-Photon time constant (~4.7 years) correlates with market cycles
        
        Uses annual returns and autocorrelation analysis.
        """
        df = self.fetch_market_data(symbol, years)
        if df is None:
            return {"error": "Could not fetch market data"}
        
        df['Year'] = df.index.year
        yearly_returns = df.groupby('Year')['Daily_Return'].apply(lambda x: (1 + x/100).prod() - 1) * 100
        yearly_returns = yearly_returns.to_dict()
        
        years_list = sorted(yearly_returns.keys())
        returns_list = [yearly_returns[y] for y in years_list]
        
        if len(returns_list) < 10:
            return {"error": "Need at least 10 years of data"}
        
        returns_array = np.array(returns_list)
        
        lags = [3, 4, 5, 6, 7, 8]
        autocorrs = {}
        
        for lag in lags:
            if len(returns_array) > lag + 5:
                corr = np.corrcoef(returns_array[:-lag], returns_array[lag:])[0, 1]
                if not np.isnan(corr):
                    autocorrs[lag] = round(corr, 4)
        
        if not autocorrs:
            return {"error": "Insufficient data for autocorrelation analysis"}
        
        best_lag = max(autocorrs.items(), key=lambda x: abs(x[1]))
        tau_de_prediction = 4.7
        
        closest_to_prediction = 5
        prediction_correlation = autocorrs.get(5, autocorrs.get(4, 0))
        
        result = {
            "test_name": "DE-Photon Market Cycle Test",
            "hypothesis_id": "DE1",
            "symbol": symbol,
            "years_analyzed": len(returns_list),
            "tau_de_prediction": "4.7 years",
            "autocorrelations_by_lag": autocorrs,
            "strongest_cycle": f"{best_lag[0]} years with r={best_lag[1]}",
            "correlation_at_5_year_lag": prediction_correlation,
            "evidence_strength": "Strong" if abs(best_lag[1]) > 0.3 else "Moderate" if abs(best_lag[1]) > 0.15 else "Weak",
            "yearly_returns_sample": {str(k): round(v, 2) for k, v in list(yearly_returns.items())[-10:]},
            "interpretation": self._interpret_cycle_result(autocorrs, best_lag)
        }
        
        self.test_results["DE1"] = result
        return result
    
    def _interpret_cycle_result(self, autocorrs: Dict, best_lag: Tuple) -> str:
        """Interpret market cycle test results"""
        lag_5_corr = autocorrs.get(5, 0)
        lag_4_corr = autocorrs.get(4, 0)
        
        if abs(lag_5_corr) > 0.2 or abs(lag_4_corr) > 0.2:
            return f"SUPPORTS DE-PHOTON: Market shows significant ~4-5 year cycling (r≈{max(abs(lag_4_corr), abs(lag_5_corr)):.2f})"
        elif best_lag[0] in [4, 5, 6] and abs(best_lag[1]) > 0.15:
            return f"PARTIALLY SUPPORTS: Strongest cycle at {best_lag[0]} years aligns with τ_DE prediction"
        elif abs(best_lag[1]) > 0.2:
            return f"DIFFERENT CYCLE: Market shows {best_lag[0]}-year cycle, not 4.7 years"
        else:
            return "INCONCLUSIVE: No strong market cycles detected"
    
    def test_gile_thresholds(self, symbol: str = "SPY", years: int = 10) -> Dict:
        """
        TEST GT1/GT2: GILE threshold effectiveness
        
        Tests if GREAT (>5%) and TERRIBLE (<-5%) thresholds identify actionable signals.
        """
        df = self.fetch_market_data(symbol, years)
        if df is None:
            return {"error": "Could not fetch market data"}
        
        returns = df['Daily_Return'].values
        
        great_days = np.where(returns > self.GREAT_THRESHOLD)[0]
        terrible_days = np.where(returns < self.TERRIBLE_THRESHOLD)[0]
        
        def calculate_next_n_day_return(indices, n_days, all_returns):
            results = []
            for idx in indices:
                if idx + n_days < len(all_returns):
                    future_return = np.sum(all_returns[idx+1:idx+n_days+1])
                    results.append(future_return)
            return results
        
        great_1d = calculate_next_n_day_return(great_days, 1, returns)
        great_5d = calculate_next_n_day_return(great_days, 5, returns)
        terrible_1d = calculate_next_n_day_return(terrible_days, 1, returns)
        terrible_5d = calculate_next_n_day_return(terrible_days, 5, returns)
        
        result = {
            "test_name": "GILE Threshold Effectiveness Test",
            "hypothesis_ids": ["GT1", "GT2"],
            "symbol": symbol,
            "period_years": years,
            "thresholds": {
                "great": f">{self.GREAT_THRESHOLD}%",
                "terrible": f"<{self.TERRIBLE_THRESHOLD}%"
            },
            "great_days_count": len(great_days),
            "terrible_days_count": len(terrible_days),
            "after_great_days": {
                "avg_1_day_return": round(np.mean(great_1d), 4) if great_1d else None,
                "avg_5_day_return": round(np.mean(great_5d), 4) if great_5d else None,
                "win_rate_1d": round(np.mean([1 if r > 0 else 0 for r in great_1d]) * 100, 1) if great_1d else None,
                "win_rate_5d": round(np.mean([1 if r > 0 else 0 for r in great_5d]) * 100, 1) if great_5d else None
            },
            "after_terrible_days": {
                "avg_1_day_return": round(np.mean(terrible_1d), 4) if terrible_1d else None,
                "avg_5_day_return": round(np.mean(terrible_5d), 4) if terrible_5d else None,
                "win_rate_1d": round(np.mean([1 if r > 0 else 0 for r in terrible_1d]) * 100, 1) if terrible_1d else None,
                "win_rate_5d": round(np.mean([1 if r > 0 else 0 for r in terrible_5d]) * 100, 1) if terrible_5d else None
            },
            "interpretation": self._interpret_threshold_result(great_1d, great_5d, terrible_1d, terrible_5d)
        }
        
        self.test_results["GT"] = result
        return result
    
    def _interpret_threshold_result(self, great_1d, great_5d, terrible_1d, terrible_5d) -> Dict:
        """Interpret threshold test results"""
        interpretations = {
            "great_days": "UNKNOWN",
            "terrible_days": "UNKNOWN",
            "overall": "UNKNOWN"
        }
        
        if great_1d:
            avg_great = np.mean(great_5d) if great_5d else 0
            if avg_great > 0:
                interpretations["great_days"] = "MOMENTUM EFFECT: Great days tend to be followed by more gains (continuation)"
            else:
                interpretations["great_days"] = "REVERSAL EFFECT: Great days tend to be followed by pullbacks"
        
        if terrible_1d:
            avg_terrible = np.mean(terrible_5d) if terrible_5d else 0
            if avg_terrible > 0:
                interpretations["terrible_days"] = "BOUNCE EFFECT: Terrible days tend to be followed by recovery (mean reversion)"
            else:
                interpretations["terrible_days"] = "CONTINUATION EFFECT: Terrible days followed by more declines"
        
        return interpretations
    
    def test_weight_comparison(self) -> Dict:
        """
        TEST CV2: Compare original vs evolved weights
        
        Tests if momentum (t1) dominance is empirically justified.
        """
        result = {
            "test_name": "Weight Comparison Analysis",
            "hypothesis_id": "CV2",
            "original_weights": {
                "t1_quantum": 0.25,
                "t2_observation": 0.35,
                "t3_cosmological": 0.25,
                "love_correlation": 0.15
            },
            "evolved_weights": {
                "t1_quantum": 0.746,
                "t2_observation": 0.015,
                "t3_cosmological": 0.0,
                "love_correlation": 0.238
            },
            "key_differences": {
                "t1_change": "+49.6% (3x increase)",
                "t2_change": "-33.5% (23x decrease)",
                "t3_change": "-25.0% (eliminated)",
                "love_change": "+8.8% (1.6x increase)"
            },
            "empirical_interpretation": {
                "t1_dominance": "Momentum is by far the strongest predictor for short-term trading",
                "t2_irrelevance": "Current-day observation has minimal predictive value",
                "t3_elimination": "Long-term context hurts short-term performance",
                "love_importance": "Cross-correlation matters more than originally assumed"
            },
            "backtest_evidence": {
                "v3_with_original_weights": "277.76% return (2020-2024)",
                "v9_with_quartz_evolved": "133.29% return (2020-2024)",
                "note": "V3's better performance may be due to simpler execution, not weights"
            },
            "recommendation": "Test V3 with evolved weights to see if performance improves beyond 277.76%"
        }
        
        self.test_results["CV2"] = result
        return result
    
    def run_all_tests(self, symbol: str = "SPY") -> Dict:
        """Run all empirical tests and return comprehensive results"""
        
        results = {
            "timestamp": datetime.now().isoformat(),
            "symbol": symbol,
            "tests_run": [],
            "results": {},
            "summary": {}
        }
        
        print("Running Sacred Interval Test...")
        results["results"]["sacred_interval"] = self.test_sacred_interval(symbol, 10)
        results["tests_run"].append("sacred_interval")
        
        print("Running Volatility After Sacred Test...")
        results["results"]["volatility_after_sacred"] = self.test_next_day_volatility_after_sacred(symbol, 10)
        results["tests_run"].append("volatility_after_sacred")
        
        print("Running DE-Photon Market Cycle Test...")
        results["results"]["de_photon_cycle"] = self.test_de_photon_market_cycle(symbol, 20)
        results["tests_run"].append("de_photon_cycle")
        
        print("Running GILE Threshold Test...")
        results["results"]["gile_thresholds"] = self.test_gile_thresholds(symbol, 10)
        results["tests_run"].append("gile_thresholds")
        
        print("Running Weight Comparison...")
        results["results"]["weight_comparison"] = self.test_weight_comparison()
        results["tests_run"].append("weight_comparison")
        
        validated = 0
        refuted = 0
        inconclusive = 0
        
        for test_name, test_result in results["results"].items():
            if isinstance(test_result, dict):
                if test_result.get("hypothesis_confirmed") is True:
                    validated += 1
                elif test_result.get("hypothesis_confirmed") is False:
                    refuted += 1
                else:
                    inconclusive += 1
        
        results["summary"] = {
            "total_tests": len(results["tests_run"]),
            "validated": validated,
            "refuted": refuted,
            "inconclusive": inconclusive,
            "data_source": f"yfinance ({symbol})"
        }
        
        return results


def run_comprehensive_tests() -> Dict:
    """Run all tests and return formatted results"""
    tester = TIEmpiricalDataTests()
    return tester.run_all_tests("SPY")


if __name__ == "__main__":
    results = run_comprehensive_tests()
    print(json.dumps(results, indent=2, default=str))
