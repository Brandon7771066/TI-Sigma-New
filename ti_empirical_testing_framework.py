"""
TI EMPIRICAL TESTING FRAMEWORK
==============================
Tests ALL assumptions in TI trading algorithms with verifiable hypotheses.

CORE PRINCIPLE: No TI theory is proven until empirically validated.

ASSUMPTIONS TO TEST:
1. Jeff Time Weights (t1=25%, t2=35%, t3=25%, love=15%)
2. Sacred Interval (-0.666, 0.333) as indeterminate/opportunity zone
3. GILE Thresholds (Great=5%, Terrible=-5%, etc.)
4. DE-Photon Time integration with trading signals
5. Love dimension (cross-correlation) predictive power

VALIDATION STANDARDS:
- Backtest Return > 200% (V3 baseline: 277.76%)
- Sharpe Ratio > 1.0
- Win Rate > 50%
- Statistical significance: p < 0.05
"""

import numpy as np
from dataclasses import dataclass, field
from typing import Dict, List, Optional, Tuple
from enum import Enum
from datetime import datetime
import json

class ValidationStatus(Enum):
    VALIDATED = "validated"
    PARTIALLY_VALIDATED = "partially_validated"
    UNVERIFIED = "unverified"
    REFUTED = "refuted"
    TESTING = "testing"

@dataclass
class TestableHypothesis:
    """A single testable hypothesis with clear acceptance criteria"""
    hypothesis_id: str
    description: str
    assumption_source: str
    null_hypothesis: str
    alternative_hypothesis: str
    test_method: str
    acceptance_criteria: Dict
    current_evidence: Dict = field(default_factory=dict)
    status: ValidationStatus = ValidationStatus.UNVERIFIED
    test_date: Optional[str] = None
    p_value: Optional[float] = None
    effect_size: Optional[float] = None
    notes: str = ""

@dataclass
class EmpiricalResult:
    """Result from an empirical test"""
    hypothesis_id: str
    test_name: str
    metric_name: str
    expected_value: float
    actual_value: float
    within_tolerance: bool
    confidence_interval: Tuple[float, float]
    sample_size: int
    test_date: str

class TIEmpiricalTestingFramework:
    """
    Comprehensive framework for testing all TI trading algorithm assumptions.
    
    Tests are organized by category:
    1. WEIGHT ASSUMPTIONS - t1/t2/t3/love weights
    2. INTERVAL ASSUMPTIONS - Sacred Interval boundaries
    3. THRESHOLD ASSUMPTIONS - GILE thresholds
    4. DE-PHOTON PREDICTIONS - Time dilation effects
    5. CROSS-VALIDATION - Algorithm comparison
    """
    
    def __init__(self):
        self.hypotheses: Dict[str, TestableHypothesis] = {}
        self.results: List[EmpiricalResult] = []
        self._define_all_hypotheses()
        
    def _define_all_hypotheses(self):
        """Define all testable hypotheses from TI algorithm assumptions"""
        
        # =====================================================================
        # CATEGORY 1: JEFF TIME WEIGHT ASSUMPTIONS
        # =====================================================================
        
        self.hypotheses["W1"] = TestableHypothesis(
            hypothesis_id="W1",
            description="t1 (Quantum/Potential) weight of 25% is optimal",
            assumption_source="ti_quantconnect_jeff_time_v3.py line 83",
            null_hypothesis="t1 weight has no effect on returns",
            alternative_hypothesis="t1 weight significantly affects returns",
            test_method="Grid search optimization across weight space",
            acceptance_criteria={
                "optimal_weight_range": (0.20, 0.30),
                "improvement_threshold": 0.0,  # Must not hurt performance
                "p_value_threshold": 0.05
            },
            current_evidence={
                "original_weight": 0.25,
                "evolved_weight": 0.746,  # From TI Performance Cartography
                "discrepancy": "Evolved weight is 3x higher than original"
            },
            status=ValidationStatus.PARTIALLY_VALIDATED,
            notes="Evolved weights suggest t1 should be ~75%, not 25%"
        )
        
        self.hypotheses["W2"] = TestableHypothesis(
            hypothesis_id="W2",
            description="t2 (Jeff Moment/Observation) weight of 35% is optimal",
            assumption_source="ti_quantconnect_jeff_time_v3.py line 86",
            null_hypothesis="t2 weight has no effect on returns",
            alternative_hypothesis="t2 weight significantly affects returns",
            test_method="Grid search optimization",
            acceptance_criteria={
                "optimal_weight_range": (0.30, 0.40),
                "improvement_threshold": 0.0
            },
            current_evidence={
                "original_weight": 0.35,
                "evolved_weight": 0.015,  # Nearly zero!
                "discrepancy": "Evolved weight is 23x LOWER than original"
            },
            status=ValidationStatus.REFUTED,
            notes="CRITICAL: Evolved data shows t2 should be ~1.5%, not 35%!"
        )
        
        self.hypotheses["W3"] = TestableHypothesis(
            hypothesis_id="W3",
            description="t3 (Cosmological/Context) weight of 25% is optimal",
            assumption_source="ti_quantconnect_jeff_time_v3.py line 91",
            null_hypothesis="t3 weight has no effect on returns",
            alternative_hypothesis="t3 weight significantly affects returns",
            test_method="Grid search optimization",
            acceptance_criteria={
                "optimal_weight_range": (0.20, 0.30),
                "improvement_threshold": 0.0
            },
            current_evidence={
                "original_weight": 0.25,
                "evolved_weight": 0.0,  # ELIMINATED!
                "discrepancy": "Evolved weight is ZERO"
            },
            status=ValidationStatus.REFUTED,
            notes="CRITICAL: t3 (long-term context) was ELIMINATED by evolution for short-term trading"
        )
        
        self.hypotheses["W4"] = TestableHypothesis(
            hypothesis_id="W4",
            description="Love (Cross-correlation) weight of 15% is optimal",
            assumption_source="ti_quantconnect_jeff_time_v3.py line 94",
            null_hypothesis="Love weight has no effect on returns",
            alternative_hypothesis="Love weight significantly affects returns",
            test_method="Grid search optimization",
            acceptance_criteria={
                "optimal_weight_range": (0.10, 0.20),
                "improvement_threshold": 0.0
            },
            current_evidence={
                "original_weight": 0.15,
                "evolved_weight": 0.238,  # Higher!
                "discrepancy": "Evolved weight is 1.6x higher"
            },
            status=ValidationStatus.PARTIALLY_VALIDATED,
            notes="Love dimension (correlation) matters MORE than originally assumed"
        )
        
        # =====================================================================
        # CATEGORY 2: SACRED INTERVAL ASSUMPTIONS
        # =====================================================================
        
        self.hypotheses["SI1"] = TestableHypothesis(
            hypothesis_id="SI1",
            description="Sacred Interval (-0.666, 0.333) identifies indeterminate zones",
            assumption_source="ti_quantconnect_jeff_time_v3.py lines 64-65",
            null_hypothesis="Sacred Interval has no predictive power for price movements",
            alternative_hypothesis="Price changes within Sacred Interval have different characteristics than outside",
            test_method="Statistical comparison of returns inside vs outside interval",
            acceptance_criteria={
                "volatility_difference_significance": 0.05,
                "return_distribution_difference": 0.05
            },
            current_evidence={
                "sacred_min": -0.666,
                "sacred_max": 0.333,
                "derivation": "Pareto 80/20 synthesis with Riemann Hypothesis"
            },
            status=ValidationStatus.UNVERIFIED,
            notes="Need to test if this interval actually identifies unique market behavior"
        )
        
        self.hypotheses["SI2"] = TestableHypothesis(
            hypothesis_id="SI2",
            description="Sacred Interval represents ~20% of market movements",
            assumption_source="GILE PD Distribution theory",
            null_hypothesis="Percentage of moves in Sacred Interval is random",
            alternative_hypothesis="~20% of daily moves fall within Sacred Interval",
            test_method="Historical analysis of daily price changes",
            acceptance_criteria={
                "percentage_range": (0.15, 0.25),  # 15-25%
                "sample_size_min": 1000
            },
            status=ValidationStatus.UNVERIFIED,
            notes="Based on Pareto principle - 20% should be 'indeterminate'"
        )
        
        # =====================================================================
        # CATEGORY 3: GILE THRESHOLD ASSUMPTIONS
        # =====================================================================
        
        self.hypotheses["GT1"] = TestableHypothesis(
            hypothesis_id="GT1",
            description="GREAT threshold at 5% daily change is optimal",
            assumption_source="ti_quantconnect_jeff_time_v3.py line 67",
            null_hypothesis="5% threshold has no predictive value",
            alternative_hypothesis="5% threshold identifies genuine buying opportunities",
            test_method="Backtest with varying thresholds (3%, 5%, 7%, 10%)",
            acceptance_criteria={
                "optimal_threshold_range": (4.0, 6.0),
                "win_rate_above_threshold": 0.55
            },
            current_evidence={
                "current_threshold": 5.0,
                "v3_win_rate": "Unknown - not tracked in backtest"
            },
            status=ValidationStatus.UNVERIFIED
        )
        
        self.hypotheses["GT2"] = TestableHypothesis(
            hypothesis_id="GT2",
            description="TERRIBLE threshold at -5% daily change identifies sell signals",
            assumption_source="ti_quantconnect_jeff_time_v3.py line 68",
            null_hypothesis="-5% threshold has no predictive value for reversals",
            alternative_hypothesis="-5% moves predict continued decline or reversal",
            test_method="Backtest exit signals at varying thresholds",
            acceptance_criteria={
                "loss_avoidance_rate": 0.50,
                "optimal_threshold_range": (-6.0, -4.0)
            },
            status=ValidationStatus.UNVERIFIED
        )
        
        # =====================================================================
        # CATEGORY 4: DE-PHOTON TIME PREDICTIONS
        # =====================================================================
        
        self.hypotheses["DE1"] = TestableHypothesis(
            hypothesis_id="DE1",
            description="DE-Photon time constant (~4.7 years) correlates with market cycles",
            assumption_source="DE_PHOTON_TIME_ICELL_MECHANICS_PAPER.md",
            null_hypothesis="4.7 year cycle has no correlation with market behavior",
            alternative_hypothesis="Market cycles show ~4.7 year periodicity",
            test_method="Fourier analysis of market indices over 50+ years",
            acceptance_criteria={
                "cycle_detection_significance": 0.05,
                "cycle_period_range": (4.0, 5.5)  # years
            },
            current_evidence={
                "tau_de": "1.47 × 10^8 seconds (~4.7 years)",
                "known_cycles": "Presidential cycle (4 years), business cycle (4-6 years)"
            },
            status=ValidationStatus.UNVERIFIED,
            notes="VERIFIABLE: Can test against historical S&P 500 data"
        )
        
        self.hypotheses["DE2"] = TestableHypothesis(
            hypothesis_id="DE2",
            description="GILE-based time dilation affects trading signal timing",
            assumption_source="DE_PHOTON_TIME_ICELL_MECHANICS_PAPER.md equation: τ_effective = τ_DE × exp(GILE/6)",
            null_hypothesis="GILE score has no effect on optimal holding period",
            alternative_hypothesis="Higher GILE signals should be held longer (time dilation)",
            test_method="Compare optimal holding periods for high vs low GILE entries",
            acceptance_criteria={
                "high_gile_holding_period": ">5 days",
                "low_gile_holding_period": "<3 days",
                "correlation_with_prediction": 0.5
            },
            status=ValidationStatus.UNVERIFIED,
            notes="VERIFIABLE: Can test with entry GILE vs optimal exit timing"
        )
        
        self.hypotheses["DE3"] = TestableHypothesis(
            hypothesis_id="DE3",
            description="HRV-GILE correlation of r=0.65 for consciousness measurement",
            assumption_source="DE_PHOTON_TIME_ICELL_MECHANICS_PAPER.md prediction",
            null_hypothesis="HRV has no correlation with GILE state",
            alternative_hypothesis="Higher HRV correlates with higher GILE (r ≈ 0.65)",
            test_method="Biometric study with HRV and GILE self-reports",
            acceptance_criteria={
                "correlation_range": (0.55, 0.75),
                "sample_size_min": 100,
                "p_value_threshold": 0.01
            },
            status=ValidationStatus.UNVERIFIED,
            notes="REQUIRES: Human subjects with Polar H10 data"
        )
        
        # =====================================================================
        # CATEGORY 5: ALGORITHM COMPARISON (CROSS-VALIDATION)
        # =====================================================================
        
        self.hypotheses["CV1"] = TestableHypothesis(
            hypothesis_id="CV1",
            description="V3's simple approach outperforms V9's quartz filtering",
            assumption_source="TI Evidence Registry backtest comparison",
            null_hypothesis="V3 and V9 have equal performance",
            alternative_hypothesis="V3 significantly outperforms V9 due to less aggressive filtering",
            test_method="Paired comparison of returns on same time period",
            acceptance_criteria={
                "v3_return": 277.76,
                "v9_return": 133.29,
                "gap_significance": 0.01
            },
            current_evidence={
                "v3_return": 277.76,
                "v9_return": 133.29,
                "gap": 144.47
            },
            status=ValidationStatus.VALIDATED,
            notes="CONFIRMED: V3 beats V9 by 144.47% - simpler is better"
        )
        
        self.hypotheses["CV2"] = TestableHypothesis(
            hypothesis_id="CV2",
            description="Evolved weights outperform original assumptions",
            assumption_source="TI Performance Cartography evolution",
            null_hypothesis="Original weights (25/35/25/15) perform as well as evolved (74.6/1.5/0/23.8)",
            alternative_hypothesis="Evolved weights significantly outperform original",
            test_method="A/B backtest comparison with both weight sets",
            acceptance_criteria={
                "improvement_threshold": 10.0,  # % improvement
                "statistical_significance": 0.05
            },
            status=ValidationStatus.UNVERIFIED,
            notes="CRITICAL TEST: Are evolved weights actually better?"
        )
    
    def get_all_hypotheses(self) -> Dict[str, TestableHypothesis]:
        """Return all defined hypotheses"""
        return self.hypotheses
    
    def get_hypotheses_by_status(self, status: ValidationStatus) -> List[TestableHypothesis]:
        """Filter hypotheses by validation status"""
        return [h for h in self.hypotheses.values() if h.status == status]
    
    def get_summary(self) -> Dict:
        """Get summary of all hypothesis statuses"""
        summary = {
            "total_hypotheses": len(self.hypotheses),
            "by_status": {},
            "categories": {
                "weight_assumptions": ["W1", "W2", "W3", "W4"],
                "sacred_interval": ["SI1", "SI2"],
                "gile_thresholds": ["GT1", "GT2"],
                "de_photon_predictions": ["DE1", "DE2", "DE3"],
                "cross_validation": ["CV1", "CV2"]
            },
            "critical_findings": []
        }
        
        for status in ValidationStatus:
            count = len([h for h in self.hypotheses.values() if h.status == status])
            summary["by_status"][status.value] = count
        
        # Identify critical findings
        refuted = self.get_hypotheses_by_status(ValidationStatus.REFUTED)
        for h in refuted:
            summary["critical_findings"].append({
                "id": h.hypothesis_id,
                "finding": f"REFUTED: {h.description}",
                "evidence": h.current_evidence,
                "notes": h.notes
            })
        
        return summary
    
    def run_sacred_interval_test(self, daily_returns: List[float]) -> EmpiricalResult:
        """
        Test if Sacred Interval (-0.666%, 0.333%) identifies unique market behavior.
        
        Uses actual daily return data to verify:
        1. What percentage of returns fall in Sacred Interval?
        2. Is this different from random expectation?
        """
        sacred_min = -0.666
        sacred_max = 0.333
        
        returns = np.array(daily_returns)
        in_sacred = np.sum((returns >= sacred_min) & (returns <= sacred_max))
        total = len(returns)
        sacred_percentage = in_sacred / total * 100 if total > 0 else 0
        
        # Expected under uniform distribution over typical range (-3%, 3%)
        expected_range = 6.0  # -3% to 3%
        sacred_range = sacred_max - sacred_min  # 0.999%
        expected_percentage = (sacred_range / expected_range) * 100  # ~16.7%
        
        # Is our percentage significantly different?
        # Using normal approximation for proportion test
        se = np.sqrt(expected_percentage/100 * (1 - expected_percentage/100) / total)
        z_score = (sacred_percentage/100 - expected_percentage/100) / se if se > 0 else 0
        
        result = EmpiricalResult(
            hypothesis_id="SI2",
            test_name="Sacred Interval Percentage Test",
            metric_name="Percentage in Sacred Interval",
            expected_value=20.0,  # TI Framework prediction
            actual_value=sacred_percentage,
            within_tolerance=abs(sacred_percentage - 20.0) < 5.0,
            confidence_interval=(sacred_percentage - 1.96*se*100, sacred_percentage + 1.96*se*100),
            sample_size=total,
            test_date=datetime.now().isoformat()
        )
        
        self.results.append(result)
        return result
    
    def run_weight_sensitivity_test(self, base_return: float, weight_returns: Dict[str, float]) -> Dict:
        """
        Test sensitivity of returns to different weight configurations.
        
        weight_returns format: {"w1_0.25_w2_0.35_w3_0.25_w4_0.15": 277.76, ...}
        """
        best_config = max(weight_returns.items(), key=lambda x: x[1])
        worst_config = min(weight_returns.items(), key=lambda x: x[1])
        
        sensitivity_range = best_config[1] - worst_config[1]
        
        return {
            "base_return": base_return,
            "best_config": best_config,
            "worst_config": worst_config,
            "sensitivity_range": sensitivity_range,
            "sensitivity_percentage": (sensitivity_range / base_return) * 100 if base_return != 0 else 0,
            "recommendation": "Weights matter significantly" if sensitivity_range > 50 else "Weights have minor impact"
        }
    
    def test_de_photon_market_cycle(self, yearly_returns: List[Tuple[int, float]]) -> Dict:
        """
        Test if ~4.7 year cycle exists in market data.
        
        yearly_returns: List of (year, return%) tuples
        """
        if len(yearly_returns) < 20:
            return {"error": "Need at least 20 years of data"}
        
        returns = np.array([r[1] for r in yearly_returns])
        years = np.array([r[0] for r in yearly_returns])
        
        # Simple autocorrelation at different lags
        lags = [3, 4, 5, 6, 7]  # Test around 4.7 years
        autocorrs = {}
        
        for lag in lags:
            if len(returns) > lag:
                corr = np.corrcoef(returns[:-lag], returns[lag:])[0, 1]
                autocorrs[f"{lag}_year_lag"] = float(corr) if not np.isnan(corr) else 0.0
        
        # Find peak correlation
        peak_lag = max(autocorrs.items(), key=lambda x: abs(x[1]))
        
        tau_de_prediction = 4.7  # years
        closest_to_prediction = min(lags, key=lambda x: abs(x - tau_de_prediction))
        
        return {
            "tau_de_prediction": f"{tau_de_prediction} years",
            "autocorrelations": autocorrs,
            "peak_correlation": peak_lag,
            "closest_to_tau_de": f"{closest_to_prediction} year lag with r={autocorrs[f'{closest_to_prediction}_year_lag']:.3f}",
            "evidence_strength": "Strong" if abs(peak_lag[1]) > 0.3 else "Weak" if abs(peak_lag[1]) > 0.1 else "None",
            "conclusion": f"Market shows {'significant' if abs(peak_lag[1]) > 0.2 else 'weak'} {peak_lag[0]} cycling"
        }
    
    def generate_de_photon_jeff_time_predictions(self) -> Dict:
        """
        Generate immediately verifiable predictions integrating DE-Photon Time with Jeff Time.
        
        These predictions should be testable with existing backtest data or near-term market behavior.
        """
        predictions = {
            "timestamp": datetime.now().isoformat(),
            "framework": "DE-Photon Jeff Time Synthesis",
            "verifiable_predictions": []
        }
        
        # Prediction 1: GILE-based holding period
        predictions["verifiable_predictions"].append({
            "prediction_id": "DEPJT-1",
            "description": "High GILE entries (>1.5) should have optimal holding period of 5-7 days (time dilation)",
            "formula": "τ_hold = base_hold × exp(GILE/6)",
            "base_hold_days": 3,
            "test_method": "Backtest entries with GILE >1.5, compare returns at different exit times",
            "expected_result": "Peak returns at 5-7 day hold, not 1-3 days",
            "falsifiable": True
        })
        
        # Prediction 2: Low GILE quick exit
        predictions["verifiable_predictions"].append({
            "prediction_id": "DEPJT-2",
            "description": "Low GILE entries (0.3-0.6) should exit faster (1-2 days) - time contraction",
            "formula": "τ_hold = base_hold × exp(GILE/6)",
            "expected_result": "Entries with GILE 0.3-0.6 perform better with 1-2 day holds",
            "falsifiable": True
        })
        
        # Prediction 3: DE-Photon cycle alignment
        predictions["verifiable_predictions"].append({
            "prediction_id": "DEPJT-3",
            "description": "Entries made during positive τ_DE phase outperform negative phase",
            "cycle_period": "4.7 years",
            "current_phase": "Need to calculate based on market data",
            "test_method": "Compare entry returns by τ_DE phase position",
            "falsifiable": True
        })
        
        # Prediction 4: t1 dominance
        predictions["verifiable_predictions"].append({
            "prediction_id": "DEPJT-4",
            "description": "Momentum (t1) should account for >70% of predictive power in short-term trading",
            "evidence": "Evolved weights show t1=74.6%",
            "test_method": "Feature importance analysis on successful trades",
            "expected_result": "t1 component importance > 0.7",
            "falsifiable": True
        })
        
        # Prediction 5: Love correlation threshold
        predictions["verifiable_predictions"].append({
            "prediction_id": "DEPJT-5",
            "description": "Trades with Love correlation >0.8 in uptrends have >60% win rate",
            "derivation": "High Love = entangled with rising tide",
            "test_method": "Filter trades by Love score and market direction",
            "expected_result": "Win rate correlation with Love score",
            "falsifiable": True
        })
        
        # Prediction 6: Sacred Interval reversals
        predictions["verifiable_predictions"].append({
            "prediction_id": "DEPJT-6",
            "description": "Price changes within Sacred Interval (-0.666%, 0.333%) followed by larger moves",
            "derivation": "Indeterminate zone builds energy before collapse",
            "test_method": "Track next-day volatility after Sacred Interval days",
            "expected_result": "Higher average next-day volatility after Sacred Interval days",
            "falsifiable": True
        })
        
        return predictions


class DEPhotonJeffTimeSynthesis:
    """
    Synthesis of DE-Photon Time with Jeff Time for trading applications.
    
    KEY INTEGRATION:
    - DE-Photon provides the TIME SCALE (τ_DE ≈ 4.7 years base cycle)
    - Jeff Time provides the SIGNAL STRUCTURE (t1/t2/t3 + Love)
    - GILE modulates both through time dilation: τ_effective = τ_DE × exp(GILE/6)
    """
    
    # DE-Photon constants
    TAU_DE_SECONDS = 1.47e8  # ~4.7 years
    TAU_DE_DAYS = TAU_DE_SECONDS / 86400  # ~1701 days
    
    def __init__(self):
        self.gile_dilation_table = self._build_dilation_table()
        
    def _build_dilation_table(self) -> Dict[float, float]:
        """Build GILE to time dilation factor mapping"""
        table = {}
        for gile in np.arange(-3.0, 3.1, 0.5):
            dilation = np.exp(gile / 6)
            table[round(gile, 1)] = round(dilation, 3)
        return table
    
    def get_dilation_factor(self, gile: float) -> float:
        """Calculate time dilation factor for a GILE score"""
        return np.exp(gile / 6)
    
    def get_optimal_holding_period(self, gile: float, base_days: int = 3) -> float:
        """
        Calculate optimal holding period based on GILE time dilation.
        
        Higher GILE = longer hold (time slows down for high-quality states)
        Lower GILE = shorter hold (time speeds up for mechanical states)
        """
        dilation = self.get_dilation_factor(gile)
        return base_days * dilation
    
    def get_de_photon_phase(self, reference_date: datetime, current_date: datetime) -> Dict:
        """
        Calculate current position in DE-Photon cycle.
        
        Uses Jan 1, 2020 as reference point (arbitrary but consistent).
        """
        days_elapsed = (current_date - reference_date).days
        phase = (days_elapsed % self.TAU_DE_DAYS) / self.TAU_DE_DAYS
        
        # Convert to radians for cycle interpretation
        phase_radians = phase * 2 * np.pi
        
        return {
            "days_in_cycle": days_elapsed % self.TAU_DE_DAYS,
            "phase_fraction": phase,
            "phase_radians": phase_radians,
            "phase_name": self._get_phase_name(phase),
            "next_peak_days": int((1.0 - phase) * self.TAU_DE_DAYS) if phase < 0.25 else int((1.25 - phase) * self.TAU_DE_DAYS)
        }
    
    def _get_phase_name(self, phase: float) -> str:
        """Convert phase fraction to named phase"""
        if phase < 0.25:
            return "Rising (Pre-Peak)"
        elif phase < 0.5:
            return "Peak (Maximum)"
        elif phase < 0.75:
            return "Falling (Post-Peak)"
        else:
            return "Trough (Minimum)"
    
    def integrate_with_jeff_time(self, t1: float, t2: float, t3: float, love: float) -> Dict:
        """
        Integrate DE-Photon time dilation with Jeff Time signals.
        
        Original Jeff Time: GILE = w1*t1 + w2*t2 + w3*t3 + wL*Love
        
        DE-Photon Enhanced: 
        - Apply GILE-dependent time dilation to holding period
        - Modulate signal strength by DE-Photon phase
        """
        # Original V3 weights
        original_weights = {"w1": 0.25, "w2": 0.35, "w3": 0.25, "wL": 0.15}
        
        # Evolved weights (from TI Performance Cartography)
        evolved_weights = {"w1": 0.746, "w2": 0.015, "w3": 0.0, "wL": 0.238}
        
        # Calculate GILE with both weight sets
        gile_original = (
            original_weights["w1"] * t1 +
            original_weights["w2"] * t2 +
            original_weights["w3"] * t3 +
            original_weights["wL"] * love
        )
        
        gile_evolved = (
            evolved_weights["w1"] * t1 +
            evolved_weights["w2"] * t2 +
            evolved_weights["w3"] * t3 +
            evolved_weights["wL"] * love
        )
        
        # DE-Photon time dilation
        dilation_original = self.get_dilation_factor(gile_original)
        dilation_evolved = self.get_dilation_factor(gile_evolved)
        
        return {
            "jeff_time_components": {
                "t1_quantum": t1,
                "t2_interaction": t2,
                "t3_cosmological": t3,
                "love": love
            },
            "gile_original": gile_original,
            "gile_evolved": gile_evolved,
            "de_photon_dilation_original": dilation_original,
            "de_photon_dilation_evolved": dilation_evolved,
            "optimal_hold_original": self.get_optimal_holding_period(gile_original),
            "optimal_hold_evolved": self.get_optimal_holding_period(gile_evolved),
            "recommendation": "Use evolved weights" if abs(gile_evolved) > abs(gile_original) else "Use original weights"
        }


def run_all_tests() -> Dict:
    """Run all empirical tests and return comprehensive results"""
    framework = TIEmpiricalTestingFramework()
    synthesis = DEPhotonJeffTimeSynthesis()
    
    results = {
        "timestamp": datetime.now().isoformat(),
        "hypothesis_summary": framework.get_summary(),
        "de_photon_predictions": framework.generate_de_photon_jeff_time_predictions(),
        "current_de_photon_phase": synthesis.get_de_photon_phase(
            datetime(2020, 1, 1),
            datetime.now()
        ),
        "dilation_table": synthesis.gile_dilation_table,
        "example_integration": synthesis.integrate_with_jeff_time(
            t1=0.5,   # Moderate quantum potential
            t2=0.3,   # Small observation signal
            t3=0.1,   # Weak cosmological context
            love=0.4  # Moderate correlation
        )
    }
    
    return results


if __name__ == "__main__":
    results = run_all_tests()
    print(json.dumps(results, indent=2, default=str))
