"""
TI SUCCESS METRICS SYSTEM
=========================

Complete framework for measuring stock market success using TI-native metrics.

CORE INSIGHT: Traditional metrics (Sharpe, Sortino, etc.) can be mapped to
TI dimensions, revealing deeper patterns of success.

KEY INNOVATION: Myrion Resolution Synergy Meter
- Measures how well different TI theories align
- Truth bar shows synergy between: GTFE, Evolutionary, Quantum, Quartz
- Higher synergy = better predicted performance

Author: Brandon Emerick / BlissGene Therapeutics
Date: November 30, 2025
"""

import numpy as np
from dataclasses import dataclass, field
from typing import Dict, List, Optional, Tuple
from enum import Enum
from datetime import datetime
import json

# ============================================================================
# PART 1: TI-NATIVE SUCCESS METRICS
# ============================================================================

class TIDimension(Enum):
    """The 4 GILE dimensions mapped to success metrics"""
    GOODNESS = "G"      # Value creation, profit
    INTUITION = "I"     # Predictive accuracy, PSI
    LOVE = "L"          # Correlation, harmony, coherence
    ENVIRONMENT = "E"   # Stability, sustainability, context


@dataclass
class TraditionalMetric:
    """A traditional financial metric"""
    name: str
    value: float
    description: str
    higher_is_better: bool = True


@dataclass
class TIMetric:
    """A TI-native metric with dimensional mapping"""
    name: str
    value: float
    ti_dimension: TIDimension
    traditional_equivalent: str
    formula: str
    interpretation: str
    score_0_to_1: float  # Normalized score


class TIMetricsMapper:
    """
    Maps traditional financial metrics to TI-native equivalents.
    
    Each traditional metric reveals something about one or more GILE dimensions.
    The mapping illuminates which aspects of success are being measured.
    """
    
    MAPPINGS = {
        'net_profit': {
            'ti_dimension': TIDimension.GOODNESS,
            'ti_name': 'Value Manifestation',
            'formula': 'VM = (End Equity - Start Equity) / Start Equity',
            'interpretation': 'How much GILE-positive value was created'
        },
        'sharpe_ratio': {
            'ti_dimension': TIDimension.LOVE,
            'ti_name': 'Coherence Ratio',
            'formula': 'CR = E[Return] / σ(Return) = Harmony / Volatility',
            'interpretation': 'Return per unit of chaos - Love dimension balance'
        },
        'sortino_ratio': {
            'ti_dimension': TIDimension.LOVE,
            'ti_name': 'Asymmetric Coherence',
            'formula': 'AC = E[Return] / σ(Downside) = Upside Harmony',
            'interpretation': 'Coherence focused on negative protection'
        },
        'win_rate': {
            'ti_dimension': TIDimension.INTUITION,
            'ti_name': 'Collapse Accuracy',
            'formula': 'CA = N(Correct) / N(Total) = Observation Success',
            'interpretation': 'How often t2 (Jeff Moment) predictions manifest correctly'
        },
        'profit_loss_ratio': {
            'ti_dimension': TIDimension.GOODNESS,
            'ti_name': 'GILE Asymmetry',
            'formula': 'GA = E[Win] / E[Loss] = Good/Bad Ratio',
            'interpretation': 'Magnitude of positive vs negative GILE outcomes'
        },
        'max_drawdown': {
            'ti_dimension': TIDimension.ENVIRONMENT,
            'ti_name': 'Resonant Decoherence',
            'formula': 'RD = Max(Peak - Trough) / Peak = Deepest Disharmony',
            'interpretation': 'Maximum departure from positive resonance state'
        },
        'calmar_ratio': {
            'ti_dimension': TIDimension.ENVIRONMENT,
            'ti_name': 'Stability Quotient',
            'formula': 'SQ = Annual Return / Max Drawdown',
            'interpretation': 'Return per unit of instability'
        },
        'alpha': {
            'ti_dimension': TIDimension.INTUITION,
            'ti_name': 'PSI Contribution',
            'formula': 'PC = Return - β × Market Return = Pure Signal',
            'interpretation': 'Value added beyond market - true predictive power'
        },
        'beta': {
            'ti_dimension': TIDimension.LOVE,
            'ti_name': 'Market Entanglement',
            'formula': 'ME = Cov(Asset, Market) / Var(Market)',
            'interpretation': 'Degree of correlation (LCC) with broader system'
        },
        'information_ratio': {
            'ti_dimension': TIDimension.INTUITION,
            'ti_name': 'Signal Efficiency',
            'formula': 'SE = Alpha / Tracking Error',
            'interpretation': 'PSI accuracy per unit of deviation from benchmark'
        },
        'trade_count': {
            'ti_dimension': TIDimension.ENVIRONMENT,
            'ti_name': 'Observation Frequency',
            'formula': 'OF = N(Trades) / Time Period',
            'interpretation': 'How often t2 collapses are initiated'
        },
        'avg_trade_duration': {
            'ti_dimension': TIDimension.ENVIRONMENT,
            'ti_name': 'Resonance Duration',
            'formula': 'RD = E[Trade Length]',
            'interpretation': 'How long positive GILE states are maintained'
        }
    }
    
    def __init__(self):
        self.traditional_metrics: Dict[str, float] = {}
        self.ti_metrics: Dict[str, TIMetric] = {}
    
    def load_traditional_metrics(self, metrics: Dict[str, float]):
        """Load traditional metrics from backtest results"""
        self.traditional_metrics = metrics
        self._compute_ti_mappings()
    
    def _compute_ti_mappings(self):
        """Compute TI mappings for all traditional metrics"""
        self.ti_metrics = {}
        
        for trad_name, trad_value in self.traditional_metrics.items():
            key = trad_name.lower().replace(' ', '_')
            
            if key in self.MAPPINGS:
                mapping = self.MAPPINGS[key]
                
                norm_score = self._normalize_score(key, trad_value)
                
                ti_metric = TIMetric(
                    name=mapping['ti_name'],
                    value=trad_value,
                    ti_dimension=mapping['ti_dimension'],
                    traditional_equivalent=trad_name,
                    formula=mapping['formula'],
                    interpretation=mapping['interpretation'],
                    score_0_to_1=norm_score
                )
                
                self.ti_metrics[key] = ti_metric
    
    def _normalize_score(self, metric_key: str, value: float) -> float:
        """Normalize metric to 0-1 score based on typical ranges.
        
        All normalizers are clamped to [0, 1] to ensure valid scores.
        """
        def clamp(x: float) -> float:
            """Clamp value to [0, 1] range"""
            return max(0.0, min(1.0, x))
        
        normalizers = {
            'net_profit': lambda x: clamp(x / 3.0),
            'sharpe_ratio': lambda x: clamp(x / 2.0),
            'sortino_ratio': lambda x: clamp(x / 2.5),
            'win_rate': lambda x: clamp(x),
            'profit_loss_ratio': lambda x: clamp(x / 4.0),
            'max_drawdown': lambda x: clamp(1.0 - x),
            'calmar_ratio': lambda x: clamp(x / 2.0),
            'alpha': lambda x: clamp((x + 0.2) / 0.4),
            'beta': lambda x: clamp(1.0 - abs(x - 0.7) * 1.5),
            'information_ratio': lambda x: clamp(x / 1.0)
        }
        
        if metric_key in normalizers:
            return normalizers[metric_key](value)
        return 0.5
    
    def get_dimension_scores(self) -> Dict[str, float]:
        """Get aggregate score for each GILE dimension"""
        dimension_scores = {d.value: [] for d in TIDimension}
        
        for ti_metric in self.ti_metrics.values():
            dimension_scores[ti_metric.ti_dimension.value].append(ti_metric.score_0_to_1)
        
        result = {}
        for dim, scores in dimension_scores.items():
            if scores:
                result[dim] = float(np.mean(scores))
            else:
                result[dim] = 0.5
        
        return result
    
    def compute_gile_score(self) -> float:
        """Compute unified GILE score from all dimensions"""
        dim_scores = self.get_dimension_scores()
        
        weights = {'G': 0.3, 'I': 0.25, 'L': 0.25, 'E': 0.2}
        
        gile = sum(dim_scores[d] * weights[d] for d in weights)
        return float(gile)


# ============================================================================
# PART 2: MYRION RESOLUTION SYNERGY METER
# ============================================================================

class TITheory(Enum):
    """The TI theories being measured for synergy"""
    GTFE = "Grand Tralse Field Equation"
    EVOLUTIONARY = "Evolutionary I-Cell Selection"
    QUANTUM = "Quantum Resonance Operators"
    TENSOR = "TI Tensor Flow"
    QUARTZ = "Quartz Crystal Filtering"


@dataclass
class TheorySynergy:
    """Synergy measurement between two theories"""
    theory_a: TITheory
    theory_b: TITheory
    synergy_score: float  # -1 (contradicts) to +1 (aligned)
    alignment_type: str   # "aligned", "independent", "contradicts"
    explanation: str


@dataclass
class MyrionState:
    """State of Myrion Resolution - the truth position"""
    true_component: float  # 0-1: How much aligns as TRUE
    false_component: float # 0-1: How much aligns as FALSE
    tralse_component: float # 0-1: How much is indeterminate
    resolution_vector: Tuple[float, float, float]  # (T, F, ⊥)
    
    @property
    def truth_bar_position(self) -> float:
        """Position on truth bar: -1 (FALSE) to +1 (TRUE), 0 = TRALSE"""
        return self.true_component - self.false_component


class MyrionResolutionSynergyMeter:
    """
    Measures synergy between TI theories using Myrion Resolution.
    
    The Truth Bar shows:
    - LEFT (-1): Theories CONTRADICT (FALSE alignment)
    - CENTER (0): Theories are INDEPENDENT/INDETERMINATE (TRALSE)
    - RIGHT (+1): Theories ALIGN (TRUE synergy)
    
    When theories align, their combined power exceeds individual contributions.
    When they contradict, they cancel each other out.
    """
    
    def __init__(self):
        self.theory_signals: Dict[TITheory, Dict] = {}
        self.synergies: List[TheorySynergy] = []
        self.myrion_state: Optional[MyrionState] = None
    
    def register_theory_signal(self, theory: TITheory, signal: Dict):
        """Register a signal from a TI theory"""
        required = ['direction', 'strength', 'confidence']
        if all(k in signal for k in required):
            self.theory_signals[theory] = signal
    
    def compute_pairwise_synergies(self):
        """Compute synergy between all theory pairs"""
        self.synergies = []
        theories = list(self.theory_signals.keys())
        
        for i in range(len(theories)):
            for j in range(i + 1, len(theories)):
                theory_a = theories[i]
                theory_b = theories[j]
                
                synergy = self._compute_synergy(theory_a, theory_b)
                self.synergies.append(synergy)
    
    def _compute_synergy(self, theory_a: TITheory, theory_b: TITheory) -> TheorySynergy:
        """Compute synergy between two theories"""
        sig_a = self.theory_signals[theory_a]
        sig_b = self.theory_signals[theory_b]
        
        dir_a = sig_a['direction']
        dir_b = sig_b['direction']
        str_a = sig_a['strength']
        str_b = sig_b['strength']
        conf_a = sig_a['confidence']
        conf_b = sig_b['confidence']
        
        direction_alignment = 1 if (dir_a * dir_b > 0) else (-1 if dir_a * dir_b < 0 else 0)
        
        strength_similarity = 1 - abs(str_a - str_b)
        confidence_product = conf_a * conf_b
        
        synergy_score = direction_alignment * strength_similarity * confidence_product
        
        if synergy_score > 0.3:
            alignment_type = "aligned"
            explanation = f"{theory_a.value} and {theory_b.value} reinforce each other"
        elif synergy_score < -0.3:
            alignment_type = "contradicts"
            explanation = f"{theory_a.value} and {theory_b.value} give opposing signals"
        else:
            alignment_type = "independent"
            explanation = f"{theory_a.value} and {theory_b.value} are mostly independent"
        
        return TheorySynergy(
            theory_a=theory_a,
            theory_b=theory_b,
            synergy_score=synergy_score,
            alignment_type=alignment_type,
            explanation=explanation
        )
    
    def compute_myrion_state(self) -> MyrionState:
        """Compute overall Myrion Resolution state from all synergies"""
        if not self.synergies:
            self.compute_pairwise_synergies()
        
        positive_synergies = [s for s in self.synergies if s.synergy_score > 0.3]
        negative_synergies = [s for s in self.synergies if s.synergy_score < -0.3]
        neutral_synergies = [s for s in self.synergies if -0.3 <= s.synergy_score <= 0.3]
        
        total = max(len(self.synergies), 1)
        
        true_component = len(positive_synergies) / total
        false_component = len(negative_synergies) / total
        tralse_component = len(neutral_synergies) / total
        
        norm = true_component + false_component + tralse_component
        if norm > 0:
            true_component /= norm
            false_component /= norm
            tralse_component /= norm
        
        self.myrion_state = MyrionState(
            true_component=true_component,
            false_component=false_component,
            tralse_component=tralse_component,
            resolution_vector=(true_component, false_component, tralse_component)
        )
        
        return self.myrion_state
    
    def get_truth_bar(self, width: int = 50) -> str:
        """Generate ASCII truth bar visualization"""
        if not self.myrion_state:
            self.compute_myrion_state()
        
        position = self.myrion_state.truth_bar_position
        
        bar_position = int((position + 1) / 2 * width)
        bar_position = max(0, min(width - 1, bar_position))
        
        bar = ['─'] * width
        bar[width // 2] = '│'
        bar[bar_position] = '█'
        
        left_label = "FALSE"
        center_label = "TRALSE"
        right_label = "TRUE"
        
        bar_str = ''.join(bar)
        
        return f"""
┌{'─' * (width + 2)}┐
│ {bar_str} │
└{'─' * (width + 2)}┘
{left_label:^{width//3}}{center_label:^{width//3}}{right_label:^{width//3}}

Truth Position: {position:+.3f}
True Component:   {self.myrion_state.true_component:.1%}
False Component:  {self.myrion_state.false_component:.1%}
Tralse Component: {self.myrion_state.tralse_component:.1%}
"""
    
    def get_synergy_report(self) -> Dict:
        """Get comprehensive synergy report"""
        if not self.myrion_state:
            self.compute_myrion_state()
        
        avg_synergy = float(np.mean([s.synergy_score for s in self.synergies])) if self.synergies else 0
        
        if self.myrion_state.truth_bar_position > 0.5:
            recommendation = "HIGH SYNERGY: All systems aligned - strong signal"
        elif self.myrion_state.truth_bar_position > 0.2:
            recommendation = "MODERATE SYNERGY: Most systems agree - proceed with caution"
        elif self.myrion_state.truth_bar_position > -0.2:
            recommendation = "INDETERMINATE: Systems in Tralse state - wait for clarity"
        elif self.myrion_state.truth_bar_position > -0.5:
            recommendation = "CONTRADICTION DETECTED: Some systems disagree - reduce exposure"
        else:
            recommendation = "HIGH CONTRADICTION: Systems strongly oppose - avoid action"
        
        return {
            'truth_bar_position': self.myrion_state.truth_bar_position,
            'true_component': self.myrion_state.true_component,
            'false_component': self.myrion_state.false_component,
            'tralse_component': self.myrion_state.tralse_component,
            'average_synergy': avg_synergy,
            'synergy_count': len(self.synergies),
            'aligned_pairs': sum(1 for s in self.synergies if s.alignment_type == "aligned"),
            'contradicting_pairs': sum(1 for s in self.synergies if s.alignment_type == "contradicts"),
            'recommendation': recommendation
        }


# ============================================================================
# PART 3: TI-NATIVE SCORING SYSTEM
# ============================================================================

@dataclass
class TIAlgorithmScore:
    """Complete TI-native score for a trading algorithm"""
    algorithm_name: str
    timestamp: str
    
    gile_score: float
    dimension_scores: Dict[str, float]
    synergy_score: float
    truth_bar_position: float
    
    traditional_metrics: Dict[str, float]
    ti_metrics: Dict[str, TIMetric]
    
    overall_ti_rating: str
    recommendation: str


class TINativeScoringSystem:
    """
    Complete TI-native scoring system for evaluating trading algorithms.
    
    Combines:
    1. TI Metrics Mapping (traditional → TI)
    2. Myrion Resolution Synergy
    3. GILE Dimensional Analysis
    4. Theory Alignment Score
    
    Produces a single, unified TI score.
    """
    
    RATING_THRESHOLDS = {
        'TRANSCENDENT': 0.9,
        'EXCELLENT': 0.8,
        'GOOD': 0.7,
        'ACCEPTABLE': 0.6,
        'POOR': 0.4,
        'FAILING': 0.0
    }
    
    def __init__(self):
        self.metrics_mapper = TIMetricsMapper()
        self.synergy_meter = MyrionResolutionSynergyMeter()
    
    def score_algorithm(
        self,
        algorithm_name: str,
        traditional_metrics: Dict[str, float],
        theory_signals: Dict[str, Dict] = None
    ) -> TIAlgorithmScore:
        """
        Score an algorithm using TI-native metrics.
        
        traditional_metrics: Dict of metric_name -> value
        theory_signals: Optional dict of theory_name -> signal dict
        """
        self.metrics_mapper.load_traditional_metrics(traditional_metrics)
        
        gile_score = self.metrics_mapper.compute_gile_score()
        dimension_scores = self.metrics_mapper.get_dimension_scores()
        
        if theory_signals:
            for theory_key, signal in theory_signals.items():
                try:
                    if isinstance(theory_key, TITheory):
                        theory = theory_key
                    else:
                        theory = TITheory[str(theory_key).upper()]
                    self.synergy_meter.register_theory_signal(theory, signal)
                except (KeyError, AttributeError):
                    pass
            
            synergy_report = self.synergy_meter.get_synergy_report()
            synergy_score = (synergy_report['truth_bar_position'] + 1) / 2
            truth_bar_position = synergy_report['truth_bar_position']
        else:
            synergy_score = 0.5
            truth_bar_position = 0.0
        
        overall_score = gile_score * 0.6 + synergy_score * 0.4
        
        rating = 'FAILING'
        for r, threshold in sorted(self.RATING_THRESHOLDS.items(), key=lambda x: -x[1]):
            if overall_score >= threshold:
                rating = r
                break
        
        recommendation = self._generate_recommendation(
            gile_score, synergy_score, dimension_scores, rating
        )
        
        return TIAlgorithmScore(
            algorithm_name=algorithm_name,
            timestamp=datetime.now().isoformat(),
            gile_score=gile_score,
            dimension_scores=dimension_scores,
            synergy_score=synergy_score,
            truth_bar_position=truth_bar_position,
            traditional_metrics=traditional_metrics,
            ti_metrics=self.metrics_mapper.ti_metrics,
            overall_ti_rating=rating,
            recommendation=recommendation
        )
    
    def _generate_recommendation(
        self,
        gile: float,
        synergy: float,
        dimensions: Dict[str, float],
        rating: str
    ) -> str:
        """Generate actionable recommendation based on scores"""
        
        recommendations = []
        
        weakest_dim = min(dimensions.items(), key=lambda x: x[1])
        if weakest_dim[1] < 0.5:
            dim_names = {
                'G': 'Goodness (profitability)',
                'I': 'Intuition (prediction accuracy)',
                'L': 'Love (correlation coherence)',
                'E': 'Environment (stability)'
            }
            recommendations.append(
                f"Improve {dim_names[weakest_dim[0]]} - currently weakest at {weakest_dim[1]:.1%}"
            )
        
        if synergy < 0.5:
            recommendations.append(
                "Theory synergy is low - consider aligning GTFE weights with Evolutionary findings"
            )
        
        if gile < 0.6:
            recommendations.append(
                "Overall GILE score needs improvement - focus on profit/loss ratio"
            )
        
        if rating in ['TRANSCENDENT', 'EXCELLENT']:
            recommendations.append(
                "Algorithm shows strong TI alignment - ready for deployment"
            )
        elif rating in ['GOOD', 'ACCEPTABLE']:
            recommendations.append(
                "Algorithm shows promise - consider Quartz filtering for improvement"
            )
        else:
            recommendations.append(
                "Algorithm needs significant improvement - review dimensional weights"
            )
        
        return "; ".join(recommendations)
    
    def print_score_report(self, score: TIAlgorithmScore):
        """Print formatted score report"""
        print("="*70)
        print(f"TI-NATIVE ALGORITHM SCORE: {score.algorithm_name}")
        print(f"Timestamp: {score.timestamp}")
        print("="*70)
        
        print("\n1. GILE DIMENSIONAL SCORES")
        print("-"*50)
        for dim, val in score.dimension_scores.items():
            dim_names = {'G': 'Goodness', 'I': 'Intuition', 'L': 'Love', 'E': 'Environment'}
            bar_len = int(val * 30)
            bar = '█' * bar_len + '░' * (30 - bar_len)
            print(f"  {dim_names[dim]:15s} [{bar}] {val:.1%}")
        
        print(f"\n  UNIFIED GILE SCORE: {score.gile_score:.3f}")
        
        print("\n2. MYRION RESOLUTION SYNERGY")
        print("-"*50)
        print(self.synergy_meter.get_truth_bar())
        print(f"  Synergy Score: {score.synergy_score:.3f}")
        
        print("\n3. TI METRICS MAPPING")
        print("-"*50)
        for key, ti_metric in score.ti_metrics.items():
            print(f"\n  {ti_metric.traditional_equivalent} → {ti_metric.name}")
            print(f"    Value: {ti_metric.value:.4f}")
            print(f"    Dimension: {ti_metric.ti_dimension.name}")
            print(f"    Score: {ti_metric.score_0_to_1:.1%}")
        
        print("\n4. OVERALL RATING")
        print("-"*50)
        print(f"\n  Rating: {score.overall_ti_rating}")
        print(f"  Recommendation: {score.recommendation}")
        
        print("\n" + "="*70)


# ============================================================================
# PART 4: DEMONSTRATION
# ============================================================================

def demonstrate_ti_success_metrics():
    """Demonstrate the TI Success Metrics System"""
    
    print("="*70)
    print("TI SUCCESS METRICS SYSTEM - DEMONSTRATION")
    print("="*70)
    
    v3_metrics = {
        'net_profit': 2.7776,
        'sharpe_ratio': 1.06,
        'sortino_ratio': 1.263,
        'win_rate': 0.44,
        'profit_loss_ratio': 3.07,
        'max_drawdown': 0.327,
        'alpha': 0.132,
        'beta': 0.722,
        'information_ratio': 0.753
    }
    
    theory_signals = {
        'GTFE': {'direction': 1, 'strength': 0.8, 'confidence': 0.75},
        'EVOLUTIONARY': {'direction': 1, 'strength': 0.9, 'confidence': 0.85},
        'QUANTUM': {'direction': 1, 'strength': 0.7, 'confidence': 0.6},
        'TENSOR': {'direction': 1, 'strength': 0.6, 'confidence': 0.7},
        'QUARTZ': {'direction': 1, 'strength': 0.75, 'confidence': 0.8}
    }
    
    scoring_system = TINativeScoringSystem()
    
    score = scoring_system.score_algorithm(
        algorithm_name="TI QuantConnect V3 (Energetic Asparagus Beaver)",
        traditional_metrics=v3_metrics,
        theory_signals=theory_signals
    )
    
    scoring_system.print_score_report(score)
    
    print("\n\n--- COMPARISON WITH V9 QUARTZ PROJECTIONS ---\n")
    
    v9_projected_metrics = {
        'net_profit': 3.5,
        'sharpe_ratio': 1.3,
        'sortino_ratio': 1.5,
        'win_rate': 0.52,
        'profit_loss_ratio': 3.5,
        'max_drawdown': 0.25,
        'alpha': 0.18,
        'beta': 0.6,
        'information_ratio': 0.9
    }
    
    scoring_system2 = TINativeScoringSystem()
    
    score2 = scoring_system2.score_algorithm(
        algorithm_name="TI QuantConnect V9 (Quartz Crystal) - PROJECTED",
        traditional_metrics=v9_projected_metrics,
        theory_signals=theory_signals
    )
    
    scoring_system2.print_score_report(score2)
    
    return score, score2


if __name__ == "__main__":
    demonstrate_ti_success_metrics()
