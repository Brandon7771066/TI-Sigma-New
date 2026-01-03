"""
TI STOCK PREDICTION DIAGNOSTIC LAB
===================================

PURPOSE: PROVE which TI dimensions predict stock market success using rigorous scientific method.

Instead of "hoping mud sticks" with algorithm iterations, we:
1. Capture ALL TI dimensions for historical data
2. Run ablation experiments (isolate each dimension's contribution)
3. Measure predictive accuracy for each dimension
4. Identify what's MISSING by "process of illumination"

KEY TI DIMENSIONS TO TEST:
- PD (Pareto Distribution): The "above and beyond" predictor
- Jeff Time: Present moment focus with 3 aspects (Potential/Actualized/Contextual)
- MR (Myrion Resolution): Contradiction handling via PD values
- LCC (Love Correlation): 0.42+ threshold for synchronization
- Sacred Interval (-0.666, 0.333): TRALSE/indeterminate zone

SCIENTIFIC METHOD:
1. Hypothesis: PD + Jeff Time together can predict stock success
2. Null Hypothesis: Random chance (50% accuracy)
3. Test: Ablation experiments isolating each dimension
4. Measure: Directional accuracy, magnitude accuracy, consistency
"""

import numpy as np
import pandas as pd
from datetime import datetime, timedelta
from typing import Dict, List, Tuple, Optional
from dataclasses import dataclass, field
from collections import defaultdict
import json

# ============================================================================
# TI DIMENSION DEFINITIONS
# ============================================================================

@dataclass
class TIDimensionCapture:
    """Captures all TI dimensions for a single timestep"""
    timestamp: datetime
    symbol: str
    price: float
    
    # PD (Pareto Distribution) Components
    pd_raw: float = 0.0  # Raw percentage change
    pd_zone: str = "TRALSE"  # TRUE (>0.333), FALSE (<-0.666), TRALSE (between)
    pd_gile: float = 0.0  # Mapped to GILE (-3 to +3)
    
    # Jeff Time: 3 Aspects of PRESENT (not temporal!)
    jt_potential: float = 0.0  # What COULD happen (momentum + volatility)
    jt_actualized: float = 0.0  # What IS happening (today's observation)
    jt_contextual: float = 0.0  # Current environment (trend context NOW)
    
    # MR (Myrion Resolution) - Contradiction State
    mr_state: str = "ALIGNED"  # ALIGNED, POSITIVE_DOMINANT, NEGATIVE_DOMINANT, BALANCED_CONFLICT
    mr_pd_weighted: float = 0.0  # PD-weighted resolution
    
    # LCC (Love Correlation) - Synchronization
    lcc_correlation: float = 0.0  # Raw correlation value
    lcc_synchronized: bool = False  # True if correlation >= 0.42
    lcc_anti_correlated: bool = False  # True if correlation <= -0.42
    
    # Outcome (for measuring accuracy)
    next_day_return: float = 0.0
    next_day_direction: int = 0  # 1=up, -1=down, 0=flat
    
    def to_dict(self) -> dict:
        return {
            'timestamp': self.timestamp.isoformat() if self.timestamp else None,
            'symbol': self.symbol,
            'price': self.price,
            'pd_raw': self.pd_raw,
            'pd_zone': self.pd_zone,
            'pd_gile': self.pd_gile,
            'jt_potential': self.jt_potential,
            'jt_actualized': self.jt_actualized,
            'jt_contextual': self.jt_contextual,
            'mr_state': self.mr_state,
            'mr_pd_weighted': self.mr_pd_weighted,
            'lcc_correlation': self.lcc_correlation,
            'lcc_synchronized': self.lcc_synchronized,
            'lcc_anti_correlated': self.lcc_anti_correlated,
            'next_day_return': self.next_day_return,
            'next_day_direction': self.next_day_direction
        }


# ============================================================================
# TI DIMENSION CALCULATOR
# ============================================================================

class TIDimensionCalculator:
    """Calculates all TI dimensions from price data"""
    
    # Sacred Interval Boundaries
    SACRED_MIN = -0.666  # Below = FALSE
    SACRED_MAX = 0.333   # Above = TRUE
    
    # GILE Thresholds
    GREAT_THRESHOLD = 5.0
    TERRIBLE_THRESHOLD = -5.0
    ULTRA_GREAT = 20.0
    ULTRA_TERRIBLE = -10.0
    
    # LCC Threshold
    LCC_SYNC_THRESHOLD = 0.42
    
    # Lookback Windows
    POTENTIAL_WINDOW = 3   # Days for momentum/volatility
    CONTEXT_SHORT = 20     # Short-term trend
    CONTEXT_LONG = 50      # Long-term trend
    CORRELATION_WINDOW = 20  # Days for correlation
    
    def __init__(self):
        self.price_history: Dict[str, List[float]] = defaultdict(list)
        self.return_history: Dict[str, List[float]] = defaultdict(list)
        
    def add_price(self, symbol: str, price: float, timestamp: datetime):
        """Add a price observation"""
        self.price_history[symbol].append(price)
        
        # Calculate return if we have previous price
        if len(self.price_history[symbol]) >= 2:
            prev = self.price_history[symbol][-2]
            ret = (price - prev) / prev * 100 if prev != 0 else 0
            self.return_history[symbol].append(ret)
        
        # Trim to prevent memory bloat
        max_len = 200
        if len(self.price_history[symbol]) > max_len:
            self.price_history[symbol] = self.price_history[symbol][-max_len:]
            self.return_history[symbol] = self.return_history[symbol][-max_len:]
    
    def price_to_gile(self, pct_change: float) -> float:
        """Map percentage change to GILE scale (-3 to +3)"""
        if pct_change > self.ULTRA_GREAT:
            excess = pct_change - self.ULTRA_GREAT
            return float(2.0 + np.log1p(excess / 20) * 0.5)
        elif pct_change < self.ULTRA_TERRIBLE:
            excess = abs(pct_change) - abs(self.ULTRA_TERRIBLE)
            return float(-3.0 - np.log1p(excess / 10) * 0.5)
        elif pct_change > self.GREAT_THRESHOLD:
            return float(1.5 + (pct_change - 5) / 15 * 0.5)
        elif pct_change < self.TERRIBLE_THRESHOLD:
            return float(-3.0 + (pct_change + 10) / 5 * 1.5)
        elif pct_change > self.SACRED_MAX:
            return float(0.3 + (pct_change - 0.333) / 4.667 * 1.2)
        elif pct_change < self.SACRED_MIN:
            return float(-1.5 + (pct_change + 5) / 4.334 * 1.2)
        else:
            # TRALSE Zone - indeterminate
            if pct_change < 0:
                return float((pct_change / 0.666) * 0.3)
            else:
                return float((pct_change / 0.333) * 0.3)
    
    def get_pd_zone(self, pct_change: float) -> str:
        """Classify into TRUE/FALSE/TRALSE zones"""
        if pct_change > self.SACRED_MAX:
            return "TRUE"
        elif pct_change < self.SACRED_MIN:
            return "FALSE"
        else:
            return "TRALSE"
    
    def calculate_jt_potential(self, symbol: str) -> float:
        """Jeff Time POTENTIAL: What COULD happen (momentum + volatility NOW)"""
        prices = self.price_history.get(symbol, [])
        if len(prices) < self.POTENTIAL_WINDOW:
            return 0.0
        
        recent = prices[-self.POTENTIAL_WINDOW:]
        momentum = (recent[-1] - recent[0]) / recent[0] * 100 if recent[0] != 0 else 0
        
        returns = np.diff(recent) / recent[:-1] * 100
        volatility = float(np.std(returns)) if len(returns) > 1 else 0
        
        # Potential = momentum scaled by volatility (uncertainty)
        potential = self.price_to_gile(momentum) * (1 + volatility * 0.1)
        return float(np.clip(potential, -3, 3))
    
    def calculate_jt_actualized(self, symbol: str) -> float:
        """Jeff Time ACTUALIZED: What IS happening (today's observation)"""
        returns = self.return_history.get(symbol, [])
        if len(returns) < 1:
            return 0.0
        
        today_return = returns[-1]
        return float(self.price_to_gile(today_return))
    
    def calculate_jt_contextual(self, symbol: str) -> float:
        """Jeff Time CONTEXTUAL: Current environment (trend context NOW)"""
        prices = self.price_history.get(symbol, [])
        if len(prices) < self.CONTEXT_LONG:
            return 0.0
        
        sma_short = float(np.mean(prices[-self.CONTEXT_SHORT:]))
        sma_long = float(np.mean(prices[-self.CONTEXT_LONG:]))
        current = prices[-1]
        
        trend_divergence = (sma_short - sma_long) / sma_long * 100 if sma_long != 0 else 0
        price_position = (current - sma_long) / sma_long * 100 if sma_long != 0 else 0
        
        context = (trend_divergence + price_position) / 2
        return float(self.price_to_gile(context))
    
    def calculate_mr_state(self, jt_potential: float, jt_actualized: float, jt_contextual: float) -> Tuple[str, float]:
        """
        Myrion Resolution: Resolve contradictions using PD values
        
        Returns (state, pd_weighted_resolution)
        """
        dimensions = [jt_potential, jt_actualized, jt_contextual]
        positive = sum(1 for d in dimensions if d > 0)
        negative = sum(1 for d in dimensions if d < 0)
        
        if positive == 3 or negative == 3:
            state = "ALIGNED"
        elif positive >= 2:
            state = "POSITIVE_DOMINANT"
        elif negative >= 2:
            state = "NEGATIVE_DOMINANT"
        else:
            state = "BALANCED_CONFLICT"
        
        # PD-weighted resolution: weight by absolute magnitude
        total_weight = sum(abs(d) for d in dimensions) + 0.001
        weighted = sum(d * abs(d) for d in dimensions) / total_weight
        
        return state, float(weighted)
    
    def calculate_lcc(self, symbol: str, reference_symbol: str = "SPY") -> Tuple[float, bool, bool]:
        """
        Love Correlation: Synchronization via 0.42+ threshold
        
        Returns (correlation, is_synchronized, is_anti_correlated)
        """
        sym_returns = self.return_history.get(symbol, [])
        ref_returns = self.return_history.get(reference_symbol, [])
        
        if len(sym_returns) < self.CORRELATION_WINDOW or len(ref_returns) < self.CORRELATION_WINDOW:
            return 0.0, False, False
        
        sym_recent = sym_returns[-self.CORRELATION_WINDOW:]
        ref_recent = ref_returns[-self.CORRELATION_WINDOW:]
        
        # Ensure equal lengths
        min_len = min(len(sym_recent), len(ref_recent))
        if min_len < 10:
            return 0.0, False, False
        
        sym_recent = sym_recent[-min_len:]
        ref_recent = ref_recent[-min_len:]
        
        try:
            corr_matrix = np.corrcoef(sym_recent, ref_recent)
            correlation = float(corr_matrix[0, 1]) if not np.isnan(corr_matrix[0, 1]) else 0.0
        except:
            correlation = 0.0
        
        is_sync = correlation >= self.LCC_SYNC_THRESHOLD
        is_anti = correlation <= -self.LCC_SYNC_THRESHOLD
        
        return correlation, is_sync, is_anti
    
    def capture_all_dimensions(self, symbol: str, timestamp: datetime, 
                               reference_symbol: str = "SPY") -> TIDimensionCapture:
        """Capture all TI dimensions for current timestep"""
        prices = self.price_history.get(symbol, [])
        returns = self.return_history.get(symbol, [])
        
        if len(prices) < 2:
            return TIDimensionCapture(
                timestamp=timestamp,
                symbol=symbol,
                price=prices[-1] if prices else 0.0
            )
        
        # PD calculations
        pd_raw = returns[-1] if returns else 0.0
        pd_zone = self.get_pd_zone(pd_raw)
        pd_gile = self.price_to_gile(pd_raw)
        
        # Jeff Time calculations
        jt_potential = self.calculate_jt_potential(symbol)
        jt_actualized = self.calculate_jt_actualized(symbol)
        jt_contextual = self.calculate_jt_contextual(symbol)
        
        # MR calculation
        mr_state, mr_pd_weighted = self.calculate_mr_state(jt_potential, jt_actualized, jt_contextual)
        
        # LCC calculation
        lcc_corr, lcc_sync, lcc_anti = self.calculate_lcc(symbol, reference_symbol)
        
        return TIDimensionCapture(
            timestamp=timestamp,
            symbol=symbol,
            price=prices[-1],
            pd_raw=pd_raw,
            pd_zone=pd_zone,
            pd_gile=pd_gile,
            jt_potential=jt_potential,
            jt_actualized=jt_actualized,
            jt_contextual=jt_contextual,
            mr_state=mr_state,
            mr_pd_weighted=mr_pd_weighted,
            lcc_correlation=lcc_corr,
            lcc_synchronized=lcc_sync,
            lcc_anti_correlated=lcc_anti
        )


# ============================================================================
# ABLATION EXPERIMENT RUNNER
# ============================================================================

@dataclass
class DimensionPrediction:
    """Prediction made by a specific dimension combination"""
    signal: float  # -1 to +1 signal strength
    direction: int  # -1=short, 0=neutral, 1=long
    confidence: float  # 0 to 1


class AblationExperiment:
    """
    Run ablation experiments to prove which dimensions predict success.
    
    Test configurations:
    1. PD_ONLY: Just Pareto Distribution
    2. JT_ONLY: Just Jeff Time (Potential + Actualized + Contextual)
    3. PD_JT: PD + Jeff Time combined
    4. PD_JT_MR: Add Myrion Resolution
    5. PD_JT_LCC: Add Love Correlation
    6. FULL_TI: All dimensions
    """
    
    DIMENSION_CONFIGS = {
        'PD_ONLY': ['pd'],
        'JT_ONLY': ['jt_potential', 'jt_actualized', 'jt_contextual'],
        'PD_JT': ['pd', 'jt_potential', 'jt_actualized', 'jt_contextual'],
        'PD_JT_MR': ['pd', 'jt_potential', 'jt_actualized', 'jt_contextual', 'mr'],
        'PD_JT_LCC': ['pd', 'jt_potential', 'jt_actualized', 'jt_contextual', 'lcc'],
        'FULL_TI': ['pd', 'jt_potential', 'jt_actualized', 'jt_contextual', 'mr', 'lcc'],
        'JT_POTENTIAL_ONLY': ['jt_potential'],
        'JT_ACTUALIZED_ONLY': ['jt_actualized'],
        'JT_CONTEXTUAL_ONLY': ['jt_contextual'],
        'MR_ONLY': ['mr'],
        'LCC_ONLY': ['lcc']
    }
    
    def __init__(self):
        self.results: Dict[str, Dict] = {}
    
    def predict_from_dimensions(self, capture: TIDimensionCapture, 
                                dimensions: List[str]) -> DimensionPrediction:
        """Generate prediction from specific dimension subset"""
        signals = []
        
        for dim in dimensions:
            if dim == 'pd':
                # PD signal: use raw percentage scaled
                signals.append(capture.pd_gile / 3.0)  # Normalize to -1 to +1
            elif dim == 'jt_potential':
                signals.append(capture.jt_potential / 3.0)
            elif dim == 'jt_actualized':
                signals.append(capture.jt_actualized / 3.0)
            elif dim == 'jt_contextual':
                signals.append(capture.jt_contextual / 3.0)
            elif dim == 'mr':
                # MR signal: weighted by state
                if capture.mr_state == "ALIGNED":
                    signals.append(capture.mr_pd_weighted / 3.0 * 1.5)
                elif capture.mr_state == "POSITIVE_DOMINANT":
                    signals.append(capture.mr_pd_weighted / 3.0 * 1.0)
                elif capture.mr_state == "NEGATIVE_DOMINANT":
                    signals.append(capture.mr_pd_weighted / 3.0 * 1.0)
                else:  # BALANCED_CONFLICT
                    signals.append(capture.mr_pd_weighted / 3.0 * 0.5)
            elif dim == 'lcc':
                # LCC signal: amplify if synchronized
                if capture.lcc_synchronized:
                    signals.append(0.5)  # Boost long
                elif capture.lcc_anti_correlated:
                    signals.append(-0.3)  # Slight bearish
                else:
                    signals.append(0.0)  # Neutral
        
        if not signals:
            return DimensionPrediction(signal=0.0, direction=0, confidence=0.0)
        
        avg_signal = float(np.mean(signals))
        direction = 1 if avg_signal > 0.1 else (-1 if avg_signal < -0.1 else 0)
        confidence = min(abs(avg_signal), 1.0)
        
        return DimensionPrediction(
            signal=float(np.clip(avg_signal, -1, 1)),
            direction=direction,
            confidence=confidence
        )
    
    def evaluate_predictions(self, predictions: List[DimensionPrediction], 
                            outcomes: List[int]) -> Dict:
        """
        Evaluate prediction accuracy
        
        outcomes: List of 1 (up), -1 (down), 0 (flat)
        """
        if len(predictions) != len(outcomes) or len(predictions) == 0:
            return {'accuracy': 0.0, 'precision': 0.0, 'recall': 0.0}
        
        total = 0
        correct = 0
        true_positives = 0
        false_positives = 0
        false_negatives = 0
        
        for pred, actual in zip(predictions, outcomes):
            if pred.direction == 0:
                continue  # Skip neutral predictions
            
            total += 1
            if pred.direction == actual:
                correct += 1
                if pred.direction == 1:
                    true_positives += 1
            else:
                if pred.direction == 1:
                    false_positives += 1
                elif actual == 1:
                    false_negatives += 1
        
        accuracy = correct / max(total, 1)
        precision = true_positives / max(true_positives + false_positives, 1)
        recall = true_positives / max(true_positives + false_negatives, 1)
        
        return {
            'accuracy': accuracy,
            'precision': precision,
            'recall': recall,
            'total_predictions': total,
            'correct_predictions': correct
        }
    
    def run_experiment(self, captures: List[TIDimensionCapture], 
                      config_name: str) -> Dict:
        """Run ablation experiment for a specific configuration"""
        if config_name not in self.DIMENSION_CONFIGS:
            return {'error': f'Unknown config: {config_name}'}
        
        dimensions = self.DIMENSION_CONFIGS[config_name]
        predictions = []
        outcomes = []
        
        for capture in captures:
            if capture.next_day_direction != 0:
                pred = self.predict_from_dimensions(capture, dimensions)
                predictions.append(pred)
                outcomes.append(capture.next_day_direction)
        
        metrics = self.evaluate_predictions(predictions, outcomes)
        metrics['config_name'] = config_name
        metrics['dimensions'] = dimensions
        
        # Calculate signal distribution stats
        signals = [p.signal for p in predictions]
        if signals:
            metrics['avg_signal'] = float(np.mean(signals))
            metrics['std_signal'] = float(np.std(signals))
            metrics['positive_signals'] = sum(1 for s in signals if s > 0)
            metrics['negative_signals'] = sum(1 for s in signals if s < 0)
        
        self.results[config_name] = metrics
        return metrics
    
    def run_all_experiments(self, captures: List[TIDimensionCapture]) -> Dict[str, Dict]:
        """Run all ablation experiments"""
        print("="*60)
        print("RUNNING TI DIMENSION ABLATION EXPERIMENTS")
        print("="*60)
        print(f"Total timesteps: {len(captures)}")
        print()
        
        for config_name in self.DIMENSION_CONFIGS:
            result = self.run_experiment(captures, config_name)
            print(f"{config_name:20s} | Accuracy: {result['accuracy']*100:5.1f}% | Predictions: {result.get('total_predictions', 0)}")
        
        print()
        return self.results
    
    def get_ranking(self) -> List[Tuple[str, float]]:
        """Rank configurations by accuracy"""
        ranking = [(name, r.get('accuracy', 0)) for name, r in self.results.items()]
        ranking.sort(key=lambda x: x[1], reverse=True)
        return ranking


# ============================================================================
# TI DIAGNOSTIC DASHBOARD
# ============================================================================

class TIDiagnosticDashboard:
    """
    Visualize TI dimension efficacy and identify gaps.
    
    Key questions to answer:
    1. Which dimensions have highest predictive accuracy?
    2. When do PD and Jeff Time diverge?
    3. What patterns appear in sacred interval violations?
    4. What's MISSING that would improve predictions?
    """
    
    def __init__(self):
        self.experiment_results: Dict[str, Dict] = {}
        self.captures: List[TIDimensionCapture] = []
    
    def load_results(self, results: Dict[str, Dict], captures: List[TIDimensionCapture]):
        self.experiment_results = results
        self.captures = captures
    
    def analyze_sacred_interval_occupancy(self) -> Dict:
        """Analyze how often prices stay in TRALSE zone vs TRUE/FALSE"""
        zone_counts = {'TRUE': 0, 'FALSE': 0, 'TRALSE': 0}
        zone_outcomes = {'TRUE': [], 'FALSE': [], 'TRALSE': []}
        
        for capture in self.captures:
            zone = capture.pd_zone
            zone_counts[zone] += 1
            if capture.next_day_direction != 0:
                zone_outcomes[zone].append(capture.next_day_direction)
        
        total = sum(zone_counts.values()) or 1
        
        analysis = {}
        for zone in ['TRUE', 'FALSE', 'TRALSE']:
            outcomes = zone_outcomes[zone]
            if outcomes:
                up_pct = sum(1 for o in outcomes if o > 0) / len(outcomes)
            else:
                up_pct = 0.5
            
            analysis[zone] = {
                'count': zone_counts[zone],
                'percentage': zone_counts[zone] / total * 100,
                'next_day_up_probability': up_pct,
                'predictive_value': abs(up_pct - 0.5) * 2  # 0=random, 1=perfect
            }
        
        return analysis
    
    def analyze_dimension_divergence(self) -> Dict:
        """Find when PD and Jeff Time diverge and measure outcome"""
        divergences = []
        
        for capture in self.captures:
            if capture.next_day_direction == 0:
                continue
            
            # PD direction
            pd_dir = 1 if capture.pd_gile > 0.1 else (-1 if capture.pd_gile < -0.1 else 0)
            
            # Jeff Time consensus
            jt_avg = (capture.jt_potential + capture.jt_actualized + capture.jt_contextual) / 3
            jt_dir = 1 if jt_avg > 0.1 else (-1 if jt_avg < -0.1 else 0)
            
            if pd_dir != 0 and jt_dir != 0 and pd_dir != jt_dir:
                # DIVERGENCE!
                divergences.append({
                    'timestamp': capture.timestamp,
                    'pd_signal': capture.pd_gile,
                    'jt_signal': jt_avg,
                    'outcome': capture.next_day_direction,
                    'pd_correct': pd_dir == capture.next_day_direction,
                    'jt_correct': jt_dir == capture.next_day_direction
                })
        
        if not divergences:
            return {'total_divergences': 0}
        
        pd_wins = sum(1 for d in divergences if d['pd_correct'])
        jt_wins = sum(1 for d in divergences if d['jt_correct'])
        
        return {
            'total_divergences': len(divergences),
            'pd_win_rate': pd_wins / len(divergences),
            'jt_win_rate': jt_wins / len(divergences),
            'stronger_predictor': 'PD' if pd_wins > jt_wins else ('JT' if jt_wins > pd_wins else 'TIE'),
            'sample_divergences': divergences[:5]
        }
    
    def identify_missing_components(self) -> List[str]:
        """
        Process of Illumination: Identify what's missing
        
        Compare FULL_TI accuracy with simpler configs to find gaps
        """
        insights = []
        
        if not self.experiment_results:
            return ["No experiment results loaded"]
        
        # Get accuracies
        full_acc = self.experiment_results.get('FULL_TI', {}).get('accuracy', 0)
        pd_only = self.experiment_results.get('PD_ONLY', {}).get('accuracy', 0)
        jt_only = self.experiment_results.get('JT_ONLY', {}).get('accuracy', 0)
        pd_jt = self.experiment_results.get('PD_JT', {}).get('accuracy', 0)
        pd_jt_mr = self.experiment_results.get('PD_JT_MR', {}).get('accuracy', 0)
        pd_jt_lcc = self.experiment_results.get('PD_JT_LCC', {}).get('accuracy', 0)
        
        # Analysis
        if pd_only > 0.55:
            insights.append(f"PD alone shows {pd_only*100:.1f}% accuracy - STRONG foundation")
        else:
            insights.append(f"PD alone shows {pd_only*100:.1f}% accuracy - needs enhancement")
        
        if jt_only > pd_only:
            insights.append(f"Jeff Time ({jt_only*100:.1f}%) beats PD ({pd_only*100:.1f}%) - JT is primary predictor")
        else:
            insights.append(f"PD ({pd_only*100:.1f}%) beats Jeff Time ({jt_only*100:.1f}%) - PD is primary predictor")
        
        if pd_jt > max(pd_only, jt_only):
            improvement = pd_jt - max(pd_only, jt_only)
            insights.append(f"PD+JT combined adds {improvement*100:.1f}% lift - SYNERGY confirmed")
        else:
            insights.append("PD+JT combined shows no synergy - may need different combination method")
        
        if pd_jt_mr > pd_jt:
            insights.append(f"MR adds {(pd_jt_mr - pd_jt)*100:.1f}% lift - contradiction resolution helps")
        else:
            insights.append("MR doesn't improve accuracy - contradiction resolution not the bottleneck")
        
        if pd_jt_lcc > pd_jt:
            insights.append(f"LCC adds {(pd_jt_lcc - pd_jt)*100:.1f}% lift - synchronization helps")
        else:
            insights.append("LCC doesn't improve accuracy - correlation not the bottleneck")
        
        # Identify what's missing
        if full_acc < 0.55:
            insights.append("")
            insights.append("=== MISSING COMPONENTS (Process of Illumination) ===")
            insights.append("Current TI dimensions achieve only {:.1f}% accuracy".format(full_acc * 100))
            insights.append("Potential missing factors:")
            insights.append("  1. VOLUME dimension (market conviction)")
            insights.append("  2. REGIME detection (bull/bear/sideways)")
            insights.append("  3. MOMENTUM confirmation (rate of change of change)")
            insights.append("  4. RESONANCE fields (cross-asset harmony)")
            insights.append("  5. TIME CYCLES (weekly/monthly patterns)")
        
        return insights
    
    def generate_report(self) -> str:
        """Generate full diagnostic report"""
        report = []
        report.append("="*70)
        report.append("TI STOCK PREDICTION DIAGNOSTIC REPORT")
        report.append("="*70)
        report.append("")
        
        # Ablation Results
        report.append("1. DIMENSION ABLATION RESULTS (Ranked by Accuracy)")
        report.append("-"*50)
        
        ranking = []
        for name, result in self.experiment_results.items():
            acc = result.get('accuracy', 0)
            ranking.append((name, acc, result.get('total_predictions', 0)))
        ranking.sort(key=lambda x: x[1], reverse=True)
        
        for name, acc, preds in ranking:
            report.append(f"  {name:25s}: {acc*100:5.1f}% ({preds} predictions)")
        
        report.append("")
        
        # Sacred Interval Analysis
        report.append("2. SACRED INTERVAL OCCUPANCY")
        report.append("-"*50)
        sacred = self.analyze_sacred_interval_occupancy()
        for zone, data in sacred.items():
            report.append(f"  {zone:8s}: {data['percentage']:5.1f}% of time | Next-day up prob: {data['next_day_up_probability']*100:5.1f}%")
        
        report.append("")
        
        # Divergence Analysis
        report.append("3. PD vs JEFF TIME DIVERGENCE")
        report.append("-"*50)
        div = self.analyze_dimension_divergence()
        report.append(f"  Total divergences: {div.get('total_divergences', 0)}")
        if div.get('total_divergences', 0) > 0:
            report.append(f"  PD win rate: {div.get('pd_win_rate', 0)*100:.1f}%")
            report.append(f"  JT win rate: {div.get('jt_win_rate', 0)*100:.1f}%")
            report.append(f"  Stronger predictor: {div.get('stronger_predictor', 'N/A')}")
        
        report.append("")
        
        # Missing Components
        report.append("4. PROCESS OF ILLUMINATION - MISSING COMPONENTS")
        report.append("-"*50)
        for insight in self.identify_missing_components():
            report.append(f"  {insight}")
        
        report.append("")
        report.append("="*70)
        
        return "\n".join(report)


# ============================================================================
# MAIN: RUN DIAGNOSTIC LAB
# ============================================================================

def run_diagnostic_lab():
    """Main function to run the TI Prediction Diagnostic Lab"""
    try:
        import yfinance as yf
    except ImportError:
        print("yfinance not installed. Install with: pip install yfinance")
        return
    
    print("="*70)
    print("TI STOCK PREDICTION DIAGNOSTIC LAB")
    print("PROVING which dimensions predict stock success")
    print("="*70)
    print()
    
    # Download data
    symbols = ['SPY', 'QQQ', 'AAPL', 'MSFT', 'GOOGL', 'TSLA', 'NVDA', 'AMD', 'META', 'AMZN']
    
    end_date = datetime.now()
    start_date = end_date - timedelta(days=365*5)  # 5 years
    
    print(f"Downloading 5 years of data for {len(symbols)} symbols...")
    
    all_data = {}
    for sym in symbols:
        try:
            ticker = yf.Ticker(sym)
            hist = ticker.history(start=start_date, end=end_date)
            if len(hist) > 0:
                all_data[sym] = hist
                print(f"  {sym}: {len(hist)} days")
        except Exception as e:
            print(f"  {sym}: FAILED - {e}")
    
    if len(all_data) < 5:
        print("Not enough data")
        return
    
    print()
    print("Processing TI dimensions...")
    
    # Create calculator and process data
    calculator = TIDimensionCalculator()
    all_captures = []
    
    # Get common dates across all symbols
    spy_data = all_data.get('SPY')
    if spy_data is None:
        print("SPY data required")
        return
    
    dates = spy_data.index.tolist()
    
    for i, date in enumerate(dates):
        # Add prices for all symbols
        for sym, data in all_data.items():
            if date in data.index:
                price = float(data.loc[date, 'Close'])
                calculator.add_price(sym, price, date)
        
        # After warmup period, capture dimensions
        if i >= 60:
            for sym, data in all_data.items():
                if len(calculator.price_history.get(sym, [])) >= 50:
                    capture = calculator.capture_all_dimensions(sym, date, reference_symbol='SPY')
                    
                    # Add next-day outcome if available
                    if i + 1 < len(dates):
                        next_date = dates[i + 1]
                        if next_date in data.index:
                            current = float(data.loc[date, 'Close'])
                            next_price = float(data.loc[next_date, 'Close'])
                            ret = (next_price - current) / current * 100
                            capture.next_day_return = ret
                            capture.next_day_direction = 1 if ret > 0.1 else (-1 if ret < -0.1 else 0)
                    
                    all_captures.append(capture)
    
    print(f"Captured {len(all_captures)} TI dimension snapshots")
    print()
    
    # Run ablation experiments
    experiment = AblationExperiment()
    results = experiment.run_all_experiments(all_captures)
    
    # Generate diagnostic report
    dashboard = TIDiagnosticDashboard()
    dashboard.load_results(results, all_captures)
    
    report = dashboard.generate_report()
    print(report)
    
    return results, all_captures, dashboard


if __name__ == "__main__":
    run_diagnostic_lab()
