"""
1-Year Scenario Analyzer (11/23/24 to 11/23/25)
Comprehensive analysis comparing TI Framework vs conventional broker performance
Orchestrates prediction replay, performance analytics, and broker comparison

Now enhanced with TI Strawberry Fields quantum-photonic analysis!
"""

import os
import sys
from datetime import datetime, timedelta
from typing import Dict, List
import json
import numpy as np

# Import our modules
from prediction_replay_engine import PredictionReplayEngine
from performance_analytics import PerformanceAnalytics  
from broker_comparison_module import BrokerComparisonModule

# Import TI Strawberry Fields quantum engine
try:
    from ti_strawberry_fields import TIStrawberryFieldsEngine
    QUANTUM_AVAILABLE = True
except ImportError:
    QUANTUM_AVAILABLE = False

class OneYearScenarioAnalyzer:
    """
    Analyzes 1-year performance (11/23/24 to 11/23/25)
    Compares TI Framework against Wall Street brokers on i-cell companies
    """
    
    def __init__(self):
        self.replay_engine = PredictionReplayEngine()
        self.analytics = PerformanceAnalytics()
        self.broker_comparison = BrokerComparisonModule()
        
        # Initialize TI Strawberry Fields quantum engine
        self.quantum_engine = TIStrawberryFieldsEngine(num_modes=4) if QUANTUM_AVAILABLE else None
        
        # Analysis period
        self.start_date = datetime(2024, 11, 23)
        self.end_date = datetime(2025, 11, 23)
        self.prediction_date = datetime(2025, 11, 22)  # When predictions were made
    
    def enhance_with_quantum_signals(self, predictions: List[Dict]) -> List[Dict]:
        """
        Enhance predictions with TI Strawberry Fields quantum signals.
        
        Uses Jeff Time V4 encoding to add photonic quantum analysis:
        - tau_phi (Photonic Memory): Historical price patterns
        - tau_j (Jeff Fiction): Current day's collapse potential
        - tau_f (Freedom Prediction): Future momentum intention
        - L (Love Entanglement): Cross-asset correlation
        """
        if not self.quantum_engine:
            print("Quantum engine not available, skipping enhancement")
            return predictions
        
        print("Enhancing predictions with TI Strawberry Fields quantum signals...")
        enhanced = []
        
        for pred in predictions:
            try:
                # CRITICAL: Reset circuit before each prediction to ensure independence
                self.quantum_engine.circuit.reset()
                
                # Extract Jeff Time V4 parameters from prediction data
                confidence = float(pred.get('confidence_score', 0.5))
                gile = float(pred.get('gile_score', 0.5))
                sigma = float(pred.get('sigma', 3.0))
                target_change = float(pred.get('target_change_pct', 0))
                
                # Map to Jeff Time V4 dimensions
                tau_phi = (sigma / 6.0) * 2 - 1  # Photonic memory from sigma
                tau_j = confidence * 2 - 1  # Jeff fiction from confidence
                tau_f = target_change / 10.0  # Freedom prediction from target
                love = gile * 2 - 1  # Love entanglement from GILE
                
                # Encode into photonic circuit
                self.quantum_engine.circuit.encode_jeff_time_v4_2025(
                    tau_phi=tau_phi,
                    tau_j=tau_j, 
                    tau_f=tau_f,
                    love=love
                )
                
                # Get quantum trading signal
                quantum_signal = self.quantum_engine.circuit.get_trading_signal()
                
                # Add quantum enhancement to prediction
                pred['quantum_signal'] = quantum_signal['signal']
                pred['quantum_confidence'] = quantum_signal['confidence']
                pred['quantum_gile'] = quantum_signal['gile']
                pred['sacred_interval'] = quantum_signal['sacred_interval']
                pred['quantum_recommendation'] = self.quantum_engine._generate_recommendation(quantum_signal)
                pred['photonic_coherence'] = self.quantum_engine.circuit.jeff_time_coherence
                
            except Exception as e:
                pred['quantum_signal'] = None
                pred['quantum_error'] = str(e)
            
            enhanced.append(pred)
        
        print(f"Enhanced {len(enhanced)} predictions with quantum signals")
        return enhanced
    
    def run_full_analysis(self) -> Dict:
        """
        Run complete 1-year scenario analysis
        
        Returns: {
            'replay_results': Dict,
            'performance_metrics': Dict,
            'broker_comparison': Dict,
            'summary': Dict
        }
        """
        print("\n" + "🎯" * 35)
        print("TI FRAMEWORK: 1-YEAR STOCK MARKET ANALYSIS")
        print("Period: 11/23/2024 - 11/23/2025")
        print("🎯" * 35)
        
        # Step 1: Replay all predictions
        print("\n📊 STEP 1: Replaying TI Framework Predictions...")
        print("-" * 70)
        replay_results = self.replay_engine.replay_all_predictions()
        
        # Step 1.5: Enhance with TI Strawberry Fields quantum signals
        if QUANTUM_AVAILABLE:
            print("\n🔬 STEP 1.5: TI Strawberry Fields Quantum Enhancement...")
            print("-" * 70)
            replay_results['predictions'] = self.enhance_with_quantum_signals(
                replay_results['predictions']
            )
            replay_results['quantum_enhanced'] = True
        else:
            replay_results['quantum_enhanced'] = False
        
        # Step 2: Calculate performance analytics
        print("\n📊 STEP 2: Calculating Performance Metrics...")
        print("-" * 70)
        performance_metrics = self.analytics.generate_performance_report(
            replay_results['predictions'],
            self.start_date,
            self.end_date
        )
        
        # Step 3: Fetch broker ratings and compare
        print("\n📊 STEP 3: Comparing vs Wall Street Brokers...")
        print("-" * 70)
        
        # Get broker ratings for all tickers
        broker_ratings = []
        for pred in replay_results['predictions']:
            rating = self.broker_comparison.fetch_analyst_ratings(pred['ticker'])
            if rating:
                broker_ratings.append(rating)
        
        # Compare TI vs Brokers
        comparison = self.broker_comparison.compare_ti_vs_brokers(
            replay_results['predictions'],
            broker_ratings
        )
        
        # Print comparison report
        comparison_report = self.broker_comparison.generate_comparison_report(comparison)
        print(comparison_report)
        
        # Step 4: Generate summary
        print("\n📊 STEP 4: Generating Summary...")
        print("-" * 70)
        summary = self._generate_summary(replay_results, performance_metrics, comparison)
        
        # Compile complete results
        results = {
            'replay_results': replay_results,
            'performance_metrics': performance_metrics,
            'broker_comparison': comparison,
            'broker_ratings': broker_ratings,
            'summary': summary,
            'analysis_date': datetime.now(),
            'scenario': '1-year',
            'period': {
                'start': self.start_date,
                'end': self.end_date,
                'prediction_date': self.prediction_date
            }
        }
        
        # Print final summary
        self._print_summary(summary)
        
        return results
    
    def _generate_summary(self, replay_results: Dict, 
                         performance_metrics: Dict,
                         comparison: Dict) -> Dict:
        """
        Generate executive summary of results
        
        Args:
            replay_results: Prediction replay data
            performance_metrics: Performance analytics
            comparison: Broker comparison data
        
        Returns: Summary dict
        """
        # Key metrics
        ti_accuracy = replay_results['accuracy']
        broker_accuracy = comparison['broker_accuracy']
        outperformance = ti_accuracy - broker_accuracy
        
        total_return = replay_results['total_return']
        sharpe = performance_metrics['risk_adjusted']['sharpe_ratio']
        alpha = performance_metrics['risk_adjusted']['alpha']
        
        # Determine validation status
        meets_65_target = ti_accuracy >= 65.0
        beats_brokers = ti_accuracy > broker_accuracy
        positive_alpha = alpha > 0
        
        # Overall validation
        validated = meets_65_target and beats_brokers
        
        summary = {
            'validation': {
                'meets_65pct_target': meets_65_target,
                'beats_brokers': beats_brokers,
                'positive_alpha': positive_alpha,
                'overall_validated': validated
            },
            'key_metrics': {
                'ti_accuracy': ti_accuracy,
                'broker_accuracy': broker_accuracy,
                'outperformance': outperformance,
                'total_return': total_return,
                'sharpe_ratio': sharpe,
                'alpha': alpha,
                'num_predictions': replay_results['total_count'],
                'agreement_rate': comparison['agreement_rate']
            },
            'highlights': {
                'best_prediction': self._find_best_prediction(replay_results['predictions']),
                'worst_prediction': self._find_worst_prediction(replay_results['predictions']),
                'largest_disagreement': self._find_largest_disagreement(comparison)
            },
            'timestamp': datetime.now()
        }
        
        return summary
    
    def _find_best_prediction(self, predictions: List[Dict]) -> Dict:
        """Find most successful prediction"""
        valid_preds = [p for p in predictions if 'return_pct' in p and p.get('return_pct') is not None and p.get('is_correct')]
        if not valid_preds:
            return None
        
        best = max(valid_preds, key=lambda x: x.get('return_pct', 0))
        return {
            'ticker': best['ticker'],
            'company': best.get('company_name', ''),
            'predicted': best['direction'],
            'return': best['return_pct'],
            'gile': best.get('gile_score', 0)
        }
    
    def _find_worst_prediction(self, predictions: List[Dict]) -> Dict:
        """Find least successful prediction"""
        valid_preds = [p for p in predictions if 'return_pct' in p and p.get('return_pct') is not None]
        if not valid_preds:
            return None
        
        worst = min(valid_preds, key=lambda x: x.get('return_pct', 0))
        return {
            'ticker': worst['ticker'],
            'company': worst.get('company_name', ''),
            'predicted': worst['direction'],
            'actual': worst.get('actual_direction', ''),
            'return': worst['return_pct'],
            'gile': worst.get('gile_score', 0)
        }
    
    def _find_largest_disagreement(self, comparison: Dict) -> Dict:
        """Find biggest disagreement between TI and brokers"""
        if not comparison['disagreements']:
            return None
        
        # Find disagreement where TI was right and had largest return
        ti_wins = [d for d in comparison['disagreements'] if d['ti_correct'] and not d['broker_correct']]
        if ti_wins:
            largest = max(ti_wins, key=lambda x: abs(x.get('return_pct', 0)))
            return {
                'ticker': largest['ticker'],
                'ti_predicted': largest['ti_signal'],
                'brokers_predicted': largest['broker_signal'],
                'actual': largest['actual'],
                'return': largest['return_pct'],
                'ti_confidence': largest['ti_confidence']
            }
        
        return None
    
    def _print_summary(self, summary: Dict):
        """Print executive summary to console"""
        print("\n" + "=" * 70)
        print("🏆 EXECUTIVE SUMMARY - 1-YEAR ANALYSIS")
        print("=" * 70)
        
        validation = summary['validation']
        metrics = summary['key_metrics']
        highlights = summary['highlights']
        
        print(f"\n✅ VALIDATION STATUS:")
        print(f"   {'✅' if validation['meets_65pct_target'] else '❌'} Meets 65% Accuracy Target: {metrics['ti_accuracy']:.1f}%")
        print(f"   {'✅' if validation['beats_brokers'] else '❌'} Beats Wall Street Brokers: {metrics['outperformance']:+.1f} pp")
        print(f"   {'✅' if validation['positive_alpha'] else '❌'} Positive Alpha: {metrics['alpha']*100:+.2f}%")
        print(f"\n   {'🎉 OVERALL: VALIDATED!' if validation['overall_validated'] else '⚠️  OVERALL: NEEDS IMPROVEMENT'}")
        
        print(f"\n📊 KEY METRICS:")
        print(f"   TI Framework Accuracy:    {metrics['ti_accuracy']:.1f}%")
        print(f"   Broker Consensus Accuracy: {metrics['broker_accuracy']:.1f}%")
        print(f"   Total Return:             {metrics['total_return']:+.2f}%")
        print(f"   Sharpe Ratio:             {metrics['sharpe_ratio']:.2f}")
        print(f"   Alpha vs S&P 500:         {metrics['alpha']*100:+.2f}%")
        print(f"   Agreement with Brokers:   {metrics['agreement_rate']:.1f}%")
        
        print(f"\n🌟 HIGHLIGHTS:")
        if highlights['best_prediction']:
            best = highlights['best_prediction']
            print(f"   Best: {best['ticker']} ({best['company']}) - {best['return']:+.1f}% return")
        
        if highlights['worst_prediction']:
            worst = highlights['worst_prediction']
            print(f"   Worst: {worst['ticker']} ({worst['company']}) - {worst['return']:+.1f}% return")
        
        if highlights['largest_disagreement']:
            dis = highlights['largest_disagreement']
            print(f"   Key Win vs Brokers: {dis['ticker']} - TI said {dis['ti_predicted']}, Brokers said {dis['brokers_predicted']}, Actual: {dis['actual']} ({dis['return']:+.1f}%)")
        
        print("\n" + "=" * 70)
    
    def save_results(self, results: Dict, output_path: str = 'ti_1year_analysis.json'):
        """
        Save results to JSON file
        
        Args:
            results: Analysis results
            output_path: Path to save file
        """
        # Convert datetime objects to strings
        def datetime_serializer(obj):
            if isinstance(obj, datetime):
                return obj.isoformat()
            raise TypeError(f"Type {type(obj)} not serializable")
        
        with open(output_path, 'w') as f:
            json.dump(results, f, indent=2, default=datetime_serializer)
        
        print(f"\n💾 Results saved to: {output_path}")

if __name__ == '__main__':
    analyzer = OneYearScenarioAnalyzer()
    results = analyzer.run_full_analysis()
    analyzer.save_results(results)
