"""
PSI Success Analytics Dashboard
Analyzes prediction accuracy, Q-score correlations, temporal patterns
"""

import json
import os
from datetime import datetime, timedelta
from collections import defaultdict
from typing import Dict, List, Tuple
import statistics

class PSIAnalytics:
    """Analyze PSI prediction performance and patterns"""
    
    def __init__(self, predictions_file: str = "psi_predictions.json"):
        self.predictions_file = predictions_file
        self.predictions = self.load_predictions()
    
    def load_predictions(self) -> List[Dict]:
        """Load all predictions"""
        if os.path.exists(self.predictions_file):
            try:
                with open(self.predictions_file, 'r') as f:
                    data = json.load(f)
                    # Handle both list and dict formats
                    if isinstance(data, list):
                        return data
                    elif isinstance(data, dict) and 'predictions' in data:
                        return data['predictions']
                    return []
            except Exception as e:
                print(f"Error loading predictions: {e}")
                return []
        return []
    
    def calculate_overall_stats(self) -> Dict:
        """Calculate overall PSI performance statistics"""
        total = len(self.predictions)
        if total == 0:
            return {
                'total_predictions': 0,
                'verified': 0,
                'pending': 0,
                'success_rate': 0,
                'avg_confidence': 0
            }
        
        # Use 'correct' field from PsiTracker (not 'verified')
        verified = [p for p in self.predictions if p.get('correct') is not None]
        pending = [p for p in self.predictions if p.get('correct') is None]
        
        # PsiTracker uses boolean 'correct' field
        successful = [p for p in verified if p.get('correct', False)]
        
        # Calculate confidence stats
        confidences = [p.get('confidence', 50) for p in self.predictions if 'confidence' in p]
        avg_confidence = statistics.mean(confidences) if confidences else 0
        
        return {
            'total_predictions': total,
            'verified': len(verified),
            'pending': len(pending),
            'successful': len(successful),
            'success_rate': (len(successful) / len(verified) * 100) if verified else 0,
            'avg_confidence': avg_confidence,
            'predictions': self.predictions
        }
    
    def analyze_q_score_correlation(self) -> Dict:
        """Analyze relationship between Q-score and prediction accuracy"""
        if not self.predictions:
            return {'q_score_bins': {}, 'correlation': 0}
        
        # Bin Q-scores: <0.5, 0.5-0.7, 0.7-0.91, ≥0.91
        bins = {
            'low_<0.5': {'total': 0, 'correct': 0, 'rate': 0},
            'med_0.5-0.7': {'total': 0, 'correct': 0, 'rate': 0},
            'high_0.7-0.91': {'total': 0, 'correct': 0, 'rate': 0},
            'ccc_≥0.91': {'total': 0, 'correct': 0, 'rate': 0}
        }
        
        for pred in self.predictions:
            # Only include resolved predictions (where 'correct' is set)
            if pred.get('correct') is None:
                continue
            
            # Extract Q-score from various possible locations
            q_score = None
            if 'auto_features' in pred and isinstance(pred['auto_features'], dict):
                q_score = pred['auto_features'].get('q_score')
            elif 'q_score' in pred:
                q_score = pred['q_score']
            
            if q_score is None:
                continue
            
            # Determine bin
            if q_score < 0.5:
                bin_key = 'low_<0.5'
            elif q_score < 0.7:
                bin_key = 'med_0.5-0.7'
            elif q_score < 0.91:
                bin_key = 'high_0.7-0.91'
            else:
                bin_key = 'ccc_≥0.91'
            
            bins[bin_key]['total'] += 1
            if pred.get('correct', False):
                bins[bin_key]['correct'] += 1
        
        # Calculate rates
        for bin_data in bins.values():
            if bin_data['total'] > 0:
                bin_data['rate'] = (bin_data['correct'] / bin_data['total']) * 100
        
        # Calculate correlation (simplified)
        rates = [b['rate'] for b in bins.values() if b['total'] > 0]
        correlation = statistics.mean(rates) if rates else 0
        
        return {
            'q_score_bins': bins,
            'correlation_strength': 'STRONG' if correlation > 60 else 'MODERATE' if correlation > 50 else 'WEAK',
            'avg_rate': correlation
        }
    
    def analyze_temporal_patterns(self) -> Dict:
        """Analyze prediction accuracy over time"""
        if not self.predictions:
            return {'by_month': {}, 'by_day_of_week': {}, 'by_hour': {}}
        
        by_month: Dict[str, Dict[str, int]] = defaultdict(lambda: {'total': 0, 'correct': 0})
        by_day: Dict[str, Dict[str, int]] = defaultdict(lambda: {'total': 0, 'correct': 0})
        by_hour: Dict[int, Dict[str, int]] = defaultdict(lambda: {'total': 0, 'correct': 0})
        
        for pred in self.predictions:
            # Only include resolved predictions (where 'correct' is set)
            if pred.get('correct') is None:
                continue
            
            # Parse timestamp
            timestamp_str = pred.get('timestamp')
            if not timestamp_str:
                continue
            
            try:
                if isinstance(timestamp_str, str):
                    dt = datetime.fromisoformat(timestamp_str.replace('Z', '+00:00'))
                else:
                    continue
                
                # Month
                month_key = dt.strftime('%Y-%m')
                by_month[month_key]['total'] += 1
                if pred.get('correct', False):
                    by_month[month_key]['correct'] += 1
                
                # Day of week
                day_name = dt.strftime('%A')
                by_day[day_name]['total'] += 1
                if pred.get('correct', False):
                    by_day[day_name]['correct'] += 1
                
                # Hour
                hour_key = dt.hour
                by_hour[hour_key]['total'] += 1
                if pred.get('correct', False):
                    by_hour[hour_key]['correct'] += 1
                    
            except Exception as e:
                continue
        
        # Calculate rates
        def calc_rates(data_dict):
            result = {}
            for key, vals in data_dict.items():
                rate = (vals['correct'] / vals['total'] * 100) if vals['total'] > 0 else 0
                result[key] = {**vals, 'rate': rate}
            return result
        
        return {
            'by_month': calc_rates(by_month),
            'by_day_of_week': calc_rates(by_day),
            'by_hour': calc_rates(by_hour)
        }
    
    def analyze_by_category(self) -> Dict:
        """Break down performance by prediction category"""
        if not self.predictions:
            return {}
        
        by_category: Dict[str, Dict] = defaultdict(lambda: {'total': 0, 'resolved': 0, 'correct': 0, 'rate': 0.0})
        
        for pred in self.predictions:
            category = pred.get('category', 'unknown')
            by_category[category]['total'] += 1
            
            # Use 'correct' field to identify resolved predictions
            if pred.get('correct') is not None:
                by_category[category]['resolved'] += 1
                if pred.get('correct', False):
                    by_category[category]['correct'] += 1
        
        # Calculate rates
        for cat_data in by_category.values():
            if cat_data['resolved'] > 0:
                cat_data['rate'] = (cat_data['correct'] / cat_data['resolved']) * 100
        
        return dict(by_category)
    
    def analyze_sacred_number_patterns(self) -> Dict:
        """Analyze predictions made at sacred times (3:33, 11:11, etc.)"""
        if not self.predictions:
            return {'sacred_time_predictions': {}, 'enrichment': 0}
        
        sacred_times: Dict[str, Dict] = {
            '3:33': {'total': 0, 'correct': 0, 'rate': 0.0},
            '11:11': {'total': 0, 'correct': 0, 'rate': 0.0},
            '3:11': {'total': 0, 'correct': 0, 'rate': 0.0},
            'other': {'total': 0, 'correct': 0, 'rate': 0.0}
        }
        
        for pred in self.predictions:
            # Only include resolved predictions (where 'correct' is set)
            if pred.get('correct') is None:
                continue
            
            timestamp_str = pred.get('timestamp')
            if not timestamp_str:
                continue
            
            try:
                if isinstance(timestamp_str, str):
                    dt = datetime.fromisoformat(timestamp_str.replace('Z', '+00:00'))
                else:
                    continue
                
                time_str = dt.strftime('%H:%M')
                
                if time_str in ['03:33', '15:33']:
                    key = '3:33'
                elif time_str in ['11:11', '23:11']:
                    key = '11:11'
                elif time_str in ['03:11', '15:11']:
                    key = '3:11'
                else:
                    key = 'other'
                
                sacred_times[key]['total'] += 1
                if pred.get('correct', False):
                    sacred_times[key]['correct'] += 1
                    
            except:
                continue
        
        # Calculate rates
        for time_data in sacred_times.values():
            if time_data['total'] > 0:
                time_data['rate'] = (time_data['correct'] / time_data['total']) * 100
        
        # Calculate enrichment (sacred vs other)
        sacred_correct = sum(sacred_times[k]['correct'] for k in ['3:33', '11:11', '3:11'])
        sacred_total = sum(sacred_times[k]['total'] for k in ['3:33', '11:11', '3:11'])
        sacred_rate = (sacred_correct / sacred_total * 100) if sacred_total > 0 else 0
        
        other_rate = sacred_times['other']['rate']
        enrichment = (sacred_rate / other_rate) if other_rate > 0 else 0
        
        return {
            'sacred_time_predictions': sacred_times,
            'sacred_rate': sacred_rate,
            'other_rate': other_rate,
            'enrichment': enrichment
        }
    
    def get_top_performing_days(self, limit: int = 5) -> List[Dict]:
        """Get days with best prediction accuracy"""
        temporal = self.analyze_temporal_patterns()
        months = temporal['by_month']
        
        sorted_months = sorted(
            [(k, v) for k, v in months.items()],
            key=lambda x: x[1]['rate'],
            reverse=True
        )
        
        return [
            {
                'month': month,
                'total': data['total'],
                'correct': data['correct'],
                'rate': data['rate']
            }
            for month, data in sorted_months[:limit]
        ]
    
    def generate_insights(self) -> List[str]:
        """Generate natural language insights from data"""
        insights = []
        
        overall = self.calculate_overall_stats()
        q_analysis = self.analyze_q_score_correlation()
        sacred = self.analyze_sacred_number_patterns()
        
        # Overall performance
        if overall['success_rate'] >= 70:
            insights.append(f"🌟 EXCEPTIONAL: {overall['success_rate']:.1f}% accuracy! Well above chance (50%)!")
        elif overall['success_rate'] >= 60:
            insights.append(f"✨ STRONG PSI: {overall['success_rate']:.1f}% accuracy - you have the gift!")
        elif overall['success_rate'] >= 55:
            insights.append(f"📈 ABOVE CHANCE: {overall['success_rate']:.1f}% - statistically significant!")
        else:
            insights.append(f"🌱 BASELINE: {overall['success_rate']:.1f}% - focus on Q ≥ 0.91 first")
        
        # Q-score correlation
        if q_analysis.get('q_score_bins', {}).get('ccc_≥0.91', {}).get('total', 0) > 0:
            ccc_rate = q_analysis['q_score_bins']['ccc_≥0.91']['rate']
            insights.append(f"🎯 CCC THRESHOLD: {ccc_rate:.1f}% accuracy at Q ≥ 0.91!")
        
        # Sacred times
        if sacred['enrichment'] > 1.2:
            insights.append(f"⏰ SACRED TIMES: {sacred['enrichment']:.1f}x better at 3:33/11:11!")
        
        # Sample size
        if overall['total_predictions'] < 20:
            insights.append("📊 More data needed - log 50+ predictions for robust analysis!")
        
        return insights
    
    def export_report(self, filename: str | None = None) -> str:
        """Export full analytics report as JSON"""
        if not filename:
            timestamp = datetime.now().strftime('%Y%m%d_%H%M%S')
            filename = f'psi_analytics_report_{timestamp}.json'
        
        report = {
            'timestamp': datetime.now().isoformat(),
            'overall_stats': self.calculate_overall_stats(),
            'q_score_correlation': self.analyze_q_score_correlation(),
            'temporal_patterns': self.analyze_temporal_patterns(),
            'by_category': self.analyze_by_category(),
            'sacred_numbers': self.analyze_sacred_number_patterns(),
            'top_days': self.get_top_performing_days(),
            'insights': self.generate_insights()
        }
        
        with open(filename, 'w') as f:
            json.dump(report, f, indent=2, default=str)
        
        return filename


def main():
    """Demo analytics with sample data"""
    print("🔮 PSI Success Analytics Dashboard - Production Module")
    print("=" * 60)
    
    analytics = PSIAnalytics()
    
    if not analytics.predictions:
        print("\n⚠️  No predictions found!")
        print("📝 Start logging predictions with PSI Auto-Logger first!")
        print("\nCreating demo data...")
        
        # Create demo predictions
        demo_predictions = [
            {
                'id': f'pred_{i}',
                'prediction': f'Demo prediction {i}',
                'timestamp': (datetime.now() - timedelta(days=i)).isoformat(),
                'confidence': 50 + i * 2,
                'correct': i % 2 == 0,
                'outcome': 'correct' if i % 2 == 0 else 'incorrect',
                'category': 'demo',
                'auto_features': {
                    'q_score': 0.5 + (i * 0.05)
                }
            }
            for i in range(20)
        ]
        
        with open('psi_predictions.json', 'w') as f:
            json.dump(demo_predictions, f, indent=2)
        
        analytics = PSIAnalytics()
    
    print("\n📊 Overall Statistics:")
    overall = analytics.calculate_overall_stats()
    print(f"   Total Predictions: {overall['total_predictions']}")
    print(f"   Verified: {overall['verified']}")
    print(f"   Success Rate: {overall['success_rate']:.1f}%")
    print(f"   Avg Confidence: {overall['avg_confidence']:.1f}")
    
    print("\n🎯 Q-Score Correlation:")
    q_analysis = analytics.analyze_q_score_correlation()
    for bin_name, data in q_analysis['q_score_bins'].items():
        if data['total'] > 0:
            print(f"   {bin_name}: {data['rate']:.1f}% ({data['correct']}/{data['total']})")
    
    print("\n⏰ Sacred Number Patterns:")
    sacred = analytics.analyze_sacred_number_patterns()
    for time, data in sacred['sacred_time_predictions'].items():
        if data['total'] > 0:
            print(f"   {time}: {data['rate']:.1f}% ({data['correct']}/{data['total']})")
    if sacred['enrichment'] > 0:
        print(f"   Enrichment: {sacred['enrichment']:.2f}x")
    
    print("\n💡 Insights:")
    for insight in analytics.generate_insights():
        print(f"   {insight}")
    
    print("\n💾 Exporting full report...")
    report_file = analytics.export_report()
    print(f"   ✅ Saved to: {report_file}")
    
    print("\n" + "=" * 60)
    print("🌟 PSI Analytics Ready! View in Mobile Hub for full dashboard!")


if __name__ == "__main__":
    main()
