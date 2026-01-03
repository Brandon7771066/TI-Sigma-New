"""
Psi Tracker - Empirical Validation System
Tracks all predictions across ALL psi methods and measures actual accuracy
"""

import streamlit as st
import pandas as pd
from datetime import datetime
from typing import Dict, List, Any, Optional
import json
import os

class PsiTracker:
    """
    Central tracking system for ALL psi-based predictions
    Stores predictions, tracks outcomes, calculates accuracy
    """
    
    def __init__(self, storage_file: str = "psi_predictions.json"):
        self.storage_file = storage_file
        self.predictions = self.load_predictions()
    
    def load_predictions(self) -> List[Dict[str, Any]]:
        """Load predictions from storage"""
        if os.path.exists(self.storage_file):
            try:
                with open(self.storage_file, 'r') as f:
                    return json.load(f)
            except:
                return []
        return []
    
    def save_predictions(self):
        """Save predictions to storage"""
        with open(self.storage_file, 'w') as f:
            json.dump(self.predictions, f, indent=2, default=str)
    
    def add_prediction(
        self,
        prediction_id: str,
        category: str,  # "stock", "prediction_market", "numerology", "weather"
        description: str,
        prediction: str,  # "BUY AAPL", "YES on election", etc.
        confidence: float,  # 0.0 to 1.0
        psi_methods: List[str],  # ["numerology", "cosmic_timing", "weather"]
        psi_scores: Dict[str, float],  # {"numerology": 1.8, "cosmic_timing": 2.0}
        metadata: Dict[str, Any],  # Additional context
        close_date: datetime,
        user_life_path: int
    ) -> str:
        """
        Add a new prediction to tracking system
        Returns prediction ID
        """
        prediction_data = {
            'id': prediction_id,
            'category': category,
            'description': description,
            'prediction': prediction,
            'confidence': confidence,
            'psi_methods': psi_methods,
            'psi_scores': psi_scores,
            'composite_score': sum(psi_scores.values()) / len(psi_scores) if psi_scores else 0.0,
            'metadata': metadata,
            'created_at': datetime.now().isoformat(),
            'close_date': close_date.isoformat(),
            'user_life_path': user_life_path,
            'outcome': None,  # To be filled when resolved
            'correct': None,  # True/False when resolved
            'profit': None,  # For money-based predictions
            'resolved_at': None
        }
        
        self.predictions.append(prediction_data)
        self.save_predictions()
        
        return prediction_id
    
    def resolve_prediction(
        self,
        prediction_id: str,
        outcome: str,
        correct: bool,
        profit: Optional[float] = None
    ):
        """Mark prediction as resolved with outcome"""
        for pred in self.predictions:
            if pred['id'] == prediction_id:
                pred['outcome'] = outcome
                pred['correct'] = correct
                pred['profit'] = profit
                pred['resolved_at'] = datetime.now().isoformat()
                self.save_predictions()
                return True
        return False
    
    def get_all_predictions(self) -> List[Dict[str, Any]]:
        """Get all predictions"""
        return self.predictions
    
    def get_accuracy_stats(self, category: Optional[str] = None) -> Dict[str, Any]:
        """Calculate accuracy statistics"""
        resolved = [p for p in self.predictions if p.get('correct') is not None]
        
        if category:
            resolved = [p for p in resolved if p.get('category') == category]
        
        if not resolved:
            return {
                'total_predictions': 0,
                'resolved': 0,
                'accuracy': 0.0,
                'total_profit': 0.0
            }
        
        correct_count = sum(1 for p in resolved if p.get('correct', False))
        total_profit = sum(p.get('profit', 0.0) for p in resolved if p.get('profit') is not None)
        
        return {
            'total_predictions': len(self.predictions),
            'resolved': len(resolved),
            'accuracy': correct_count / len(resolved) if resolved else 0.0,
            'correct_count': correct_count,
            'incorrect_count': len(resolved) - correct_count,
            'total_profit': total_profit,
            'avg_confidence': sum(p.get('confidence', 0.0) for p in resolved) / len(resolved) if resolved else 0.0,
            'avg_composite_score': sum(p.get('composite_score', 0.0) for p in resolved) / len(resolved) if resolved else 0.0
        }
    
    def get_psi_method_performance(self) -> Dict[str, Dict[str, float]]:
        """Calculate performance by psi method"""
        resolved = [p for p in self.predictions if p.get('correct') is not None]
        
        if not resolved:
            return {}
        
        method_stats = {}
        
        # Get all unique methods
        all_methods = set()
        for pred in resolved:
            psi_methods = pred.get('psi_methods', [])
            if psi_methods:
                all_methods.update(psi_methods)
        
        for method in all_methods:
            predictions_with_method = [p for p in resolved if method in p.get('psi_methods', [])]
            
            if predictions_with_method:
                correct = sum(1 for p in predictions_with_method if p.get('correct', False))
                total = len(predictions_with_method)
                avg_score = sum(p.get('psi_scores', {}).get(method, 0) for p in predictions_with_method) / total
                
                method_stats[method] = {
                    'accuracy': correct / total,
                    'count': total,
                    'avg_score': avg_score,
                    'correct': correct,
                    'incorrect': total - correct
                }
        
        return method_stats
    
    def get_calibration_data(self) -> pd.DataFrame:
        """
        Get calibration data: predicted confidence vs actual accuracy
        Returns DataFrame for plotting
        """
        resolved = [p for p in self.predictions if p.get('correct') is not None]
        
        if not resolved:
            return pd.DataFrame()
        
        # Bin by confidence
        bins = [0.0, 0.5, 0.6, 0.7, 0.8, 0.9, 1.0]
        bin_labels = ['<50%', '50-60%', '60-70%', '70-80%', '80-90%', '90-100%']
        
        calibration_data = []
        
        for i, (bin_low, bin_high) in enumerate(zip(bins[:-1], bins[1:])):
            preds_in_bin = [p for p in resolved if p.get('confidence') is not None and bin_low <= p.get('confidence', 0) < bin_high]
            
            if preds_in_bin:
                actual_accuracy = sum(1 for p in preds_in_bin if p.get('correct', False)) / len(preds_in_bin)
                avg_confidence = sum(p.get('confidence', 0) for p in preds_in_bin) / len(preds_in_bin)
                
                calibration_data.append({
                    'bin': bin_labels[i],
                    'predicted_confidence': avg_confidence,
                    'actual_accuracy': actual_accuracy,
                    'count': len(preds_in_bin)
                })
        
        return pd.DataFrame(calibration_data)
    
    def get_recent_predictions(self, limit: int = 10) -> List[Dict[str, Any]]:
        """Get most recent predictions"""
        # Filter out predictions without created_at, then sort
        preds_with_date = [p for p in self.predictions if p.get('created_at')]
        sorted_preds = sorted(
            preds_with_date,
            key=lambda x: x.get('created_at', ''),
            reverse=True
        )
        return sorted_preds[:limit]
    
    def get_unresolved_predictions(self) -> List[Dict[str, Any]]:
        """Get predictions awaiting resolution"""
        return [p for p in self.predictions if p.get('correct') is None]

# ============================================================================
# CROSS-MODULE PSI INTEGRATION
# ============================================================================

class PsiCrossTalk:
    """
    Enable cross-talk between all psi modules
    Share numerology, cosmic timing, weather, etc.
    """
    
    @staticmethod
    def get_cosmic_context(date: datetime, user_life_path: int) -> Dict[str, Any]:
        """
        Get complete cosmic context for any prediction
        Shared across ALL modules
        """
        from numerology_validation import analyze_date_with_multiple_masters
        
        date_analysis = analyze_date_with_multiple_masters(date)
        
        return {
            'date': date.isoformat(),
            'date_life_path': date_analysis['life_path']['life_path'],
            'date_energy': date_analysis.get('overall_significance', 0.5),
            'master_numbers': len(date_analysis.get('interpretations', [])),
            'user_life_path': user_life_path,
            'month': date.month,
            'day': date.day,
            'year': date.year,
            'day_of_week': date.strftime('%A')
        }
    
    @staticmethod
    def calculate_event_numerology(text: str) -> int:
        """
        Calculate numerology for ANY text (ticker, event title, etc.)
        Shared calculation method
        """
        from numerology_validation import reduce_to_single_digit
        
        total = sum([ord(c) for c in text.upper() if c.isalpha()])
        return reduce_to_single_digit(total, preserve_master=True)
    
    @staticmethod
    def get_weather_psi(location: str = "default") -> Dict[str, Any]:
        """
        Get weather-based psi indicators
        Placeholder for future weather divination integration
        """
        # TODO: Integrate weather API
        return {
            'available': False,
            'method': 'weather_divination',
            'score': 0.0,
            'message': 'Weather divination not yet integrated'
        }
    
    @staticmethod
    def get_synchronicity_score(context: Dict[str, Any]) -> float:
        """
        Calculate synchronicity score based on multi-dimensional alignment
        """
        alignments = []
        
        # Check if date energy is strong
        if context.get('date_energy', 0) >= 2.0:
            alignments.append(1.5)
        elif context.get('date_energy', 0) >= 1.5:
            alignments.append(1.0)
        
        # Check for Master Number days
        if context.get('master_numbers', 0) >= 2:
            alignments.append(1.8)
        elif context.get('master_numbers', 0) >= 1:
            alignments.append(1.2)
        
        # Check day of week patterns
        if context.get('day_of_week') in ['Monday', 'Friday']:  # Market edges
            alignments.append(0.8)
        
        return sum(alignments) / len(alignments) if alignments else 0.5
    
    @staticmethod
    def combine_psi_scores(scores: Dict[str, float]) -> float:
        """
        Combine multiple psi method scores into composite
        Uses weighted average (not multiplication - PRF theory!)
        """
        if not scores:
            return 0.0
        
        # Weight different methods
        weights = {
            'numerology': 1.0,
            'cosmic_timing': 1.2,  # Slightly higher weight
            'weather': 0.8,
            'synchronicity': 1.0,
            'user_resonance': 1.1
        }
        
        weighted_sum = 0.0
        total_weight = 0.0
        
        for method, score in scores.items():
            weight = weights.get(method, 1.0)
            weighted_sum += score * weight
            total_weight += weight
        
        return weighted_sum / total_weight if total_weight > 0 else 0.0

# ============================================================================
# STREAMLIT UI FOR PSI TRACKING
# ============================================================================

def render_psi_tracker_dashboard():
    """Render the empirical validation dashboard"""
    st.title("📊 Psi Tracker - Empirical Validation")
    st.markdown("### Track ALL Predictions Across ALL Psi Methods")
    
    st.info("""
    🔬 **Scientific Validation:**
    - Track predictions from ALL modules (stocks, prediction markets, numerology)
    - Measure actual accuracy vs predicted confidence
    - Identify which psi methods work best
    - Build empirical evidence for resonance field theory
    
    **Goal:** Prove psi methods provide informational edge through data!
    """)
    
    tracker = PsiTracker()
    
    # Overall stats
    st.subheader("📈 Overall Performance")
    
    stats = tracker.get_accuracy_stats()
    
    col1, col2, col3, col4 = st.columns(4)
    
    with col1:
        st.metric("Total Predictions", stats['total_predictions'])
    
    with col2:
        st.metric("Resolved", stats['resolved'])
    
    with col3:
        accuracy_pct = stats['accuracy'] * 100
        st.metric("Accuracy", f"{accuracy_pct:.1f}%")
    
    with col4:
        st.metric("Total Profit", f"${stats.get('total_profit', 0):.2f}")
    
    # Psi method performance
    if stats['resolved'] > 0:
        st.markdown("---")
        st.subheader("🔮 Psi Method Performance")
        
        method_stats = tracker.get_psi_method_performance()
        
        if method_stats:
            method_df = pd.DataFrame(method_stats).T
            method_df['accuracy_pct'] = method_df['accuracy'] * 100
            
            st.dataframe(
                method_df[['count', 'accuracy_pct', 'avg_score', 'correct', 'incorrect']],
                use_container_width=True
            )
            
            # Chart
            st.bar_chart(method_df['accuracy_pct'])
    
    # Calibration
    if stats['resolved'] > 5:  # Need at least 5 resolved
        st.markdown("---")
        st.subheader("🎯 Calibration Analysis")
        st.markdown("Are you overconfident or underconfident?")
        
        calibration_df = tracker.get_calibration_data()
        
        if not calibration_df.empty:
            st.line_chart(
                calibration_df.set_index('bin')[['predicted_confidence', 'actual_accuracy']]
            )
            
            st.dataframe(calibration_df, use_container_width=True)
    
    # Recent predictions
    st.markdown("---")
    st.subheader("📝 Recent Predictions")
    
    recent = tracker.get_recent_predictions(limit=10)
    
    for pred in recent:
        status_emoji = "✅" if pred['correct'] is True else "❌" if pred['correct'] is False else "⏳"
        
        with st.expander(f"{status_emoji} {pred['description']} ({pred['category']})"):
            col1, col2 = st.columns(2)
            
            with col1:
                st.markdown(f"**Prediction:** {pred['prediction']}")
                st.markdown(f"**Confidence:** {pred['confidence']*100:.0f}%")
                st.markdown(f"**Composite Score:** {pred['composite_score']:.2f}")
            
            with col2:
                st.markdown(f"**Psi Methods:** {', '.join(pred['psi_methods'])}")
                st.markdown(f"**Created:** {pred['created_at'][:10]}")
                
                if pred['correct'] is not None:
                    st.markdown(f"**Outcome:** {pred['outcome']}")
                    st.markdown(f"**Result:** {'✅ CORRECT' if pred['correct'] else '❌ INCORRECT'}")
                    
                    if pred['profit'] is not None:
                        profit_color = "green" if pred['profit'] > 0 else "red"
                        st.markdown(f"**Profit:** :{profit_color}[${pred['profit']:.2f}]")
    
    # Unresolved predictions
    st.markdown("---")
    st.subheader("⏳ Awaiting Resolution")
    
    unresolved = tracker.get_unresolved_predictions()
    
    if unresolved:
        st.markdown(f"**{len(unresolved)} predictions pending**")
        
        for pred in unresolved[:5]:
            st.markdown(f"- {pred['description']} (closes {pred['close_date'][:10]})")
    else:
        st.success("No pending predictions - make some predictions to test psi methods!")
    
    # Manual resolution interface
    st.markdown("---")
    st.subheader("✏️ Resolve Prediction")
    
    if unresolved:
        pred_id = st.selectbox(
            "Select Prediction",
            options=[p['id'] for p in unresolved],
            format_func=lambda x: next((p['description'] for p in unresolved if p['id'] == x), x)
        )
        
        if pred_id:  # Only show if valid selection
            outcome = st.text_input("Actual Outcome")
            correct = st.checkbox("Was prediction correct?")
            profit = st.number_input("Profit/Loss ($)", value=0.0)
            
            if st.button("✅ Mark as Resolved"):
                tracker.resolve_prediction(pred_id, outcome, correct, profit)
                st.success(f"Prediction {pred_id} resolved!")
                st.rerun()

if __name__ == "__main__":
    render_psi_tracker_dashboard()
