"""
Rigorous PSI Testing Framework
Empirical validation with blind testing, error bars, and falsifiable predictions

Core capabilities:
1. Blind predictions from minimal/unrelated content
2. Statistical error bars and confidence intervals  
3. Clair abilities measurement (clairvoyance, clairaudience, etc)
4. Hardware/software limitation analysis
5. Per-problem accuracy bounds (>95% overall target)
6. Election and historical fact predictions
"""

import streamlit as st
from datetime import datetime, timedelta
from typing import Dict, Any, List, Optional, Tuple
import numpy as np
from scipy import stats
import json
from db_utils import db
import random


class BlindPredictionEngine:
    """
    Generate predictions from minimal, unrelated content
    Maximum blinding to test pure PSI capability
    """
    
    def __init__(self):
        self.prediction_types = [
            "Election Result",
            "Historical Fact",
            "Future Event",
            "Hidden Information",
            "Random Number",
            "Coin Flip Sequence"
        ]
    
    def get_all_predictions(self) -> List[Dict[str, Any]]:
        """Get all blind predictions from database"""
        assets = db.search_assets("asset_type = 'blind_prediction'")
        predictions = []
        for asset in assets:
            content = asset.get('content', {})
            content['asset_id'] = asset.get('asset_id')
            predictions.append(content)
        return predictions
    
    def get_pending_predictions(self) -> List[Dict[str, Any]]:
        """Get predictions awaiting validation"""
        all_preds = self.get_all_predictions()
        
        # Get all validation records to check which predictions are validated
        validation_assets = db.search_assets("asset_type = 'psi_validation'")
        validated_ids = {
            v.get('content', {}).get('prediction_id')
            for v in validation_assets
        }
        
        # Return only predictions that don't have validations
        return [
            p for p in all_preds
            if p.get('status') == 'pending_validation'
            and p.get('prediction_id') not in validated_ids
        ]
    
    def get_validated_predictions(self) -> List[Dict[str, Any]]:
        """Get all validated predictions"""
        all_preds = self.get_all_predictions()
        
        # Get all validation records to check which predictions are validated
        validation_assets = db.search_assets("asset_type = 'psi_validation'")
        validated_ids = {
            v.get('content', {}).get('prediction_id')
            for v in validation_assets
        }
        
        # Return only predictions that have validations
        return [
            p for p in all_preds
            if p.get('prediction_id') in validated_ids
        ]
    
    def create_blind_prediction(
        self,
        minimal_content: str,
        prediction_type: str,
        target: str,
        predicted_outcome: str
    ) -> Dict[str, Any]:
        """
        Create prediction from minimal content with maximum blinding
        
        Args:
            minimal_content: Unrelated seed content (1-3 words)
            prediction_type: Type of prediction
            target: What to predict (kept separate for blinding)
            predicted_outcome: Your actual prediction
            
        Returns:
            Prediction with metadata for validation
        """
        
        prediction_id = f"blind_{datetime.now().strftime('%Y%m%d_%H%M%S_%f')}"
        
        prediction = {
            'prediction_id': prediction_id,
            'type': prediction_type,
            'minimal_content': minimal_content,
            'target': target,
            'predicted_outcome': predicted_outcome,
            'timestamp': datetime.now().isoformat(),
            'blinding_level': 'maximum',
            'method': 'psi_resonance',
            'status': 'pending_validation'
        }
        
        # Store in database
        db.add_asset(
            asset_type='blind_prediction',
            source_app='Rigorous PSI Testing',
            title=f"Blind: {target}",
            content=prediction,
            tags=['psi', 'rigorous', 'blind', prediction_type.lower().replace(' ', '_')]
        )
        
        return prediction
    
    def validate_prediction(
        self,
        prediction_id: str,
        actual_outcome: str,
        notes: str = ""
    ) -> Dict[str, Any]:
        """
        Validate prediction against actual outcome
        
        Returns:
            Validation result with accuracy metrics
        """
        
        # Retrieve prediction from database
        assets = db.search_assets("asset_type = 'blind_prediction'")
        prediction_asset = None
        
        for asset in assets:
            content = asset.get('content', {})
            if content.get('prediction_id') == prediction_id:
                prediction_asset = asset
                break
        
        if not prediction_asset:
            return {'error': f'Prediction {prediction_id} not found'}
        
        prediction = prediction_asset.get('content', {})
        predicted = prediction.get('predicted_outcome', '').strip().lower()
        actual = actual_outcome.strip().lower()
        
        # Simple binary accuracy (correct/incorrect)
        is_correct = predicted == actual
        accuracy = 1.0 if is_correct else 0.0
        
        # PSI score (deviation from chance, assuming binary)
        chance = 0.5
        psi_score = abs(accuracy - chance)
        
        validation = {
            'prediction_id': prediction_id,
            'predicted_outcome': prediction.get('predicted_outcome'),
            'actual_outcome': actual_outcome,
            'is_correct': is_correct,
            'accuracy': accuracy,
            'validated_at': datetime.now().isoformat(),
            'psi_score': psi_score,
            'notes': notes,
            'prediction_type': prediction.get('type'),
            'target': prediction.get('target')
        }
        
        # Save validation as a separate asset for tracking
        db.add_asset(
            asset_type='psi_validation',
            source_app='Rigorous PSI Testing',
            title=f"Validation: {prediction.get('target')}",
            content=validation,
            tags=['validation', 'psi', 'rigorous']
        )
        
        return validation


class PSIErrorBarCalculator:
    """
    Calculate provable PSI error bars and confidence intervals
    Statistical rigor for all predictions
    """
    
    @staticmethod
    def get_all_validations() -> List[Dict[str, Any]]:
        """Get all validation records from database"""
        assets = db.search_assets("asset_type = 'psi_validation'")
        validations = []
        for asset in assets:
            content = asset.get('content', {})
            validations.append(content)
        return validations
    
    @staticmethod
    def calculate_error_bars(
        validations: Optional[List[Dict[str, Any]]] = None,
        confidence_level: float = 0.95
    ) -> Dict[str, Any]:
        """
        Calculate error bars for prediction accuracy
        
        Args:
            validations: List of validation records (if None, fetches from DB)
            confidence_level: Confidence interval (0.95 = 95%)
            
        Returns:
            Error bar statistics
        """
        
        # Get validations from DB if not provided
        if validations is None:
            validations = PSIErrorBarCalculator.get_all_validations()
        
        if not validations:
            return {
                'error': 'No validations to analyze',
                'n': 0
            }
        
        # Extract accuracy scores
        accuracies = []
        for val in validations:
            acc = val.get('accuracy', 0)
            accuracies.append(acc)
        
        if not accuracies:
            return {
                'error': 'No validated predictions',
                'n': 0
            }
        
        # Statistical calculations
        n = len(accuracies)
        mean_acc = np.mean(accuracies)
        
        # Guard against small sample sizes
        if n < 2:
            # With only 1 sample, we can't calculate std dev or CI
            return {
                'n_predictions': n,
                'mean_accuracy': mean_acc,
                'std_dev': 0.0,
                'std_error': 0.0,
                'confidence_level': confidence_level,
                'confidence_interval': (mean_acc, mean_acc),
                'margin_of_error': 0.0,
                'z_score': 0.0,
                'p_value': 1.0,
                'cohens_d': 0.0,
                'significance': 'insufficient_data',
                'psi_evidence': 'need_more_data',
                'chance_baseline': 0.50,
                'warning': 'Need at least 2 validations for statistical analysis'
            }
        
        std_acc = np.std(accuracies, ddof=1)
        sem = std_acc / np.sqrt(n)
        
        # Confidence interval (t-distribution)
        df = n - 1
        t_critical = stats.t.ppf((1 + confidence_level) / 2, df)
        margin_of_error = t_critical * sem
        
        ci_lower = mean_acc - margin_of_error
        ci_upper = mean_acc + margin_of_error
        
        # Calculate PSI significance (vs random chance)
        # For binary predictions, chance = 50%
        baseline = 0.50
        z_score = (mean_acc - baseline) / sem if sem > 0 else 0
        p_value = 2 * (1 - stats.norm.cdf(abs(z_score)))
        
        # Effect size (Cohen's d)
        cohens_d = (mean_acc - baseline) / std_acc if std_acc > 0 else 0
        
        return {
            'n_predictions': n,
            'mean_accuracy': mean_acc,
            'std_dev': std_acc,
            'std_error': sem,
            'confidence_level': confidence_level,
            'confidence_interval': (ci_lower, ci_upper),
            'margin_of_error': margin_of_error,
            'z_score': z_score,
            'p_value': p_value,
            'cohens_d': cohens_d,
            'significance': 'significant' if p_value < 0.05 else 'not_significant',
            'psi_evidence': 'strong' if p_value < 0.001 else 'moderate' if p_value < 0.05 else 'weak',
            'chance_baseline': baseline
        }
    
    @staticmethod
    def calculate_per_problem_bounds() -> Dict[str, Dict[str, float]]:
        """
        Calculate accuracy bounds for each problem type
        Groups all validations by prediction_type and calculates statistics
        
        Returns:
            Dictionary mapping prediction type to accuracy statistics
        """
        
        validations = PSIErrorBarCalculator.get_all_validations()
        
        if not validations:
            return {}
        
        by_type = {}
        for val in validations:
            pred_type = val.get('prediction_type', 'Unknown')
            if pred_type not in by_type:
                by_type[pred_type] = []
            by_type[pred_type].append(val)
        
        bounds = {}
        
        for problem_type, type_validations in by_type.items():
            accuracies = [v.get('accuracy', 0) for v in type_validations]
            
            if accuracies and len(accuracies) > 0:
                mean = np.mean(accuracies)
                n = len(accuracies)
                
                if n > 1:
                    std = np.std(accuracies, ddof=1)
                    sem = std / np.sqrt(n)
                    t_crit = stats.t.ppf(0.975, n - 1)
                    margin = t_crit * sem
                else:
                    std = 0.0
                    sem = 0.0
                    margin = 0.0
                
                correct_count = sum(1 for a in accuracies if a == 1.0)
                
                bounds[problem_type] = {
                    'lower_bound': max(0, mean - margin),
                    'upper_bound': min(1, mean + margin),
                    'mean_accuracy': mean,
                    'std_dev': std,
                    'margin_of_error': margin,
                    'n_samples': n,
                    'correct_count': correct_count,
                    'incorrect_count': n - correct_count,
                    'meets_95_target': mean >= 0.95
                }
        
        return bounds


class ClairAbilitiesFramework:
    """
    Measure and track specific "clair" abilities
    Scientific measurement of paranormal capabilities
    """
    
    def __init__(self):
        self.clair_types = {
            'clairvoyance': 'Clear seeing - visual information',
            'clairaudience': 'Clear hearing - auditory information',
            'clairsentience': 'Clear feeling - emotional/physical sensing',
            'claircognizance': 'Clear knowing - direct knowledge',
            'clairalience': 'Clear smelling - olfactory information',
            'clairgustance': 'Clear tasting - gustatory information',
            'clairtangency': 'Clear touching - psychometry'
        }
    
    def test_clair_ability(
        self,
        ability_type: str,
        test_protocol: str,
        trials: int = 100
    ) -> Dict[str, Any]:
        """
        Test specific clair ability with controlled protocol
        
        Args:
            ability_type: Type of clair ability
            test_protocol: Experimental protocol description
            trials: Number of trials
            
        Returns:
            Test results with accuracy and significance
        """
        
        test_result = {
            'ability': ability_type,
            'description': self.clair_types.get(ability_type, 'Unknown'),
            'protocol': test_protocol,
            'n_trials': trials,
            'timestamp': datetime.now().isoformat(),
            'results': {
                'accuracy': None,
                'hits': None,
                'misses': None,
                'confidence_interval': None,
                'p_value': None,
                'effect_size': None
            }
        }
        
        return test_result
    
    def measure_all_clairs(self) -> Dict[str, Dict[str, float]]:
        """
        Comprehensive measurement of all clair abilities
        
        Returns:
            Accuracy scores for each clair type
        """
        
        results = {}
        
        for clair_type in self.clair_types.keys():
            results[clair_type] = {
                'accuracy': 0.0,  # Placeholder
                'confidence': 0.0,
                'trials_completed': 0,
                'status': 'pending'
            }
        
        return results


class LimitationAnalyzer:
    """
    Identify hardware, software, and logical limitations
    Determine what's holding back PSI prediction accuracy
    """
    
    def __init__(self):
        self.limitation_categories = [
            'Hardware',
            'Software',
            'Logic/Assumptions',
            'Classical vs Quantum',
            'Binary vs Ternary',
            'Material Constraints',
            'Theoretical Framework'
        ]
    
    def analyze_limitations(
        self,
        current_accuracy: float,
        target_accuracy: float = 0.95
    ) -> Dict[str, Any]:
        """
        Analyze what's preventing achievement of target accuracy
        
        Args:
            current_accuracy: Current prediction accuracy
            target_accuracy: Desired accuracy (default 95%)
            
        Returns:
            Limitation analysis with recommendations
        """
        
        accuracy_gap = target_accuracy - current_accuracy
        
        analysis = {
            'current_accuracy': current_accuracy,
            'target_accuracy': target_accuracy,
            'accuracy_gap': accuracy_gap,
            'gap_percentage': (accuracy_gap / target_accuracy) * 100,
            'timestamp': datetime.now().isoformat(),
            'limiting_factors': []
        }
        
        # Analyze each category
        limitations = []
        
        if current_accuracy < 0.60:
            limitations.append({
                'category': 'Hardware',
                'factor': 'Binary transistors limiting quantum coherence',
                'impact': 'high',
                'recommendation': 'Transition to ternary/tralse computing for Φ/Ψ state support',
                'theoretical_improvement': '+15-20% accuracy'
            })
            limitations.append({
                'category': 'Software',
                'factor': 'Classical probability models (Bayesian inference)',
                'impact': 'high',
                'recommendation': 'Implement Probability as Resonance Field (PRF) theory',
                'theoretical_improvement': '+10-15% accuracy'
            })
        
        if current_accuracy < 0.75:
            limitations.append({
                'category': 'Logic/Assumptions',
                'factor': 'Binary true/false logic',
                'impact': 'medium',
                'recommendation': 'Adopt tralse quadruplet logic (T, F, Φ, Ψ)',
                'theoretical_improvement': '+8-12% accuracy'
            })
            limitations.append({
                'category': 'Classical vs Quantum',
                'factor': 'Classical computing cannot access quantum coherence',
                'impact': 'high',
                'recommendation': 'Quantum-classical hybrid system with consciousness coupling',
                'theoretical_improvement': '+12-18% accuracy'
            })
        
        if current_accuracy < 0.85:
            limitations.append({
                'category': 'Theoretical Framework',
                'factor': 'Independent probability assumption',
                'impact': 'medium',
                'recommendation': 'CCC resonance field model (all events entangled)',
                'theoretical_improvement': '+5-10% accuracy'
            })
        
        if current_accuracy < 0.95:
            limitations.append({
                'category': 'Material Constraints',
                'factor': 'Silicon-based computing vs consciousness substrate',
                'impact': 'medium',
                'recommendation': 'Biophoton-sensitive materials for i-cell coupling',
                'theoretical_improvement': '+3-8% accuracy'
            })
        
        analysis['limiting_factors'] = limitations
        analysis['estimated_max_accuracy'] = min(0.99, current_accuracy + sum([
            float(lim['theoretical_improvement'].split('+')[1].split('-')[1].replace('% accuracy', '')) / 100
            for lim in limitations
        ]))
        
        return analysis
    
    def recommend_upgrades(
        self,
        limitations: List[Dict[str, Any]]
    ) -> List[Dict[str, Any]]:
        """
        Prioritized recommendations to overcome limitations
        
        Returns:
            Ordered list of recommended upgrades
        """
        
        # Sort by impact and theoretical improvement
        impact_order = {'high': 3, 'medium': 2, 'low': 1}
        
        sorted_limits = sorted(
            limitations,
            key=lambda x: impact_order.get(x.get('impact', 'low'), 0),
            reverse=True
        )
        
        recommendations = []
        for i, lim in enumerate(sorted_limits, 1):
            recommendations.append({
                'priority': i,
                'category': lim['category'],
                'upgrade': lim['recommendation'],
                'expected_gain': lim['theoretical_improvement'],
                'implementation_difficulty': 'high' if i <= 2 else 'medium'
            })
        
        return recommendations


class ElectionPredictor:
    """
    Predict election results from minimal content
    Falsifiable predictions with statistical rigor
    """
    
    def predict_election(
        self,
        election_name: str,
        minimal_seed: str,
        candidates: List[str],
        coherence_level: float = 0.91
    ) -> Dict[str, Any]:
        """
        Predict election outcome from minimal unrelated content
        
        Args:
            election_name: Name of election
            minimal_seed: 1-3 unrelated words as seed
            candidates: List of candidates
            coherence_level: Coherence at prediction time
            
        Returns:
            Prediction with confidence intervals
        """
        
        # Use sacred number patterns + coherence for prediction
        # (Simplified - real implementation would use God Machine)
        
        prediction = {
            'election': election_name,
            'seed_content': minimal_seed,
            'candidates': candidates,
            'predicted_winner': None,  # To be filled by PSI process
            'probability_distribution': {},  # Prob for each candidate
            'coherence_at_prediction': coherence_level,
            'confidence_interval': (0.0, 1.0),
            'timestamp': datetime.now().isoformat(),
            'validation_date': None,  # When results known
            'falsifiable': True,
            'blinding_level': 'maximum'
        }
        
        return prediction


class HistoricalFactValidator:
    """
    Validate historical facts from minimal content
    Test God Machine on known historical truths
    """
    
    def validate_historical_fact(
        self,
        question: str,
        minimal_seed: str,
        known_answer: Optional[str] = None
    ) -> Dict[str, Any]:
        """
        Predict/validate historical fact from minimal content
        
        Args:
            question: Historical question
            minimal_seed: Unrelated seed content
            known_answer: Actual answer (for validation)
            
        Returns:
            Prediction/validation result
        """
        
        validation = {
            'question': question,
            'seed_content': minimal_seed,
            'predicted_answer': None,  # From PSI
            'actual_answer': known_answer,
            'accuracy': None,
            'confidence': None,
            'timestamp': datetime.now().isoformat(),
            'method': 'minimal_content_psi',
            'falsifiable': True if known_answer else False
        }
        
        return validation


class RigorousPSIManager:
    """
    Centralized management of rigorous PSI testing
    Integrates all components for comprehensive empirical validation
    """
    
    def __init__(self):
        self.blind_engine = BlindPredictionEngine()
        self.error_calculator = PSIErrorBarCalculator()
        self.clair_framework = ClairAbilitiesFramework()
        self.limitation_analyzer = LimitationAnalyzer()
        self.election_predictor = ElectionPredictor()
        self.historical_validator = HistoricalFactValidator()
    
    def run_comprehensive_test(
        self,
        test_type: str,
        n_trials: int = 100
    ) -> Dict[str, Any]:
        """
        Run comprehensive PSI test with full statistical analysis
        
        Args:
            test_type: Type of test to run
            n_trials: Number of trials
            
        Returns:
            Complete test results with error bars, limitations, recommendations
        """
        
        test_result = {
            'test_type': test_type,
            'n_trials': n_trials,
            'timestamp': datetime.now().isoformat(),
            'predictions': [],
            'error_bars': None,
            'clair_abilities': None,
            'limitations': None,
            'recommendations': None,
            'overall_accuracy': None,
            'target_met': False
        }
        
        # Run test and collect results
        # (Implementation would depend on test type)
        
        return test_result
    
    def get_overall_accuracy(self) -> Dict[str, Any]:
        """
        Calculate overall accuracy across all prediction types
        Target: >95%
        
        Returns:
            Overall accuracy metrics
        """
        
        try:
            validations = self.error_calculator.get_all_validations()
            
            if not validations:
                return {
                    'overall_accuracy': 0.0,
                    'n_predictions': 0,
                    'target_accuracy': 0.95,
                    'target_met': False,
                    'gap_to_target': 0.95
                }
            
            error_bars = self.error_calculator.calculate_error_bars(validations)
            
            overall = {
                'overall_accuracy': error_bars.get('mean_accuracy', 0.0),
                'n_predictions': error_bars.get('n_predictions', 0),
                'confidence_interval': error_bars.get('confidence_interval', (0, 0)),
                'p_value': error_bars.get('p_value', 1.0),
                'target_accuracy': 0.95,
                'target_met': error_bars.get('mean_accuracy', 0.0) >= 0.95,
                'gap_to_target': max(0, 0.95 - error_bars.get('mean_accuracy', 0.0))
            }
            
            return overall
            
        except Exception as e:
            return {
                'error': str(e),
                'overall_accuracy': 0.0,
                'n_predictions': 0,
                'target_met': False,
                'gap_to_target': 0.95
            }


# Global instance
_rigorous_psi_manager = None

def get_rigorous_psi_manager() -> RigorousPSIManager:
    """Get global rigorous PSI manager instance"""
    global _rigorous_psi_manager
    if _rigorous_psi_manager is None:
        _rigorous_psi_manager = RigorousPSIManager()
    return _rigorous_psi_manager
