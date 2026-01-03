"""
Model Comparison Framework

Tests:
1. Individual model performance (Russell, PANAS, Frontal Asymmetry, TI-UOP)
2. Combined model performance (ensemble methods)
3. Coupling threshold analysis (0.6, 0.85 evidence)
"""

import numpy as np
from typing import List, Dict, Tuple
from sklearn.metrics import mean_absolute_error, r2_score, accuracy_score
from scipy.stats import pearsonr
import warnings

from emotion_models import (
    RussellCircumplexModel, PANASModel, FrontalAlphaAsymmetry,
    EmotionPrediction
)
from tiuop_adapter import TIUOPModel, TIUOPCouplingAnalyzer


class EnsembleModel:
    """
    Ensemble combining multiple emotion recognition models
    
    Methods:
    - Average: Simple average of predictions
    - Weighted: Confidence-weighted average
    - Stacking: Use one model's features as input to another
    """
    
    def __init__(self, models: List, method: str = 'weighted'):
        self.models = models
        self.method = method
        self.model_name = f"Ensemble-{method}"
    
    def predict(self, eeg: np.ndarray) -> EmotionPrediction:
        """Combine predictions from all models"""
        predictions = [model.predict(eeg) for model in self.models]
        
        if self.method == 'average':
            return self._average_ensemble(predictions)
        elif self.method == 'weighted':
            return self._weighted_ensemble(predictions)
        else:
            raise ValueError(f"Unknown method: {self.method}")
    
    def _average_ensemble(self, predictions: List[EmotionPrediction]) -> EmotionPrediction:
        """Simple average"""
        valence = np.mean([p.valence for p in predictions])
        arousal = np.mean([p.arousal for p in predictions])
        confidence = np.mean([p.confidence for p in predictions])
        
        return EmotionPrediction(
            valence=valence,
            arousal=arousal,
            confidence=confidence,
            model_name=self.model_name,
            raw_features={
                'individual_predictions': [
                    {
                        'model': p.model_name,
                        'valence': p.valence,
                        'arousal': p.arousal,
                        'confidence': p.confidence
                    }
                    for p in predictions
                ]
            }
        )
    
    def _weighted_ensemble(self, predictions: List[EmotionPrediction]) -> EmotionPrediction:
        """Confidence-weighted average"""
        weights = np.array([p.confidence for p in predictions])
        weights = weights / (np.sum(weights) + 1e-10)
        
        valence = np.sum([p.valence * w for p, w in zip(predictions, weights)])
        arousal = np.sum([p.arousal * w for p, w in zip(predictions, weights)])
        confidence = np.mean([p.confidence for p in predictions])
        
        return EmotionPrediction(
            valence=valence,
            arousal=arousal,
            confidence=confidence,
            model_name=self.model_name,
            raw_features={
                'weights': weights.tolist(),
                'individual_predictions': [
                    {
                        'model': p.model_name,
                        'valence': p.valence,
                        'arousal': p.arousal,
                        'confidence': p.confidence,
                        'weight': float(w)
                    }
                    for p, w in zip(predictions, weights)
                ]
            }
        )


class ModelComparison:
    """
    Compare emotion recognition models on DEAP dataset
    
    Tests:
    1. Prediction accuracy (vs ground truth labels)
    2. Correlation with human ratings
    3. Individual vs ensemble performance
    """
    
    def __init__(self):
        self.models = {
            'russell': RussellCircumplexModel(),
            'panas': PANASModel(),
            'frontal_asymmetry': FrontalAlphaAsymmetry(),
            'tiuop': TIUOPModel()
        }
        
        # Create ensemble models
        all_models = list(self.models.values())
        self.models['ensemble_all_avg'] = EnsembleModel(all_models, 'average')
        self.models['ensemble_all_weighted'] = EnsembleModel(all_models, 'weighted')
        
        # Validated + TI-UOP ensemble
        validated = [self.models['russell'], self.models['panas'], 
                    self.models['frontal_asymmetry'], self.models['tiuop']]
        self.models['ensemble_tiuop_weighted'] = EnsembleModel(validated, 'weighted')
    
    def evaluate_on_trials(
        self,
        eeg_trials: np.ndarray,
        labels: np.ndarray,
        valence_threshold: float = 5.0
    ) -> Dict:
        """
        Evaluate all models on a set of trials
        
        Args:
            eeg_trials: (n_trials, 32, timepoints)
            labels: (n_trials, 4) - valence, arousal, dominance, liking
            valence_threshold: Threshold for binary classification
            
        Returns:
            Comprehensive performance metrics
        """
        n_trials = len(eeg_trials)
        
        # Ground truth (normalized to 0-1)
        gt_valence = (labels[:, 0] - 1) / 8  # 1-9 scale to 0-1
        gt_arousal = (labels[:, 1] - 1) / 8
        
        # Binary labels (high/low)
        gt_valence_binary = (labels[:, 0] >= valence_threshold).astype(int)
        gt_arousal_binary = (labels[:, 1] >= valence_threshold).astype(int)
        
        results = {}
        
        for model_name, model in self.models.items():
            print(f"Evaluating {model_name}...")
            
            pred_valence = []
            pred_arousal = []
            confidences = []
            
            for i in range(n_trials):
                try:
                    prediction = model.predict(eeg_trials[i])
                    pred_valence.append(prediction.valence)
                    pred_arousal.append(prediction.arousal)
                    confidences.append(prediction.confidence)
                except Exception as e:
                    warnings.warn(f"Error in {model_name} trial {i}: {e}")
                    pred_valence.append(0.5)
                    pred_arousal.append(0.5)
                    confidences.append(0.0)
            
            pred_valence = np.array(pred_valence)
            pred_arousal = np.array(pred_arousal)
            
            # Binary predictions
            pred_valence_binary = (pred_valence >= 0.5).astype(int)
            pred_arousal_binary = (pred_arousal >= 0.5).astype(int)
            
            # Compute metrics
            results[model_name] = {
                'valence': {
                    'mae': float(mean_absolute_error(gt_valence, pred_valence)),
                    'correlation': float(pearsonr(gt_valence, pred_valence)[0]),
                    'r2': float(r2_score(gt_valence, pred_valence)),
                    'accuracy_binary': float(accuracy_score(gt_valence_binary, pred_valence_binary))
                },
                'arousal': {
                    'mae': float(mean_absolute_error(gt_arousal, pred_arousal)),
                    'correlation': float(pearsonr(gt_arousal, pred_arousal)[0]),
                    'r2': float(r2_score(gt_arousal, pred_arousal)),
                    'accuracy_binary': float(accuracy_score(gt_arousal_binary, pred_arousal_binary))
                },
                'mean_confidence': float(np.mean(confidences))
            }
        
        # Compute improvement metrics (ensemble vs best individual)
        individual_models = ['russell', 'panas', 'frontal_asymmetry', 'tiuop']
        
        best_val_corr = max([
            results[m]['valence']['correlation'] 
            for m in individual_models
        ])
        
        ensemble_val_corr = results['ensemble_all_weighted']['valence']['correlation']
        
        results['summary'] = {
            'best_individual_valence_corr': float(best_val_corr),
            'ensemble_valence_corr': float(ensemble_val_corr),
            'ensemble_improvement': float(ensemble_val_corr - best_val_corr),
            'ensemble_better': ensemble_val_corr > best_val_corr
        }
        
        return results


class CouplingThresholdAnalysis:
    """
    Analyze evidence for natural coupling at 0.6 and 0.85 thresholds
    
    Tests:
    1. Distribution of LCC values across trial pairs
    2. Clustering around 0.6 and 0.85
    3. Regime transitions
    """
    
    def __init__(self):
        self.analyzer = TIUOPCouplingAnalyzer()
    
    def analyze_trial_pairs(
        self,
        eeg_trials: np.ndarray,
        n_samples: int = 200
    ) -> Dict:
        """
        Analyze coupling across pairs of trials
        
        Args:
            eeg_trials: (n_trials, 32, timepoints)
            n_samples: Number of random pairs to sample
            
        Returns:
            Analysis results including threshold evidence
        """
        n_trials = len(eeg_trials)
        
        lcc_values = []
        
        for _ in range(n_samples):
            i, j = np.random.choice(n_trials, 2, replace=False)
            
            try:
                result = self.analyzer.analyze_coupling(
                    eeg_trials[i], 
                    eeg_trials[j]
                )
                lcc_values.append(result['lcc'])
            except Exception as e:
                warnings.warn(f"Error computing LCC: {e}")
        
        lcc_values = np.array(lcc_values)
        
        # Histogram analysis
        hist, bin_edges = np.histogram(lcc_values, bins=20, range=(-1, 1))
        
        # Find peaks near 0.6 and 0.85
        bin_centers = (bin_edges[:-1] + bin_edges[1:]) / 2
        
        # Look for local maxima
        peaks = []
        for i in range(1, len(hist) - 1):
            if hist[i] > hist[i-1] and hist[i] > hist[i+1]:
                peaks.append({
                    'center': float(bin_centers[i]),
                    'count': int(hist[i]),
                    'percentage': float(hist[i] / len(lcc_values) * 100)
                })
        
        # Check if peaks near 0.6 and 0.85 exist
        near_0_6 = [p for p in peaks if 0.5 < p['center'] < 0.7]
        near_0_85 = [p for p in peaks if 0.8 < p['center'] < 0.9]
        
        return {
            'lcc_values': lcc_values.tolist(),
            'statistics': {
                'mean': float(np.mean(lcc_values)),
                'std': float(np.std(lcc_values)),
                'median': float(np.median(lcc_values)),
                'min': float(np.min(lcc_values)),
                'max': float(np.max(lcc_values))
            },
            'histogram': {
                'counts': hist.tolist(),
                'bin_edges': bin_edges.tolist(),
                'bin_centers': bin_centers.tolist()
            },
            'peaks': peaks,
            'threshold_evidence': {
                'peak_near_0.6': len(near_0_6) > 0,
                'peak_near_0.85': len(near_0_85) > 0,
                'peaks_0.6': near_0_6,
                'peaks_0.85': near_0_85
            },
            'regime_distribution': {
                'below_0.6': float(np.mean(lcc_values < 0.6) * 100),
                'in_0.6_0.85': float(np.mean(
                    (lcc_values >= 0.6) & (lcc_values <= 0.85)
                ) * 100),
                'above_0.85': float(np.mean(lcc_values > 0.85) * 100)
            },
            'n_samples': n_samples
        }
    
    def test_threshold_significance(
        self,
        eeg_trials: np.ndarray,
        labels: np.ndarray,
        n_samples: int = 100
    ) -> Dict:
        """
        Test if coupling strength correlates with emotional similarity
        
        Hypothesis: Trials with similar emotions should have higher LCC
        """
        n_trials = len(eeg_trials)
        
        high_sim_lcc = []  # Similar emotional states
        low_sim_lcc = []   # Different emotional states
        
        for _ in range(n_samples):
            i, j = np.random.choice(n_trials, 2, replace=False)
            
            # Compute emotional distance
            val_dist = abs(labels[i, 0] - labels[j, 0])
            aro_dist = abs(labels[i, 1] - labels[j, 1])
            emotion_dist = np.sqrt(val_dist**2 + aro_dist**2)
            
            try:
                result = self.analyzer.analyze_coupling(
                    eeg_trials[i], 
                    eeg_trials[j]
                )
                lcc = result['lcc']
                
                if emotion_dist < 2.0:  # Similar emotions
                    high_sim_lcc.append(lcc)
                elif emotion_dist > 5.0:  # Different emotions
                    low_sim_lcc.append(lcc)
            except Exception:
                pass
        
        if len(high_sim_lcc) > 0 and len(low_sim_lcc) > 0:
            from scipy.stats import ttest_ind
            t_stat, p_value = ttest_ind(high_sim_lcc, low_sim_lcc)
            
            return {
                'similar_emotions': {
                    'mean_lcc': float(np.mean(high_sim_lcc)),
                    'std_lcc': float(np.std(high_sim_lcc)),
                    'n': len(high_sim_lcc)
                },
                'different_emotions': {
                    'mean_lcc': float(np.mean(low_sim_lcc)),
                    'std_lcc': float(np.std(low_sim_lcc)),
                    'n': len(low_sim_lcc)
                },
                'statistical_test': {
                    't_statistic': float(t_stat),
                    'p_value': float(p_value),
                    'significant': p_value < 0.05
                },
                'interpretation': (
                    "Higher LCC for similar emotions" 
                    if np.mean(high_sim_lcc) > np.mean(low_sim_lcc)
                    else "No clear relationship"
                )
            }
        else:
            return {
                'error': 'Insufficient samples',
                'similar_emotions': {'n': len(high_sim_lcc)},
                'different_emotions': {'n': len(low_sim_lcc)}
            }


if __name__ == '__main__':
    print("Model Comparison Framework\n")
    
    # Test with synthetic data
    np.random.seed(42)
    n_trials = 20
    eeg_trials = np.random.randn(n_trials, 32, 7680) * 10  # After baseline removal
    labels = np.random.uniform(1, 9, size=(n_trials, 4))
    
    # Test model comparison
    comparison = ModelComparison()
    results = comparison.evaluate_on_trials(eeg_trials, labels)
    
    print("Model Performance (Valence Correlation):")
    for model_name, metrics in results.items():
        if model_name != 'summary':
            corr = metrics['valence']['correlation']
            print(f"  {model_name}: {corr:.3f}")
    
    print(f"\nEnsemble Improvement: {results['summary']['ensemble_improvement']:.3f}")
    
    # Test coupling analysis
    print("\n" + "="*60)
    print("Coupling Threshold Analysis\n")
    
    coupling_analysis = CouplingThresholdAnalysis()
    coupling_results = coupling_analysis.analyze_trial_pairs(eeg_trials, n_samples=50)
    
    print(f"LCC Statistics:")
    print(f"  Mean: {coupling_results['statistics']['mean']:.3f}")
    print(f"  Std: {coupling_results['statistics']['std']:.3f}")
    
    print(f"\nRegime Distribution:")
    for regime, pct in coupling_results['regime_distribution'].items():
        print(f"  {regime}: {pct:.1f}%")
    
    threshold_ev = coupling_results['threshold_evidence']
    print(f"\nPeak near 0.6: {threshold_ev['peak_near_0.6']}")
    print(f"Peak near 0.85: {threshold_ev['peak_near_0.85']}")
