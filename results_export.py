"""
Results Export Utility for Validation Dashboard

Provides JSON export of validation results
"""

import json
from datetime import datetime
from typing import Dict, Any


def export_validation_results(
    model_results: Dict[str, Any] | None = None,
    coupling_results: Dict[str, Any] | None = None
) -> str:
    """
    Export validation results to JSON format
    
    Args:
        model_results: Model comparison results
        coupling_results: Coupling threshold analysis results
        
    Returns:
        JSON string ready for download
    """
    export_data = {
        'export_timestamp': datetime.now().isoformat(),
        'experiment_type': [],
        'results': {}
    }
    
    if model_results:
        export_data['experiment_type'].append('model_comparison')
        # Convert numpy arrays to lists for JSON serialization
        export_data['results']['model_comparison'] = serialize_model_results(model_results)
    
    if coupling_results:
        export_data['experiment_type'].append('coupling_threshold_analysis')
        export_data['results']['coupling_analysis'] = serialize_coupling_results(coupling_results)
    
    return json.dumps(export_data, indent=2)


def serialize_model_results(results: Dict[str, Any]) -> Dict[str, Any]:
    """Serialize model results for JSON export"""
    serialized = {}
    
    for model_name, metrics in results.items():
        if model_name == 'summary':
            serialized[model_name] = metrics
        else:
            serialized[model_name] = {
                'valence': {
                    'correlation': float(metrics['valence'].get('correlation', 0)),
                    'p_value': float(metrics['valence'].get('p_value', 1.0)),
                    'mae': float(metrics['valence'].get('mae', 0)),
                    'r2': float(metrics['valence'].get('r2', 0)),
                    'binary_accuracy': float(metrics['valence'].get('binary_accuracy', 0))
                },
                'arousal': {
                    'correlation': float(metrics['arousal'].get('correlation', 0)),
                    'p_value': float(metrics['arousal'].get('p_value', 1.0)),
                    'mae': float(metrics['arousal'].get('mae', 0)),
                    'r2': float(metrics['arousal'].get('r2', 0)),
                    'binary_accuracy': float(metrics['arousal'].get('binary_accuracy', 0))
                },
                'mean_confidence': float(metrics.get('mean_confidence', 0))
            }
    
    return serialized


def serialize_coupling_results(results: Dict[str, Any]) -> Dict[str, Any]:
    """Serialize coupling results for JSON export"""
    import numpy as np
    
    return {
        'statistics': {
            'mean': float(results['statistics']['mean']),
            'std': float(results['statistics']['std']),
            'median': float(results['statistics']['median']),
            'min': float(results['statistics']['min']),
            'max': float(results['statistics']['max'])
        },
        'regime_distribution': {
            'below_0.6': float(results['regime_distribution']['below_0.6']),
            'in_0.6_0.85': float(results['regime_distribution']['in_0.6_0.85']),
            'above_0.85': float(results['regime_distribution']['above_0.85'])
        },
        'threshold_evidence': {
            'peak_near_0.6': bool(results['threshold_evidence']['peak_near_0.6']),
            'peak_near_0.85': bool(results['threshold_evidence']['peak_near_0.85']),
            'peaks_0.6': results['threshold_evidence']['peaks_0.6'],
            'peaks_0.85': results['threshold_evidence']['peaks_0.85']
        },
        'n_samples': int(results['n_samples'])
    }


def interpret_validation_results(
    model_results: Dict[str, Any] | None = None,
    coupling_results: Dict[str, Any] | None = None
) -> str:
    """
    Generate scientific interpretation of validation results
    
    Returns:
        Markdown-formatted interpretation
    """
    interpretation = "# 🎓 Scientific Interpretation\n\n"
    
    if model_results:
        interpretation += "## Model Performance Analysis\n\n"
        
        summary = model_results.get('summary', {})
        best_corr = summary.get('best_individual_valence_corr', 0)
        ensemble_corr = summary.get('ensemble_valence_corr', 0)
        improvement = summary.get('ensemble_improvement', 0)
        
        # Interpret correlation strength
        if best_corr < 0.3:
            interpretation += "⚠️ **Weak Performance**: Individual models show weak correlation (< 0.3) with ground truth. This suggests:\n"
            interpretation += "- Models may not capture the emotional dimensions well\n"
            interpretation += "- Dataset may be too noisy or limited\n"
            interpretation += "- Feature extraction may need refinement\n\n"
        elif best_corr < 0.5:
            interpretation += "📊 **Moderate Performance**: Models show moderate correlation (0.3-0.5), which is typical for emotion recognition. This suggests:\n"
            interpretation += "- Models capture some emotional variance\n"
            interpretation += "- Results are consistent with published EEG emotion research\n"
            interpretation += "- Room for improvement through ensemble or feature engineering\n\n"
        else:
            interpretation += "✅ **Strong Performance**: Models show strong correlation (> 0.5), exceeding typical benchmarks. This suggests:\n"
            interpretation += "- Models effectively capture emotional states\n"
            interpretation += "- Feature extraction is well-calibrated\n"
            interpretation += "- Results are promising for further validation\n\n"
        
        # Interpret ensemble
        if improvement > 0.05:
            interpretation += f"🎯 **Ensemble Benefit**: Combining models improves performance by {improvement:.3f}. This indicates:\n"
            interpretation += "- Individual models capture complementary information\n"
            interpretation += "- TI-UOP may add unique value when combined with validated models\n"
            interpretation += "- Ensemble approach is recommended for this application\n\n"
        elif improvement > -0.05:
            interpretation += f"📊 **Neutral Ensemble**: Ensemble shows minimal change ({improvement:+.3f}). This suggests:\n"
            interpretation += "- Models may be redundant or highly correlated\n"
            interpretation += "- Individual best model may be sufficient\n"
            interpretation += "- Need to examine model diversity\n\n"
        else:
            interpretation += f"⚠️ **Ensemble Degradation**: Ensemble performs worse ({improvement:.3f}). This indicates:\n"
            interpretation += "- Some models may add noise rather than signal\n"
            interpretation += "- Weighting scheme may need adjustment\n"
            interpretation += "- Consider using only top-performing individual models\n\n"
    
    if coupling_results:
        interpretation += "## Coupling Threshold Analysis\n\n"
        
        stats = coupling_results.get('statistics', {})
        regime_dist = coupling_results.get('regime_distribution', {})
        evidence = coupling_results.get('threshold_evidence', {})
        
        target_zone = regime_dist.get('in_0.6_0.85', 0)
        
        # Interpret distribution
        if target_zone > 50:
            interpretation += f"✅ **Strong Support for 0.6-0.85 Range**: {target_zone:.1f}% of correlations fall in the target zone. This suggests:\n"
            interpretation += "- Natural brain correlations do cluster in this range\n"
            interpretation += "- The LCC threshold hypothesis has empirical support\n"
            interpretation += "- This aligns with neuroscience literature on optimal coupling\n\n"
        elif target_zone > 30:
            interpretation += f"📊 **Moderate Support**: {target_zone:.1f}% in target zone (0.6-0.85). This suggests:\n"
            interpretation += "- Some clustering observed but not dominant\n"
            interpretation += "- May need larger sample size for clearer pattern\n"
            interpretation += "- Results are somewhat consistent with hypothesis\n\n"
        else:
            interpretation += f"⚠️ **Limited Support**: Only {target_zone:.1f}% in target zone. This suggests:\n"
            interpretation += "- Correlations may not naturally cluster at 0.6-0.85\n"
            interpretation += "- Hypothesis may need refinement\n"
            interpretation += "- Alternative thresholds may be more appropriate\n\n"
        
        # Interpret peaks
        if evidence.get('peak_near_0.6') and evidence.get('peak_near_0.85'):
            interpretation += "🎯 **Bimodal Distribution Detected**: Peaks near both 0.6 and 0.85 thresholds. This is remarkable because:\n"
            interpretation += "- Suggests two distinct coupling regimes in brain activity\n"
            interpretation += "- Strongly supports the theoretical framework\n"
            interpretation += "- Aligns with phase synchronization literature (γ=0.85)\n\n"
        elif evidence.get('peak_near_0.6') or evidence.get('peak_near_0.85'):
            interpretation += "📊 **Single Peak Detected**: Peak near one threshold but not both. This suggests:\n"
            interpretation += "- Partial support for the coupling framework\n"
            interpretation += "- One threshold may be more fundamental than the other\n"
            interpretation += "- May need to investigate non-uniformity in coupling states\n\n"
        else:
            interpretation += "⚠️ **No Clear Peaks**: No distinct peaks at proposed thresholds. This indicates:\n"
            interpretation += "- Distribution may be more uniform or have different structure\n"
            interpretation += "- Thresholds may be dataset-specific rather than universal\n"
            interpretation += "- Alternative analysis methods may be needed\n\n"
    
    interpretation += "## 🔬 Next Steps\n\n"
    interpretation += "Based on these results:\n\n"
    interpretation += "1. **If performance is promising**: Replicate with DEAP dataset (32 real participants)\n"
    interpretation += "2. **If ensemble helps**: Investigate which model combinations work best\n"
    interpretation += "3. **If thresholds supported**: Test on additional datasets (SEED, AMIGOS)\n"
    interpretation += "4. **If results are weak**: Revisit feature extraction and preprocessing\n\n"
    interpretation += "**Remember**: Even positive results here DO NOT validate safety for human use. See VALIDATION_METHODOLOGY.md for required safety steps.\n"
    
    return interpretation
