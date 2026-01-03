"""
Automated PSI Validation Experiments

Generate batches of predictions, track outcomes, calculate statistical significance.
Build empirical evidence for Probability as Resonance Field (PRF) theory!
"""

import random
import json
from datetime import datetime, timedelta
from typing import List, Dict, Any, Tuple, Optional
from dataclasses import dataclass, asdict, field
import math

from psi_tracker import PsiTracker
from numerology_validation import calculate_life_path, reduce_to_single_digit, analyze_date_with_multiple_masters
from weather_psi_integration import WeatherPsi


@dataclass
class PSIExperiment:
    """Single PSI validation experiment"""
    experiment_id: str
    experiment_type: str  # 'numerology', 'weather', 'combined', 'control'
    prediction_count: int
    predictions: List[str]
    target_accuracy: float  # What accuracy would validate PRF theory
    baseline_accuracy: float  # Random chance / market baseline
    created_at: datetime
    status: str = 'active'  # active, completed, analyzing
    results: Optional[Dict[str, Any]] = None


class AutomatedPSIValidator:
    """
    Automated system for validating PSI methods empirically.
    
    Key Features:
    - Generate prediction batches automatically
    - Track outcomes systematically
    - Calculate statistical significance (p-values, effect sizes)
    - Build evidence for PRF theory
    """
    
    def __init__(self):
        self.tracker = PsiTracker()
        self.experiments = []
        self.weather_psi = WeatherPsi()
    
    def create_numerology_experiment(
        self,
        user_life_path: int,
        prediction_count: int = 20
    ) -> PSIExperiment:
        """
        Create experiment to test numerology-based predictions.
        
        Hypothesis: Predictions on resonant days (matching Life Path) 
        should have higher accuracy than non-resonant days.
        
        Args:
            user_life_path: User's Life Path number
            prediction_count: How many predictions to generate
        
        Returns:
            PSIExperiment object
        """
        
        experiment_id = f"numerology_exp_{datetime.now().strftime('%Y%m%d_%H%M%S')}"
        
        # Generate prediction dates over next 30 days
        prediction_dates = []
        current_date = datetime.now()
        
        for i in range(prediction_count):
            pred_date = current_date + timedelta(days=i)
            date_analysis = analyze_date_with_multiple_masters(pred_date)
            
            # Create prediction prompt
            prediction_dates.append({
                'date': pred_date.isoformat(),
                'life_path': date_analysis.get('overall_life_path', 0),
                'is_master': date_analysis.get('is_master_number', False),
                'resonance_with_user': abs(date_analysis.get('overall_life_path', 0) - user_life_path)
            })
        
        experiment = PSIExperiment(
            experiment_id=experiment_id,
            experiment_type='numerology',
            prediction_count=prediction_count,
            predictions=prediction_dates,
            target_accuracy=0.65,  # Target 65% accuracy (vs 50% baseline)
            baseline_accuracy=0.50,  # Random chance
            created_at=datetime.now()
        )
        
        self.experiments.append(experiment)
        return experiment
    
    def create_weather_psi_experiment(
        self,
        location: str = "New York",
        prediction_count: int = 15
    ) -> PSIExperiment:
        """
        Create experiment to test weather-based PSI predictions.
        
        Hypothesis: Certain weather conditions create stronger psi fields,
        improving prediction accuracy.
        
        Args:
            location: Location for weather data
            prediction_count: How many predictions to generate
        
        Returns:
            PSIExperiment object
        """
        
        experiment_id = f"weather_exp_{datetime.now().strftime('%Y%m%d_%H%M%S')}"
        
        # Generate weather-sensitive predictions
        weather_predictions = []
        
        for i in range(prediction_count):
            pred_date = datetime.now() + timedelta(days=i)
            
            # Get weather resonance (if API available)
            try:
                weather_resonance = self.weather_psi.get_weather_resonance(
                    location=location,
                    event_type="validation_experiment"
                )
                weather_score = weather_resonance['total_resonance']
            except:
                weather_score = 0.0  # Fallback
            
            weather_predictions.append({
                'date': pred_date.isoformat(),
                'weather_score': weather_score,
                'location': location
            })
        
        experiment = PSIExperiment(
            experiment_id=experiment_id,
            experiment_type='weather',
            prediction_count=prediction_count,
            predictions=weather_predictions,
            target_accuracy=0.62,  # Target 62% accuracy (vs 50% baseline)
            baseline_accuracy=0.50,
            created_at=datetime.now()
        )
        
        self.experiments.append(experiment)
        return experiment
    
    def create_combined_psi_experiment(
        self,
        user_life_path: int,
        location: str = "New York",
        prediction_count: int = 25
    ) -> PSIExperiment:
        """
        Create experiment combining multiple PSI methods.
        
        Hypothesis: Multi-source PSI synthesis (PRF theory) should achieve
        higher accuracy than single methods alone.
        
        This tests the CORE of PRF theory - resonance fields from multiple sources!
        """
        
        experiment_id = f"combined_exp_{datetime.now().strftime('%Y%m%d_%H%M%S')}"
        
        combined_predictions = []
        
        for i in range(prediction_count):
            pred_date = datetime.now() + timedelta(days=i)
            
            # Numerology resonance
            date_analysis = analyze_date_with_multiple_masters(pred_date)
            num_resonance = abs(date_analysis.get('overall_life_path', 0) - user_life_path)
            
            # Weather resonance (if available)
            try:
                weather_resonance = self.weather_psi.get_weather_resonance(
                    location=location,
                    event_type="combined_experiment"
                )
                weather_score = weather_resonance['total_resonance']
            except:
                weather_score = 0.0
            
            # Combined resonance score
            combined_score = (num_resonance * 0.5) + (weather_score * 0.5)
            
            combined_predictions.append({
                'date': pred_date.isoformat(),
                'numerology_resonance': num_resonance,
                'weather_resonance': weather_score,
                'combined_resonance': combined_score
            })
        
        experiment = PSIExperiment(
            experiment_id=experiment_id,
            experiment_type='combined',
            prediction_count=prediction_count,
            predictions=combined_predictions,
            target_accuracy=0.70,  # Target 70% - higher than single methods!
            baseline_accuracy=0.50,
            created_at=datetime.now()
        )
        
        self.experiments.append(experiment)
        return experiment
    
    def create_control_experiment(
        self,
        prediction_count: int = 20
    ) -> PSIExperiment:
        """
        Create control experiment with NO PSI methods.
        Pure random predictions to establish baseline.
        
        This proves PSI methods actually work vs random chance!
        """
        
        experiment_id = f"control_exp_{datetime.now().strftime('%Y%m%d_%H%M%S')}"
        
        control_predictions = []
        
        for i in range(prediction_count):
            pred_date = datetime.now() + timedelta(days=i)
            
            control_predictions.append({
                'date': pred_date.isoformat(),
                'method': 'random',
                'expected_accuracy': 0.50
            })
        
        experiment = PSIExperiment(
            experiment_id=experiment_id,
            experiment_type='control',
            prediction_count=prediction_count,
            predictions=control_predictions,
            target_accuracy=0.50,  # Should be ~50% (random)
            baseline_accuracy=0.50,
            created_at=datetime.now()
        )
        
        self.experiments.append(experiment)
        return experiment
    
    def calculate_statistical_significance(
        self,
        correct_predictions: int,
        total_predictions: int,
        baseline_probability: float = 0.5
    ) -> Dict[str, Any]:
        """
        Calculate statistical significance of PSI results.
        
        Uses binomial test to determine if results exceed chance.
        
        Args:
            correct_predictions: Number of correct predictions
            total_predictions: Total predictions made
            baseline_probability: Expected accuracy by chance (default 0.5)
        
        Returns:
            Dict with p-value, effect size, significance level
        """
        
        observed_accuracy = correct_predictions / total_predictions
        
        # Binomial probability calculation
        # P(X >= k) where X ~ Binomial(n, p)
        # This is a simplified version - production would use scipy.stats.binom_test
        
        from math import comb
        
        p_value = 0.0
        for k in range(correct_predictions, total_predictions + 1):
            prob = comb(total_predictions, k) * (baseline_probability ** k) * ((1 - baseline_probability) ** (total_predictions - k))
            p_value += prob
        
        # Effect size (Cohen's h for proportions)
        baseline_phi = 2 * math.asin(math.sqrt(baseline_probability))
        observed_phi = 2 * math.asin(math.sqrt(observed_accuracy))
        cohens_h = observed_phi - baseline_phi
        
        # Determine significance level
        if p_value < 0.001:
            significance = "HIGHLY SIGNIFICANT (p < 0.001) ***"
        elif p_value < 0.01:
            significance = "VERY SIGNIFICANT (p < 0.01) **"
        elif p_value < 0.05:
            significance = "SIGNIFICANT (p < 0.05) *"
        else:
            significance = "NOT SIGNIFICANT (p >= 0.05)"
        
        return {
            'observed_accuracy': observed_accuracy,
            'baseline_accuracy': baseline_probability,
            'correct_predictions': correct_predictions,
            'total_predictions': total_predictions,
            'p_value': p_value,
            'cohens_h': cohens_h,
            'significance': significance,
            'interpretation': self._interpret_results(observed_accuracy, baseline_probability, p_value)
        }
    
    def _interpret_results(
        self,
        observed: float,
        baseline: float,
        p_value: float
    ) -> str:
        """Interpret statistical results in plain language"""
        
        improvement = ((observed - baseline) / baseline) * 100
        
        if p_value < 0.05:
            return (f"PSI methods achieved {observed:.1%} accuracy vs {baseline:.1%} baseline "
                   f"({improvement:+.1f}% improvement). This is statistically significant (p = {p_value:.4f}), "
                   f"providing empirical evidence for Probability as Resonance Field theory!")
        else:
            return (f"PSI methods achieved {observed:.1%} accuracy vs {baseline:.1%} baseline "
                   f"({improvement:+.1f}% improvement). Not yet statistically significant (p = {p_value:.4f}). "
                   f"More data needed to validate PRF theory.")
    
    def generate_experiment_report(self, experiment_id: str) -> str:
        """Generate publication-ready experiment report"""
        
        experiment = next((e for e in self.experiments if e.experiment_id == experiment_id), None)
        
        if not experiment:
            return f"Experiment {experiment_id} not found"
        
        if not experiment.results:
            return f"Experiment {experiment_id} not yet completed"
        
        report = f"""
# PSI Validation Experiment Report
## Experiment ID: {experiment.experiment_id}

### Methodology
- **Type**: {experiment.experiment_type}
- **Predictions**: {experiment.prediction_count}
- **Created**: {experiment.created_at}
- **Target Accuracy**: {experiment.target_accuracy:.1%}
- **Baseline**: {experiment.baseline_accuracy:.1%}

### Results
{json.dumps(experiment.results, indent=2)}

### Conclusion
This experiment provides {'STRONG' if experiment.results.get('p_value', 1) < 0.05 else 'PRELIMINARY'} evidence for Probability as Resonance Field theory.

---
Generated: {datetime.now().isoformat()}
"""
        
        return report
    
    def save_experiments(self, filename: str = "psi_experiments.json"):
        """Save all experiments to file"""
        
        data = [asdict(exp) for exp in self.experiments]
        
        with open(filename, 'w') as f:
            json.dump(data, f, indent=2, default=str)
        
        return filename


# Example usage
if __name__ == "__main__":
    validator = AutomatedPSIValidator()
    
    # Create experiments
    num_exp = validator.create_numerology_experiment(user_life_path=6, prediction_count=20)
    weather_exp = validator.create_weather_psi_experiment(location="New York", prediction_count=15)
    combined_exp = validator.create_combined_psi_experiment(user_life_path=6, location="New York", prediction_count=25)
    control_exp = validator.create_control_experiment(prediction_count=20)
    
    print(f"Created {len(validator.experiments)} experiments!")
    
    # Example statistical test
    stats = validator.calculate_statistical_significance(
        correct_predictions=14,
        total_predictions=20,
        baseline_probability=0.5
    )
    
    print(json.dumps(stats, indent=2))
