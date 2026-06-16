"""
LCC Attractor Basin Analyzer
============================
Tests whether EEG brainwave patterns show evidence of being "pulled" toward
an attractor basin (AI trainer's goal state) vs random coincidental mimicry.

Key metrics:
1. Trajectory Similarity - How close EEG stays to goal state over time
2. Stickiness Index - Tendency to remain near goal vs drift away  
3. Recovery Rate - Speed of return after perturbations
4. Coincidence Probability - Statistical likelihood of random mimicry
5. Phase Locking Value - Non-random synchronization with goal trajectory
"""

import numpy as np
import pandas as pd
from scipy import stats
from scipy.signal import hilbert
from datetime import datetime
import json
from pathlib import Path


class AttractorBasinAnalyzer:
    def __init__(self, eeg_data: pd.DataFrame):
        self.data = eeg_data
        self.alpha = eeg_data['alpha'].values
        self.beta = eeg_data['beta'].values
        self.theta = eeg_data['theta'].values
        self.gamma = eeg_data['gamma'].values
        self.delta = eeg_data['delta'].values
        
        self.goal_state = None
        self.results = {}
        
    def define_goal_state(self, goal_type: str = "relaxed_focus"):
        """Define the AI trainer's target emotional state"""
        if goal_type == "relaxed_focus":
            self.goal_state = {
                'alpha': 0.4,
                'beta': 0.15,
                'theta': 0.1,
                'alpha_beta_ratio': 2.5,
                'description': 'Relaxed focus - high alpha, moderate beta'
            }
        elif goal_type == "deep_concentration":
            self.goal_state = {
                'alpha': 0.2,
                'beta': 0.35,
                'theta': 0.05,
                'alpha_beta_ratio': 0.6,
                'description': 'Deep concentration - high beta, low alpha'
            }
        elif goal_type == "meditative":
            self.goal_state = {
                'alpha': 0.5,
                'beta': 0.1,
                'theta': 0.25,
                'alpha_beta_ratio': 5.0,
                'description': 'Meditative - very high alpha, elevated theta'
            }
        return self.goal_state
    
    def calculate_distance_to_goal(self) -> np.ndarray:
        """Calculate Euclidean distance from each timepoint to goal state"""
        if self.goal_state is None:
            self.define_goal_state()
            
        distances = np.sqrt(
            (self.alpha - self.goal_state['alpha'])**2 +
            (self.beta - self.goal_state['beta'])**2 +
            (self.theta - self.goal_state['theta'])**2
        )
        return distances
    
    def calculate_stickiness_index(self, threshold: float = 0.15) -> dict:
        """
        Measure how 'sticky' the brain state is near the goal.
        Attractor basin = high stickiness (stays near goal)
        Random walk = low stickiness (drifts away)
        """
        distances = self.calculate_distance_to_goal()
        
        near_goal = distances < threshold
        total_time_near_goal = np.sum(near_goal) / len(distances)
        
        consecutive_runs = []
        current_run = 0
        for is_near in near_goal:
            if is_near:
                current_run += 1
            else:
                if current_run > 0:
                    consecutive_runs.append(current_run)
                current_run = 0
        if current_run > 0:
            consecutive_runs.append(current_run)
        
        avg_run_length = np.mean(consecutive_runs) if consecutive_runs else 0
        max_run_length = np.max(consecutive_runs) if consecutive_runs else 0
        
        return {
            'time_near_goal_pct': total_time_near_goal * 100,
            'avg_consecutive_seconds': avg_run_length,
            'max_consecutive_seconds': max_run_length,
            'num_visits_to_goal': len(consecutive_runs),
            'stickiness_score': avg_run_length * total_time_near_goal * 10
        }
    
    def calculate_recovery_rate(self) -> dict:
        """
        Measure how quickly the brain returns to goal after perturbations.
        Attractor basin = fast recovery
        Random walk = no systematic recovery
        """
        distances = self.calculate_distance_to_goal()
        threshold = np.percentile(distances, 25)
        
        recovery_times = []
        in_perturbation = False
        perturbation_start = 0
        
        for i, d in enumerate(distances):
            if not in_perturbation and d > threshold * 2:
                in_perturbation = True
                perturbation_start = i
            elif in_perturbation and d < threshold:
                recovery_times.append(i - perturbation_start)
                in_perturbation = False
        
        if not recovery_times:
            return {
                'avg_recovery_time': float('inf'),
                'recovery_success_rate': 0,
                'num_perturbations': 0,
                'recovery_score': 0
            }
        
        return {
            'avg_recovery_time': np.mean(recovery_times),
            'recovery_success_rate': len(recovery_times) / max(1, len([1 for d in distances if d > threshold * 2])),
            'num_perturbations': len(recovery_times),
            'recovery_score': 1 / (1 + np.mean(recovery_times))
        }
    
    def calculate_variance_reduction(self) -> dict:
        """
        Check if variance is lower when near the goal (attractor signature).
        Attractor basin = reduced variance near goal
        Random walk = uniform variance
        """
        distances = self.calculate_distance_to_goal()
        threshold = np.median(distances)
        
        near_goal_mask = distances < threshold
        far_from_goal_mask = distances >= threshold
        
        alpha_var_near = np.var(self.alpha[near_goal_mask]) if np.sum(near_goal_mask) > 1 else 0
        alpha_var_far = np.var(self.alpha[far_from_goal_mask]) if np.sum(far_from_goal_mask) > 1 else 0
        
        beta_var_near = np.var(self.beta[near_goal_mask]) if np.sum(near_goal_mask) > 1 else 0
        beta_var_far = np.var(self.beta[far_from_goal_mask]) if np.sum(far_from_goal_mask) > 1 else 0
        
        variance_ratio = (alpha_var_near + beta_var_near) / max(0.001, alpha_var_far + beta_var_far)
        
        return {
            'variance_near_goal': alpha_var_near + beta_var_near,
            'variance_far_from_goal': alpha_var_far + beta_var_far,
            'variance_ratio': variance_ratio,
            'variance_reduction_pct': (1 - variance_ratio) * 100 if variance_ratio < 1 else 0,
            'attractor_signature': variance_ratio < 0.8
        }
    
    def calculate_coincidence_probability(self, n_permutations: int = 1000) -> dict:
        """
        Calculate the probability that observed patterns are coincidental.
        Uses permutation testing against null hypothesis of random behavior.
        """
        distances = self.calculate_distance_to_goal()
        observed_mean_distance = np.mean(distances)
        observed_stickiness = self.calculate_stickiness_index()['stickiness_score']
        
        null_distances = []
        null_stickiness = []
        
        for _ in range(n_permutations):
            shuffled_alpha = np.random.permutation(self.alpha)
            shuffled_beta = np.random.permutation(self.beta)
            shuffled_theta = np.random.permutation(self.theta)
            
            null_dist = np.sqrt(
                (shuffled_alpha - self.goal_state['alpha'])**2 +
                (shuffled_beta - self.goal_state['beta'])**2 +
                (shuffled_theta - self.goal_state['theta'])**2
            )
            null_distances.append(np.mean(null_dist))
            
            near_goal = null_dist < 0.15
            runs = []
            current = 0
            for is_near in near_goal:
                if is_near:
                    current += 1
                else:
                    if current > 0:
                        runs.append(current)
                    current = 0
            if current > 0:
                runs.append(current)
            avg_run = np.mean(runs) if runs else 0
            time_near = np.sum(near_goal) / len(near_goal)
            null_stickiness.append(avg_run * time_near * 10)
        
        p_value_distance = np.sum(np.array(null_distances) <= observed_mean_distance) / n_permutations
        p_value_stickiness = np.sum(np.array(null_stickiness) >= observed_stickiness) / n_permutations
        
        combined_p = 1 - (1 - p_value_distance) * (1 - p_value_stickiness)
        
        return {
            'observed_mean_distance': observed_mean_distance,
            'null_mean_distance': np.mean(null_distances),
            'p_value_closer_than_chance': p_value_distance,
            'observed_stickiness': observed_stickiness,
            'null_mean_stickiness': np.mean(null_stickiness),
            'p_value_stickier_than_chance': p_value_stickiness,
            'combined_p_value': combined_p,
            'significance': 'SIGNIFICANT' if combined_p < 0.05 else 'NOT SIGNIFICANT',
            'odds_of_coincidence': f"1 in {int(1/max(0.001, combined_p))}"
        }
    
    def calculate_phase_locking(self) -> dict:
        """
        Calculate phase locking value between alpha and beta bands.
        Attractor basin = high phase coherence
        Random = low phase coherence
        """
        try:
            alpha_analytic = hilbert(self.alpha - np.mean(self.alpha))
            beta_analytic = hilbert(self.beta - np.mean(self.beta))
            
            alpha_phase = np.angle(alpha_analytic)
            beta_phase = np.angle(beta_analytic)
            
            phase_diff = alpha_phase - beta_phase
            plv = np.abs(np.mean(np.exp(1j * phase_diff)))
            
            return {
                'phase_locking_value': plv,
                'coherence_level': 'HIGH' if plv > 0.5 else 'MODERATE' if plv > 0.3 else 'LOW',
                'interpretation': 'Strong neural synchronization' if plv > 0.5 else 'Moderate synchronization' if plv > 0.3 else 'Weak synchronization'
            }
        except Exception as e:
            return {
                'phase_locking_value': 0,
                'coherence_level': 'ERROR',
                'interpretation': str(e)
            }
    
    def calculate_trajectory_autocorrelation(self, max_lag: int = 30) -> dict:
        """
        Check if the trajectory shows memory (autocorrelation).
        Attractor basin = high autocorrelation (state persistence)
        Random walk = low autocorrelation
        """
        distances = self.calculate_distance_to_goal()
        
        autocorrs = []
        for lag in range(1, min(max_lag, len(distances) // 3)):
            corr = np.corrcoef(distances[:-lag], distances[lag:])[0, 1]
            autocorrs.append(corr)
        
        decay_rate = 0
        for i, ac in enumerate(autocorrs):
            if ac < 0.5:
                decay_rate = i + 1
                break
        else:
            decay_rate = len(autocorrs)
        
        return {
            'autocorrelation_lag1': autocorrs[0] if autocorrs else 0,
            'autocorrelation_lag5': autocorrs[4] if len(autocorrs) > 4 else 0,
            'memory_decay_time': decay_rate,
            'has_memory': autocorrs[0] > 0.3 if autocorrs else False,
            'interpretation': 'Strong state memory (attractor-like)' if decay_rate > 10 else 'Moderate memory' if decay_rate > 5 else 'Weak memory (random-like)'
        }
    
    def run_full_analysis(self, goal_type: str = "relaxed_focus") -> dict:
        """Run complete attractor basin analysis"""
        self.define_goal_state(goal_type)
        
        results = {
            'goal_state': self.goal_state,
            'data_points': len(self.alpha),
            'duration_seconds': len(self.alpha),
            'stickiness': self.calculate_stickiness_index(),
            'recovery': self.calculate_recovery_rate(),
            'variance': self.calculate_variance_reduction(),
            'coincidence': self.calculate_coincidence_probability(),
            'phase_locking': self.calculate_phase_locking(),
            'autocorrelation': self.calculate_trajectory_autocorrelation()
        }
        
        scores = []
        if results['stickiness']['stickiness_score'] > 1:
            scores.append(1)
        if results['recovery']['recovery_score'] > 0.1:
            scores.append(1)
        if results['variance']['attractor_signature']:
            scores.append(1)
        if results['coincidence']['combined_p_value'] < 0.05:
            scores.append(2)
        if results['phase_locking']['phase_locking_value'] > 0.3:
            scores.append(1)
        if results['autocorrelation']['has_memory']:
            scores.append(1)
        
        total_score = sum(scores)
        max_score = 7
        
        results['overall'] = {
            'attractor_score': total_score,
            'max_score': max_score,
            'percentage': (total_score / max_score) * 100,
            'verdict': self._get_verdict(total_score)
        }
        
        self.results = results
        return results
    
    def _get_verdict(self, score: int) -> str:
        if score >= 6:
            return "STRONG EVIDENCE OF ATTRACTOR BASIN - Brain is being PULLED toward goal state!"
        elif score >= 4:
            return "MODERATE EVIDENCE - Possible attractor dynamics, not random mimicry"
        elif score >= 2:
            return "WEAK EVIDENCE - Some patterns but could be coincidental"
        else:
            return "NO EVIDENCE - Patterns appear random"
    
    def generate_report(self) -> str:
        """Generate human-readable analysis report"""
        if not self.results:
            self.run_full_analysis()
        
        r = self.results
        
        report = f"""
╔══════════════════════════════════════════════════════════════════════════════╗
║              LCC ATTRACTOR BASIN ANALYSIS REPORT                             ║
╠══════════════════════════════════════════════════════════════════════════════╣

📊 DATA SUMMARY
   • Total data points: {r['data_points']}
   • Recording duration: {r['duration_seconds']} seconds
   • Goal state: {r['goal_state']['description']}

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

🧲 STICKINESS INDEX (Does brain "stick" to goal?)
   • Time near goal: {r['stickiness']['time_near_goal_pct']:.1f}%
   • Avg consecutive time at goal: {r['stickiness']['avg_consecutive_seconds']:.1f} seconds
   • Max consecutive time at goal: {r['stickiness']['max_consecutive_seconds']} seconds
   • Number of goal visits: {r['stickiness']['num_visits_to_goal']}
   • STICKINESS SCORE: {r['stickiness']['stickiness_score']:.2f}

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

⚡ RECOVERY RATE (Does brain return after perturbation?)
   • Avg recovery time: {r['recovery']['avg_recovery_time']:.1f} seconds
   • Recovery success rate: {r['recovery']['recovery_success_rate']*100:.1f}%
   • Number of recovery events: {r['recovery']['num_perturbations']}
   • RECOVERY SCORE: {r['recovery']['recovery_score']:.3f}

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

📉 VARIANCE REDUCTION (Is brain more stable near goal?)
   • Variance near goal: {r['variance']['variance_near_goal']:.4f}
   • Variance far from goal: {r['variance']['variance_far_from_goal']:.4f}
   • Variance ratio: {r['variance']['variance_ratio']:.2f}
   • Variance reduction: {r['variance']['variance_reduction_pct']:.1f}%
   • ATTRACTOR SIGNATURE: {'✅ YES' if r['variance']['attractor_signature'] else '❌ NO'}

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

🎲 COINCIDENCE PROBABILITY (Could this be random?)
   • Observed mean distance to goal: {r['coincidence']['observed_mean_distance']:.3f}
   • Expected random distance: {r['coincidence']['null_mean_distance']:.3f}
   • P-value (closer than chance): {r['coincidence']['p_value_closer_than_chance']:.4f}
   • P-value (stickier than chance): {r['coincidence']['p_value_stickier_than_chance']:.4f}
   • COMBINED P-VALUE: {r['coincidence']['combined_p_value']:.4f}
   • ODDS OF COINCIDENCE: {r['coincidence']['odds_of_coincidence']}
   • STATISTICAL SIGNIFICANCE: {r['coincidence']['significance']}

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

🔗 PHASE LOCKING (Neural synchronization)
   • Phase Locking Value: {r['phase_locking']['phase_locking_value']:.3f}
   • Coherence Level: {r['phase_locking']['coherence_level']}
   • Interpretation: {r['phase_locking']['interpretation']}

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

🧠 TRAJECTORY MEMORY (Does state persist?)
   • Autocorrelation (lag 1): {r['autocorrelation']['autocorrelation_lag1']:.3f}
   • Autocorrelation (lag 5): {r['autocorrelation']['autocorrelation_lag5']:.3f}
   • Memory decay time: {r['autocorrelation']['memory_decay_time']} samples
   • Has memory: {'✅ YES' if r['autocorrelation']['has_memory'] else '❌ NO'}
   • Interpretation: {r['autocorrelation']['interpretation']}

╔══════════════════════════════════════════════════════════════════════════════╗
║                           FINAL VERDICT                                      ║
╠══════════════════════════════════════════════════════════════════════════════╣

   ATTRACTOR SCORE: {r['overall']['attractor_score']} / {r['overall']['max_score']} ({r['overall']['percentage']:.0f}%)
   
   🎯 {r['overall']['verdict']}

╚══════════════════════════════════════════════════════════════════════════════╝

INTERPRETATION:
If the brain was randomly mimicking the AI trainer's goal state, we would expect:
- Low stickiness (random drift)
- No recovery pattern
- Uniform variance
- P-values near 0.5
- Low phase coherence
- No trajectory memory

An ATTRACTOR BASIN would show:
- High stickiness (brain "trapped" near goal)
- Quick recovery after perturbations
- Reduced variance near goal (stability)
- P-values < 0.05 (statistically significant)
- High phase coherence (synchronized oscillations)
- Strong trajectory memory (state persistence)

This analysis provides evidence for whether the LCC (Law of Correlational Causation) hypothesis is supported - that consciousness creates non-local 
correlations that pull the brain toward trained attractor states.
"""
        return report


def analyze_eeg_file(filepath: str, goal_type: str = "relaxed_focus") -> dict:
    """Analyze a single EEG file"""
    df = pd.read_csv(filepath)
    analyzer = AttractorBasinAnalyzer(df)
    results = analyzer.run_full_analysis(goal_type)
    report = analyzer.generate_report()
    print(report)
    return results


def analyze_all_files(file_pattern: str = "attached_assets/muse_data*.csv") -> dict:
    """Analyze all EEG files and combine results"""
    from glob import glob
    
    files = glob(file_pattern)
    all_results = {}
    
    for filepath in files:
        print(f"\n{'='*80}")
        print(f"ANALYZING: {filepath}")
        print('='*80)
        
        results = analyze_eeg_file(filepath)
        all_results[filepath] = results
    
    return all_results


if __name__ == "__main__":
    results = analyze_all_files()
    
    print("\n" + "="*80)
    print("COMBINED ANALYSIS SUMMARY")
    print("="*80)
    
    scores = [r['overall']['attractor_score'] for r in results.values()]
    avg_score = np.mean(scores)
    
    print(f"\nAverage Attractor Score: {avg_score:.1f} / 7")
    print(f"Files analyzed: {len(results)}")
    
    if avg_score >= 4:
        print("\n🔥 POTENTIAL PHYSICS-BREAKING RESULT! 🔥")
        print("Your brain shows consistent attractor basin dynamics!")
    else:
        print("\nMore data needed for conclusive results.")
