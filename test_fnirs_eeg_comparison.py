"""
Test script for fNIRS-EEG cross-modality comparison
Demonstrates virtual animal testing with parallel fNIRS and EEG acquisition
"""

from animal_testing_simulation import AnimalStudySimulator
import json

def run_comparison_test():
    """Run a test study comparing fNIRS and EEG modalities across species"""
    
    print("="*80)
    print("fNIRS-EEG CROSS-MODALITY VALIDATION TEST")
    print("="*80)
    print()
    
    # Test with different species
    species_list = [
        ('rat', 15),
        ('mouse', 12),
        ('macaque', 10),  # Primate
        ('marmoset', 8)   # Smaller primate
    ]
    
    for species, n_subjects in species_list:
        print(f"\n{'='*80}")
        print(f"SPECIES: {species.upper()} (n={n_subjects})")
        print(f"{'='*80}\n")
        
        # Create simulator
        simulator = AnimalStudySimulator(
            n_subjects=n_subjects,
            species=species
        )
        
        # Run study
        results = simulator.run_study(
            intervention_duration_minutes=5,
            recording_duration_minutes=10
        )
        
        # Extract fNIRS-EEG validation stats
        validation = results['group_statistics']['fnirs_eeg_validation']
        
        print(f"Sample Sizes:")
        print(f"  - Agreement measurements: {validation['sample_size_agreement']}")
        print(f"  - Valid correlations: {validation['sample_size_correlation']}")
        print(f"  - Statistical inference available: {validation['statistical_inference_available']}")
        print()
        
        if validation['statistical_inference_available']:
            print(f"Agreement Rate:")
            print(f"  - Point estimate: {validation['modality_agreement_rate_percent']:.1f}%")
            print(f"  - 95% CI: [{validation['agreement_95ci_low']*100:.1f}%, {validation['agreement_95ci_high']*100:.1f}%]")
            print(f"  - Significantly above chance (50%): {validation['agreement_significantly_above_chance']}")
            print(f"  - p-value: {validation['agreement_exceeds_chance_p_value']:.4f}")
            print()
            
            print(f"Temporal Correlation:")
            print(f"  - Mean: {validation['mean_temporal_correlation']:.3f}")
            print(f"  - 95% CI: [{validation['correlation_95ci_low']:.3f}, {validation['correlation_95ci_high']:.3f}]")
            print(f"  - Significantly positive: {validation['correlation_significantly_positive']}")
            print(f"  - p-value: {validation['correlation_significantly_nonzero_p_value']:.4f}")
            print()
            
            print(f"Validation Strength: {validation['validation_strength'].upper()}")
            print(f"Interpretation: {validation['interpretation']}")
        else:
            print(f"⚠️  {validation['interpretation']}")
        
        print()
        
        # Show a few individual subject examples
        print(f"Individual Subject Examples (first 3):")
        for i, subj in enumerate(results['individual_results'][:3]):
            comp = subj['fnirs_eeg_comparison']
            print(f"\n  Subject {subj['subject_id']}:")
            print(f"    - Baseline mood: {subj['baseline_mood']}")
            print(f"    - fNIRS detected: {comp['fnirs_detected_direction']}")
            print(f"    - EEG detected: {comp['eeg_detected_direction']}")
            print(f"    - Modalities agree: {comp['modalities_agree']}")
            print(f"    - Temporal correlation: {comp['fnirs_eeg_correlation']:.3f}")
            print(f"    - Agreement strength: {comp['agreement_strength']}")
    
    print("\n" + "="*80)
    print("TEST COMPLETE")
    print("="*80)

if __name__ == "__main__":
    run_comparison_test()
