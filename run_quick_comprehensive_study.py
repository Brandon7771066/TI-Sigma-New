"""
Quick comprehensive study runner - generates full report efficiently
"""

from comprehensive_animal_study import *

# Run with smaller but statistically valid sample size
results = run_comprehensive_multi_species_study(
    sample_size_per_species=30,  # 30 per species = 90 total (still high statistical power)
    durations=[3, 5]
)

# Save and print results
output_file = f"comprehensive_study_results_{datetime.now().strftime('%Y%m%d_%H%M%S')}.json"

# Remove large arrays
for species, durations in results['species_results'].items():
    for duration, data in durations.items():
        if 'eeg' in data and 'individual_results' in data['eeg']:
            for subject in data['eeg']['individual_results']:
                if 'baseline_eeg' in subject:
                    del subject['baseline_eeg']
                if 'post_eeg' in subject:
                    del subject['post_eeg']

with open(output_file, 'w') as f:
    json.dump(results, f, indent=2, default=str)

print(f"\nResults saved to: {output_file}\n")
print_executive_summary(results)

# Detailed findings
print("\n\n" + "="*80)
print("DETAILED FINDINGS")
print("="*80)

print("\n\n📊 CROSS-SPECIES COMPARISON")
print("="*60)
cross_species = results['cross_species_comparison']
for species, data in cross_species['efficacy_by_species'].items():
    print(f"\n{species.upper()}:")
    print(f"  Mean valence shift: {data['mean_valence_shift']:+.3f} ± {data['std_valence_shift']:.3f}")
    safety = cross_species['safety_by_species'][species]
    print(f"  Mean safety score: {safety['mean_safety_score']:.1f}/100")

if 'statistical_test' in cross_species:
    print(f"\nStatistical test: {cross_species['statistical_test']['test']}")
    print(f"Result: {cross_species['statistical_test']['interpretation']}")
    print(f"p-value: {cross_species['statistical_test']['p_value']:.4f}")

print("\n\n⚠️ NEGATIVE EFFECTS ANALYSIS")
print("="*60)
neg_analysis = results['negative_effects_analysis']

print("\nNegative Effect Rates:")
for effect, data in neg_analysis['negative_effect_types'].items():
    print(f"  {effect}: {data['percent']:.2f}% ({data['count']} subjects)")

print("\nStatistical Significance Tests:")
for effect, test in neg_analysis['statistical_tests'].items():
    print(f"\n  {effect}:")
    print(f"    Observed: {test['observed_rate']*100:.2f}%")
    print(f"    Baseline: {test['expected_baseline']*100:.2f}%")
    print(f"    p-value: {test['p_value']:.4f}")
    print(f"    Result: {test['interpretation']}")

print(f"\nHealth Impact Assessment:")
print(f"  Severity: {neg_analysis['health_significance']['severity_assessment']}")
print(f"  Clinical Significance: {neg_analysis['health_significance']['clinical_significance']}")

print("\n\n🎯 SUCCESS RATE INVESTIGATION")
print("="*60)
success_analysis = results['success_rate_analysis']

print(f"\nObserved Success Rate: {success_analysis['observed_success_rate']['percent']:.1f}%")
print(f"  Successful: {success_analysis['observed_success_rate']['n_successful']}")
print(f"  Unsuccessful: {success_analysis['observed_success_rate']['n_unsuccessful']}")

print("\nPredictors of Success:")
print("\n  Baseline Mood Effect:")
mood_pred = success_analysis['predictors_of_success']['baseline_mood']
print("    Successful subjects:")
for mood, pct in mood_pred['successful'].items():
    print(f"      {mood}: {pct:.1f}%")

print("\n  Duration Effect:")
for dur, success_rate in success_analysis['predictors_of_success']['duration_effect'].items():
    print(f"    {dur} min: {success_rate:.1f}% success rate")

print("\n  Coupling Strength Effect:")
coupling_pred = success_analysis['predictors_of_success']['coupling_strength']
print(f"    Successful subjects: mean coupling = {coupling_pred['successful_mean']:.3f}")
print(f"    Unsuccessful subjects: mean coupling = {coupling_pred['unsuccessful_mean']:.3f}")
print(f"    Finding: {coupling_pred['finding']}")

print("\n\nImprovement Strategies:")
for i, strategy in enumerate(success_analysis['improvement_strategies'], 1):
    print(f"\n  {i}. {strategy['strategy']}")
    print(f"     Expected improvement: {strategy['expected_improvement']}")
    print(f"     Implementation: {strategy['implementation']}")
    print(f"     Evidence level: {strategy['evidence_level']}")

print("\n\n⏱️ 3-MINUTE VS 5-MINUTE COMPARISON")
print("="*60)
duration_comp = results['duration_comparison']

stats_comp = duration_comp['statistical_comparison']
print("\nEfficacy Comparison:")
print(f"  3 minutes: {stats_comp['efficacy']['3_min_mean']:.3f} mean valence shift")
print(f"  5 minutes: {stats_comp['efficacy']['5_min_mean']:.3f} mean valence shift")
print(f"  Difference: {stats_comp['efficacy']['5_min_mean'] - stats_comp['efficacy']['3_min_mean']:+.3f}")
print(f"  p-value: {stats_comp['efficacy']['p_value']:.4f}")
print(f"  Result: {stats_comp['efficacy']['interpretation']}")

print("\nSafety Comparison:")
print(f"  3 minutes: {stats_comp['safety']['3_min_mean']:.1f}/100")
print(f"  5 minutes: {stats_comp['safety']['5_min_mean']:.1f}/100")

print(f"\nRecommendation:")
print(f"  {duration_comp['optimal_duration']['recommendation']}")

print("\n\n🧠 PHYSICAL MECHANISMS & LCC COUPLING")
print("="*60)
mech_analysis = results['mechanism_analysis']

print("\nPrimary Mechanism:")
primary = mech_analysis['neural_mechanisms']['primary_mechanism']
print(f"  Name: {primary['name']}")
print(f"  Description: {primary['description']}")
print(f"  Evidence: {primary['evidence']}")
print(f"  Brain regions involved:")
for region in primary['brain_regions']:
    print(f"    - {region}")

print("\nLCC Coupling Details:")
lcc = mech_analysis['lcc_coupling_details']
print("\n  Efficacy by Coupling Strength:")
for regime, data in lcc['coupling_efficacy_relationship'].items():
    print(f"    {regime}:")
    print(f"      Mean effect: {data['mean_valence_shift']:+.3f}")
    print(f"      Success rate: {data['success_rate']:.1f}%")
    print(f"      N subjects: {data['n_subjects']}")

optimal = lcc['optimal_range']
print(f"\n  Optimal Coupling Range: {optimal['regime']}")
print(f"  Mean effect size: {optimal['mean_effect']:.3f}")
print(f"  Mechanism: {optimal['mechanism']}")

print("\nNeurotransmitter Hypotheses:")
for nt, data in mech_analysis['neurotransmitter_hypothesis'].items():
    print(f"\n  {nt.capitalize()}:")
    print(f"    Evidence: {data['evidence']}")
    print(f"    Mechanism: {data['mechanism']}")
    print(f"    Confidence: {data['confidence']}")

if 'network_dynamics' in mech_analysis:
    print("\nNetwork Dynamics (from fMRI):")
    net = mech_analysis['network_dynamics']
    print(f"  Integration change: {net['mean_integration_change']:+.3f}")
    print(f"  Interpretation: {net['interpretation']}")
    print(f"  Key connections:")
    for conn in net['key_connections']:
        print(f"    - {conn}")

print("\n" + "="*80)
print("END OF COMPREHENSIVE REPORT")
print("="*80 + "\n")
