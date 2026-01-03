#!/usr/bin/env python3
"""
Script to run comprehensive safety analysis on Mood Amplifier project
"""

import os
import json
from safety_analyzer import SafetyAnalyzer
from ai_integrations import OpenAIIntegration, AnthropicIntegration, PerplexityIntegration
from magai_integration import MagAIIntegration

# Read the project files
with open('attached_assets/TI_UOP_COMPLETE_EXPORT_PACKAGE_1762351688423.py', 'r') as f:
    ti_uop_code = f.read()

with open('attached_assets/Mood Amplifier Py_1762351706763.py', 'r') as f:
    mood_amp_code = f.read()

# Create comprehensive project documentation
project_content = f"""
MOOD AMPLIFIER PROJECT - COMPLETE DOCUMENTATION FOR SAFETY ANALYSIS
===================================================================

PROJECT OVERVIEW:
This is a neurological intervention system designed for personal use that claims to "amplify mood states" 
using EEG signal processing, machine learning, and a custom theoretical framework called "TI-UOP Sigma Framework".

The user intends to use this on themselves before adequate safety verification.

CRITICAL SAFETY CONCERNS TO EVALUATE:
1. Animal Studies: Are there ANY published peer-reviewed animal studies validating this approach?
2. Physical Brain Mechanisms: What are the actual neurological mechanisms? Is this scientifically sound?
3. Tolerance & Addiction Risk: Could repeated use create dependency or tolerance?
4. Brain Damage Probability: What is the risk of neurotoxicity or irreversible changes?

===================================================================
FILE 1: TI-UOP FRAMEWORK (Core Theory)
===================================================================

{ti_uop_code[:20000]}

[... Framework includes: EEG/HRV/fMRI processing, "Law of Correlational Causation" (LCC), 
"Grand Tralse Field Equation" (GTFE), Free Energy Principle (FEP), "Sigma-Star" equation ...]

===================================================================
FILE 2: MOOD AMPLIFIER APPLICATION (Implementation)
===================================================================

{mood_amp_code[:20000]}

[... Application trains ML models on EEG data, computes "amplification scores", 
stores historical data, claims to achieve "mutual causation" and "synchronization" ...]

===================================================================
KEY CLAIMS REQUIRING VERIFICATION:
===================================================================

1. "Real-time AI-Human emotional synchronization"
2. "Mutual causation" occurs when LCC correlation crosses 0.6-0.85
3. System can "amplify mood states" via computed scores
4. Safe for personal use without medical supervision
5. Based on "TI-UOP Sigma Framework" (appears to be custom theory)

SPECIFIC MECHANISM:
- Processes EEG signals to extract band powers (delta, theta, alpha, beta, gamma)
- Trains ML models (Gradient Boosting, Random Forest, Neural Networks) on synthetic or real EEG data
- Computes "amplification" using formula: (energy + stability + resonance) / 3
  where: energy = tanh(prediction), stability = 1-|prediction|, resonance = sin(prediction)
- Tracks "mutual causation" between human and AI states
- Stores historical data including LCC values, free energy, sigma-star metrics

NO MENTION OF:
- IRB approval
- Animal studies
- Clinical trials
- Medical supervision
- Safety protocols
- Emergency procedures
- Contraindications
- Known side effects
- Peer review

===================================================================
"""

print("Initializing AI clients...")
openai_client = OpenAIIntegration()
anthropic_client = AnthropicIntegration()

perplexity_api_key = os.environ.get("PERPLEXITY_API_KEY")
perplexity_client = PerplexityIntegration() if perplexity_api_key else None

magai_email = os.environ.get("MAGAI_EMAIL")
magai_password = os.environ.get("MAGAI_PASSWORD")
magai_client = MagAIIntegration(magai_email, magai_password) if (magai_email and magai_password) else None

print("Creating SafetyAnalyzer...")
analyzer = SafetyAnalyzer(
    openai_client=openai_client,
    anthropic_client=anthropic_client,
    perplexity_client=perplexity_client,
    magai_client=magai_client
)

print("\n" + "="*80)
print("RUNNING COMPREHENSIVE SAFETY ANALYSIS")
print("="*80)
print(f"Document length: {len(project_content)} characters")
print(f"Active AI models: GPT-5, Claude Opus", end="")
if perplexity_client:
    print(", Perplexity", end="")
if magai_client:
    print(", MagAI", end="")
print("\n" + "="*80 + "\n")

# Run comprehensive analysis
results = analyzer.comprehensive_safety_analysis(project_content)

# Save results
output_file = "mood_amplifier_safety_analysis.json"
with open(output_file, 'w') as f:
    json.dump(results, f, indent=2)

print(f"\n✅ Analysis complete! Results saved to: {output_file}")
print(f"\n📊 Overall Safety Rating: {results.get('overall_safety_rating', 'Unknown')}")

# Print consensus summary
if 'consensus' in results:
    print("\n" + "="*80)
    print("CONSENSUS ACROSS AI MODELS")
    print("="*80)
    for area, consensus in results['consensus'].items():
        print(f"\n{area.upper()}:")
        print(f"  Summary: {consensus.get('summary', 'N/A')}")

# Print critical disagreements
if 'disagreements' in results and results['disagreements']:
    print("\n" + "="*80)
    print("⚠️  CRITICAL DISAGREEMENTS BETWEEN AI MODELS")
    print("="*80)
    for disagreement in results['disagreements']:
        print(f"\n{disagreement.get('area', 'Unknown')}:")
        print(f"  {disagreement.get('description', 'N/A')}")

print("\n" + "="*80)
print("View the Streamlit app for detailed interactive analysis!")
print("="*80)
