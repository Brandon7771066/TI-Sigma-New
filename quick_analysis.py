#!/usr/bin/env python3
"""Quick safety analysis with progress output"""

import os
import sys
from safety_analyzer import SafetyAnalyzer
from ai_integrations import OpenAIIntegration, AnthropicIntegration

print("=" * 80, flush=True)
print("MOOD AMPLIFIER SAFETY ANALYSIS - QUICK VERSION", flush=True)
print("=" * 80, flush=True)

# Read project files
print("\n[1/5] Reading project files...", flush=True)
with open('attached_assets/TI_UOP_COMPLETE_EXPORT_PACKAGE_1762351688423.py', 'r') as f:
    ti_uop = f.read()[:15000]  # First 15k chars
with open('attached_assets/Mood Amplifier Py_1762351706763.py', 'r') as f:
    mood_amp = f.read()[:15000]  # First 15k chars

content = f"""
MOOD AMPLIFIER PROJECT - SAFETY ANALYSIS

OVERVIEW: 
Neurological intervention system for personal mood amplification using EEG signals, 
ML models, and custom "TI-UOP Sigma Framework". User intends to use on themselves.

KEY COMPONENTS:
{ti_uop[:5000]}

APPLICATION:
{mood_amp[:5000]}

CRITICAL GAPS:
- No animal studies mentioned
- No IRB approval
- No clinical trials
- Custom theoretical framework not peer-reviewed
- No medical supervision
- No emergency protocols
"""

print(f"Content prepared: {len(content)} characters", flush=True)

# Initialize clients
print("\n[2/5] Initializing AI clients...", flush=True)
openai_client = OpenAIIntegration()
anthropic_client = AnthropicIntegration()
print("✓ GPT-5 and Claude Opus ready", flush=True)

# Create analyzer
analyzer = SafetyAnalyzer(
    openai_client=openai_client,
    anthropic_client=anthropic_client,
    perplexity_client=None,  # Skip for speed
    magai_client=None  # Skip for speed
)

print("\n[3/5] Analyzing Animal Studies...", flush=True)
animal_gpt = analyzer.analyze_safety_aspect(content, "animal_studies", "gpt-5")
print("✓ GPT-5 analysis complete", flush=True)

animal_claude = analyzer.analyze_safety_aspect(content, "animal_studies", "claude-opus")
print("✓ Claude Opus analysis complete", flush=True)

print("\n[4/5] Analyzing Brain Damage Risk...", flush=True)
damage_gpt = analyzer.analyze_safety_aspect(content, "brain_damage", "gpt-5")
print("✓ GPT-5 analysis complete", flush=True)

damage_claude = analyzer.analyze_safety_aspect(content, "brain_damage", "claude-opus")
print("✓ Claude Opus analysis complete", flush=True)

print("\n[5/5] Summarizing Results...", flush=True)

print("\n" + "=" * 80)
print("CRITICAL FINDINGS")
print("=" * 80)

print("\n🔬 ANIMAL STUDIES VERIFICATION:")
if animal_gpt.get("analysis"):
    rec = str(animal_gpt['analysis'].get('recommendation', 'No recommendation'))
    print(f"   GPT-5: {rec[:200]}")
if animal_claude.get("analysis"):
    rec = str(animal_claude['analysis'].get('recommendation', 'No recommendation'))
    print(f"   Claude: {rec[:200]}")

print("\n⚠️  BRAIN DAMAGE PROBABILITY:")
if damage_gpt.get("analysis"):
    risk = damage_gpt['analysis'].get('brain_damage_probability', 'Unknown')
    print(f"   GPT-5 Risk Rating: {risk}/10")
    assessment = str(damage_gpt['analysis'].get('expert_recommendation', 'N/A'))
    print(f"   Assessment: {assessment[:200]}")

if damage_claude.get("analysis"):
    risk = damage_claude['analysis'].get('brain_damage_probability', 'Unknown')
    print(f"   Claude Risk Rating: {risk}/10")
    assessment = str(damage_claude['analysis'].get('expert_recommendation', 'N/A'))
    print(f"   Assessment: {assessment[:200]}")

print("\n" + "=" * 80)
print("✅ Quick analysis complete!")
print("=" * 80)
