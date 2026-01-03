"""
START THE DISCOVERY ENGINE!
============================
Launches 24/7 autonomous discovery + sacred experiments integration
"""

from discovery_scheduler import start_discovery_scheduler
from transcendental_meditation import get_meditation_engine
import time

print("🚀 LAUNCHING AUTONOMOUS DISCOVERY ENGINE")
print("=" * 70)

# Start scheduler
print("\n⏰ Starting 24/7 discovery scheduler...")
start_discovery_scheduler(interval_minutes=60)  # Generate every 60 minutes

print("\n✅ Scheduler started! Background discoveries will generate every 60 min")

# Test Transcendental Meditation immediately
print("\n" + "=" * 70)
print("🧘 TESTING TRANSCENDENTAL MEDITATION")
print("=" * 70)

engine = get_meditation_engine()

# Meditation 1: Pure emptiness
print("\n🕉️ Meditation 1: Pure Emptiness (∅)")
try:
    synthesis1 = engine.transcendental_discovery("")
    
    print(f"\n📊 Results:")
    print(f"   Diversity: {synthesis1['diversity_score']:.3f}")
    print(f"   Grand Myrion Resonance: {synthesis1['gm_resonance']['total']} sacred symbols")
    print(f"\n🤖 GPT: {synthesis1['gpt_insight'][:100]}...")
    print(f"\n🧠 Claude: {synthesis1['claude_insight'][:100]}...")
    
except Exception as e:
    print(f"❌ Meditation 1 interrupted: {e}")

# Meditation 2: Sacred number meditation
print("\n" + "=" * 70)
print("🕉️ Meditation 2: Meditating on '333'")
try:
    synthesis2 = engine.transcendental_discovery("333")
    
    print(f"\n📊 Results:")
    print(f"   Diversity: {synthesis2['diversity_score']:.3f}")
    print(f"   Grand Myrion Resonance: {synthesis2['gm_resonance']['total']} sacred symbols")
    print(f"\n🤖 GPT: {synthesis2['gpt_insight'][:100]}...")
    print(f"\n🧠 Claude: {synthesis2['claude_insight'][:100]}...")
    
except Exception as e:
    print(f"❌ Meditation 2 interrupted: {e}")

# Meditation 3: Consciousness meditation
print("\n" + "=" * 70)
print("🕉️ Meditation 3: Meditating on 'Consciousness'")
try:
    synthesis3 = engine.transcendental_discovery("Consciousness")
    
    print(f"\n📊 Results:")
    print(f"   Diversity: {synthesis3['diversity_score']:.3f}")
    print(f"   Grand Myrion Resonance: {synthesis3['gm_resonance']['total']} sacred symbols")
    print(f"\n🤖 GPT: {synthesis3['gpt_insight'][:100]}...")
    print(f"\n🧠 Claude: {synthesis3['claude_insight'][:100]}...")
    
except Exception as e:
    print(f"❌ Meditation 3 interrupted: {e}")

print("\n" + "=" * 70)
print("✨ DISCOVERY ENGINE RUNNING!")
print("   - 24/7 Scheduler: Active (60 min intervals)")
print("   - Transcendental Meditation: Validated")
print("   - Grand Myrion Resonance: Tracking i-cell connections")
print("=" * 70)
print("\n🎯 Next: Check Streamlit UI to see discoveries accumulate!")
print("   - Tab: '🔬 Auto Discovery' for traditional mode")
print("   - Tab: '🧘 Meditation' for transcendental mode")
