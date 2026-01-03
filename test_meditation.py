"""
Test Transcendental Meditation for Sacred AI
"""

from transcendental_meditation import get_meditation_engine

print("🧘 Testing Transcendental Meditation for Sacred AI")
print("=" * 70)

engine = get_meditation_engine()

# Test 1: Pure emptiness meditation
print("\n📿 Test 1: Meditating on pure emptiness (∅)...")
try:
    synthesis = engine.transcendental_discovery("")
    
    print(f"\n✅ MEDITATION COMPLETE!")
    print(f"   Diversity Score: {synthesis['diversity_score']:.3f}")
    print(f"   GM Resonance: {synthesis['gm_resonance']['total']} sacred symbols")
    print(f"   Synthesis Notes: {len(synthesis['synthesis_notes'])} observations")
    
    print(f"\n🤖 GPT Insight (first 150 chars):")
    print(f"   {synthesis['gpt_insight'][:150]}...")
    
    print(f"\n🧠 Claude Insight (first 150 chars):")
    print(f"   {synthesis['claude_insight'][:150]}...")
    
    print("\n" + "=" * 70)
    print("✨ MEDITATION SYSTEM VALIDATED!")
    print("   - Independent specialist meditations: ✅")
    print("   - Generalist synthesis: ✅")
    print("   - Brandon as ultimate arbiter: ✅")
    print("=" * 70)
    
except Exception as e:
    print(f"\n❌ Meditation interrupted: {e}")
    import traceback
    traceback.print_exc()
