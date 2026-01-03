"""
Full production test: Generate one real mathematical discovery
"""

from autonomous_math_discovery_production import get_production_system

print("🔬 Testing PRODUCTION Autonomous Math Discovery System")
print("=" * 60)

system = get_production_system()

print(f"\n📚 Available domains: {', '.join(system.domains)}")
print(f"🔮 Sacred numbers: {system.sacred_numbers}")

# Generate ONE discovery with real AI
domain = "consciousness_mathematics"
print(f"\n🎯 Generating discovery for: {domain}")
print("⏳ This will call GPT-5 and Claude Opus 4.1 (30-60 seconds)...")

try:
    discovery = system.create_discovery_with_ai(domain)
    
    print("\n✅ DISCOVERY GENERATED!")
    print("=" * 60)
    print(f"📝 ID: {discovery.id}")
    print(f"🏷️  Title: {discovery.title}")
    print(f"💡 Intuition: {discovery.intuition}")
    print(f"\n🤖 God Machine Score: {discovery.god_machine_score:.3f}")
    print(f"🧠 MagAI Consensus: {discovery.mag_ai_consensus:.3f}")
    print(f"📊 Confidence: {discovery.confidence:.3f}")
    print(f"🏷️  Tags: {', '.join(discovery.tags)}")
    
    if discovery.gpt5_analysis:
        print(f"\n📐 GPT-5 Formalization:")
        print(discovery.gpt5_analysis[:200] + "..." if len(discovery.gpt5_analysis) > 200 else discovery.gpt5_analysis)
    
    if discovery.claude_analysis:
        print(f"\n🧪 Claude Critique:")
        print(discovery.claude_analysis[:200] + "..." if len(discovery.claude_analysis) > 200 else discovery.claude_analysis)
    
    print(f"\n🔷 Tralse Encoding: {discovery.tralse_encoding}")
    
    # Save it
    system.save_to_database(discovery)
    print(f"\n💾 Saved to: discoveries/{discovery.id}.json")
    
    print("\n" + "=" * 60)
    print("✨ PRODUCTION SYSTEM FULLY OPERATIONAL!")
    
except Exception as e:
    print(f"\n❌ ERROR: {e}")
    import traceback
    traceback.print_exc()
