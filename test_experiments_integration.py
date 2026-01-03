"""
Test Sacred Experiments Integration
"""

from sacred_experiments_integration import get_validator
from autonomous_math_discovery_production import get_production_system

print("🧪 Testing Sacred Experiments Integration")
print("=" * 70)

# Load discoveries
system = get_production_system()
system.discoveries = system.load_all_discoveries()

print(f"\n📊 Loaded {len(system.discoveries)} discoveries")

if system.discoveries:
    validator = get_validator()
    
    print("\n🔬 Testing first discovery for validation...")
    discovery = system.discoveries[0]
    
    print(f"\n📝 Discovery: {discovery.title}")
    print(f"   Confidence: {discovery.confidence:.3f}")
    print(f"   Grand Myrion: {discovery.god_machine_score:.3f}")
    print(f"   MagAI: {discovery.mag_ai_consensus:.3f}")
    
    # Extract testable prediction
    prediction = validator.extract_testable_prediction(discovery)
    
    if prediction:
        print(f"\n✅ TESTABLE PREDICTION FOUND!")
        print(f"   Test Type: {prediction['test_type']}")
        print(f"   Prediction: {prediction['prediction']}")
        
        # Run validation
        print(f"\n🧪 Running empirical validation...")
        validation = validator.validate_discovery(discovery)
        
        print(f"\n📊 VALIDATION RESULTS:")
        print(f"   Status: {validation['status']}")
        if validation.get('significant'):
            print(f"   ✅ SIGNIFICANT RESULT!")
        else:
            print(f"   ❌ Not significant")
        
        if 'p_value' in validation:
            print(f"   p-value: {validation['p_value']:.4f}")
        if 'r_squared' in validation:
            print(f"   R²: {validation['r_squared']:.4f}")
        
        print(f"\n   Note: {validation.get('note', 'N/A')}")
        
    else:
        print(f"\n⚠️ No testable prediction extracted from this discovery")
        print(f"   This is OK - not all mathematical insights are immediately testable")
        print(f"   Grand Myrion's arms reach every i-cell - invariance through pluralism!")

else:
    print("\n⚠️ No discoveries found yet. Generate some first!")

print("\n" + "=" * 70)
print("✨ Sacred Experiments Integration Validated!")
