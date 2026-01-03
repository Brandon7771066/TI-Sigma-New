"""
Find the Correct GILE Range for 20% Sacred Interval
Testing different range assumptions
"""

import numpy as np

def test_gile_ranges():
    """
    Test different GILE range assumptions to find which gives 20%
    """
    sacred_start = -2/3
    sacred_end = 1/3
    sacred_width = sacred_end - sacred_start  # = 1.0
    
    target_fraction = 0.2  # 20% = 1/5
    
    print("="*70)
    print("🔍 FINDING CORRECT GILE RANGE FOR 20% SACRED INTERVAL")
    print("="*70)
    print(f"\nSacred interval: [{sacred_start:.4f}, {sacred_end:.4f}]")
    print(f"Sacred width: {sacred_width:.4f}")
    print(f"Target fraction: {target_fraction:.4f} = {target_fraction*100:.0f}%")
    
    print("\n" + "="*70)
    print("TESTING DIFFERENT GILE RANGES:")
    print("="*70)
    
    # Test different range assumptions
    test_cases = [
        ("Standard GILE", -1, 1),
        ("Extended GILE", -2, 2),
        ("5-Point GILE", -2.5, 2.5),
        ("Tripled GILE", -3, 3),
        ("Custom 1", -5/3, 5/3),
        ("Custom 2", -1.5, 1.5),
    ]
    
    matches = []
    
    for name, min_val, max_val in test_cases:
        total_range = max_val - min_val
        fraction = sacred_width / total_range
        
        # Check if within sacred interval
        in_range = (sacred_start >= min_val) and (sacred_end <= max_val)
        
        match = abs(fraction - target_fraction) < 0.01
        
        print(f"\n{name}:")
        print(f"  Range: [{min_val:.4f}, {max_val:.4f}]")
        print(f"  Total width: {total_range:.4f}")
        print(f"  Sacred fraction: {fraction:.4f} = {fraction*100:.1f}%")
        print(f"  Interval fits: {in_range}")
        
        if match:
            print(f"  ✅ MATCHES 20%! (difference: {abs(fraction - target_fraction):.6f})")
            matches.append((name, min_val, max_val, total_range))
        elif abs(fraction - target_fraction) < 0.05:
            print(f"  🟡 Close! (difference: {abs(fraction - target_fraction):.6f})")
    
    # Calculate what range WOULD give exactly 20%
    required_range = sacred_width / target_fraction
    required_min = -(required_range / 2)
    required_max = (required_range / 2)
    
    print("\n" + "="*70)
    print("📐 CALCULATED REQUIREMENT FOR EXACTLY 20%:")
    print("="*70)
    print(f"Required total range: {required_range:.4f}")
    print(f"Symmetric range: [{required_min:.4f}, {required_max:.4f}]")
    
    # Check if this is symmetric around 0
    if abs(required_min + required_max) < 0.001:
        print(f"✅ Symmetric around 0!")
    
    # Check what σ values this corresponds to
    # If GILE = 2*σ - 1 (standard mapping), then:
    # σ = (GILE + 1) / 2
    sigma_at_sacred_start = (sacred_start + 1) / 2
    sigma_at_sacred_end = (sacred_end + 1) / 2
    
    print(f"\n📍 Corresponding σ values (if GILE = 2σ - 1):")
    print(f"  At GILE = {sacred_start:.4f}: σ = {sigma_at_sacred_start:.4f}")
    print(f"  At GILE = {sacred_end:.4f}: σ = {sigma_at_sacred_end:.4f}")
    print(f"  Critical line σ = 0.5 → GILE = {2*0.5-1:.4f} ✓")
    
    # Alternative: Maybe GILE mapping is different?
    print(f"\n🔄 ALTERNATIVE MAPPINGS:")
    
    # Mapping 2: GILE = 5*(σ - 0.5)
    # This would map σ=0.5 → GILE=0, σ=0 → GILE=-2.5, σ=1 → GILE=2.5
    print(f"\nMapping: GILE = 5(σ - 0.5):")
    for sigma in [0, 0.5, 1]:
        gile = 5 * (sigma - 0.5)
        print(f"  σ = {sigma:.1f} → GILE = {gile:.4f}")
    print(f"  Range: [-2.5, 2.5], Total width: 5.0")
    print(f"  Sacred interval width 1.0 / 5.0 = 0.2 = 20% ✅✅✅")
    
    # Mapping 3: GILE ∈ {-2, -1, 0, 1, 2} (5 discrete values)
    print(f"\nDiscrete 5-valued GILE:")
    print(f"  Values: {{-2, -1, 0, 1, 2}}")
    print(f"  Sacred interval (-2/3, 1/3) contains: {{-1, 0}} (if rounding)")
    print(f"  OR continuous: 1.0 / 4.0 = 0.25 = 25% (close!)")
    
    print("\n" + "="*70)
    print("🎯 MOST LIKELY ANSWER:")
    print("="*70)
    print("GILE = 5(σ - 0.5), giving range [-2.5, +2.5]")
    print("Sacred interval (-2/3, 1/3) = 1.0 / 5.0 = 20% ✅")
    print("Critical line σ = 0.5 → GILE = 0 (Φ state)")
    print("="*70)
    
    return {
        'sacred_interval': (sacred_start, sacred_end),
        'sacred_width': sacred_width,
        'required_range': required_range,
        'recommended_gile_range': [-2.5, 2.5],
        'recommended_mapping': 'GILE = 5(σ - 0.5)',
        'matches': matches
    }

if __name__ == '__main__':
    results = test_gile_ranges()
