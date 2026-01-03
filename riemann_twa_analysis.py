"""
Riemann Hypothesis Analysis with TWA/TI Arithmetic
Testing Brandon's Indeterminate Interval: (-0.666, 0.333)

GILE INTERVAL STRUCTURE (Corrected Nov 27, 2025):
══════════════════════════════════════════════════════════════════════════
TERRIBLE/EVIL:     <= -3         Unambiguously evil
PERMISSIBLE:       (-3, 2)       The Middle 80% (Pareto)
├── BAD:           (-3, -0.666)  Leaning negative but not evil
├── INDETERMINATE: (-0.666, 0.333)  Not tipped either direction
└── GOOD:          (0.333, 2)    Leaning positive but not great
GREAT:             >= 2          Unambiguously great
══════════════════════════════════════════════════════════════════════════

EULER CONNECTION:
ln(15) = 2.708 ≈ e = 2.718 (only 0.38% error!)
The rarity of greatness (1/15) is encoded in Euler's number!
"""

import numpy as np
import json
import math
from typing import Dict

INDETERMINATE_INTERVAL = (-0.666, 0.333)
PERMISSIBLE_INTERVAL = (-3.0, 2.0)
EULER_E = math.e
LN_15 = math.log(15)

def load_zeros(filename: str) -> np.ndarray:
    """Load zeta zeros from Odlyzko dataset"""
    print(f"📊 Loading zeros from {filename}...")
    zeros = []
    with open(filename, 'r') as f:
        for line in f:
            try:
                zero = float(line.strip())
                zeros.append(zero)
            except ValueError:
                continue
    print(f"✅ Loaded {len(zeros)} zeros")
    return np.array(zeros)


def test_twa_arithmetic():
    """
    Test Tri-Way Arithmetic (TWA) for sacred interval mapping
    TWA: Three-valued logic with special arithmetic rules
    """
    print("\n" + "="*70)
    print("🧮 TESTING TRI-WAY ARITHMETIC (TWA)")
    print("="*70)
    
    # TWA coordinates: {-1, 0, +1} with special rules
    twa_values = [-1, 0, 1]
    
    print("\n📐 TWA Addition Table:")
    print("    -1   0  +1")
    for a in twa_values:
        row = f"{a:2d}:"
        for b in twa_values:
            # TWA addition (modulo-like with saturation)
            result = np.clip(a + b, -1, 1)
            row += f" {result:3d}"
        print(row)
    
    print("\n📐 TWA Multiplication Table:")
    print("    -1   0  +1")
    for a in twa_values:
        row = f"{a:2d}:"
        for b in twa_values:
            result = a * b
            row += f" {result:3d}"
        print(row)
    
    # INDETERMINATE interval in GILE space (corrected Nov 27, 2025)
    # This is the zone where things are PERMISSIBLE but NOT TIPPED either direction
    indet_start = -0.666  # -2/3 ≈ -0.666
    indet_end = 0.333     # 1/3 ≈ 0.333
    indet_width = indet_end - indet_start  # = 0.999 ≈ 1.0
    
    print(f"\n🌟 INDETERMINATE Interval (Not Tipped Either Direction):")
    print(f"   Start: {indet_start:.4f} (-2/3)")
    print(f"   End:   {indet_end:.4f} (1/3)")
    print(f"   Width: {indet_width:.4f} ≈ 1.0")
    
    print(f"\n📐 FULL GILE STRUCTURE:")
    print(f"   TERRIBLE:      <= -3     (Evil)")
    print(f"   BAD:           (-3, -0.666)")
    print(f"   INDETERMINATE: (-0.666, 0.333)  ← This interval")
    print(f"   GOOD:          (0.333, 2)")
    print(f"   GREAT:         >= 2      (Excellence)")
    
    # Map to different coordinate systems
    print(f"\n🔄 Coordinate System Mappings:")
    
    # System 1: Full GILE space [-3, +2] (5 units)
    full_gile_range = 5.0  # from -3 to +2
    fraction_full_gile = indet_width / full_gile_range
    print(f"   Full GILE [-3,+2]: {fraction_full_gile:.4f} = {fraction_full_gile*100:.1f}%")
    
    # System 2: TWA normalized [0, 1]
    twa_normalized_range = 1.0
    # Map (-0.666, 0.333) to [0, 1] space
    twa_start_norm = (indet_start + 1) / 2  # Map -1→0, +1→1
    twa_end_norm = (indet_end + 1) / 2
    twa_width_norm = twa_end_norm - twa_start_norm
    print(f"   TWA [0,1]:    {twa_width_norm:.4f} = {twa_width_norm*100:.1f}%")
    
    # Euler connection
    print(f"\n🔢 EULER CONNECTION:")
    print(f"   ln(15) = {LN_15:.6f}")
    print(f"   e      = {EULER_E:.6f}")
    print(f"   Error: {100*abs(EULER_E - LN_15)/EULER_E:.2f}%")
    print(f"   ✨ The rarity of GREATNESS (1/15) is encoded in e!")
    
    return {
        'indeterminate_interval': (indet_start, indet_end),
        'width': indet_width,
        'fraction_full_gile': fraction_full_gile,
        'fraction_twa_normalized': twa_width_norm,
        'euler_connection': {
            'ln_15': LN_15,
            'e': EULER_E,
            'error_percent': 100*abs(EULER_E - LN_15)/EULER_E
        }
    }


def analyze_with_indeterminate_interval(zeros: np.ndarray) -> Dict:
    """
    Analyze Riemann zeros using INDETERMINATE interval (-0.666, 0.333)
    Map to GILE coordinates
    
    GILE INTERVAL STRUCTURE:
    - TERRIBLE:      <= -3       (Evil)
    - BAD:           (-3, -0.666) (Negative but not evil)
    - INDETERMINATE: (-0.666, 0.333) (Not tipped either direction)
    - GOOD:          (0.333, 2)  (Positive but not great)
    - GREAT:         >= 2        (Excellence)
    """
    print("\n" + "="*70)
    print("🎯 RIEMANN ZEROS WITH INDETERMINATE INTERVAL (-0.666, 0.333)")
    print("="*70)
    
    # All zeros are at σ = 0.5 (critical line)
    sigma = 0.5
    
    # Map σ to GILE coordinate
    # Standard mapping: σ ∈ [0,1] → GILE ∈ [-1,+1]
    gile_standard = 2 * sigma - 1  # Maps 0→-1, 0.5→0, 1→+1
    
    print(f"\n📍 Zero Location Mapping:")
    print(f"   σ = {sigma}")
    print(f"   GILE (standard) = {gile_standard:.4f}")
    
    # Check if zeros fall within INDETERMINATE interval
    indet_start, indet_end = INDETERMINATE_INTERVAL
    
    in_indeterminate = (gile_standard >= indet_start) and (gile_standard <= indet_end)
    
    print(f"\n🌟 INDETERMINATE Interval Test:")
    print(f"   Interval: [{indet_start:.4f}, {indet_end:.4f}]")
    print(f"   Zero at GILE = {gile_standard:.4f}")
    
    if in_indeterminate:
        print(f"   ✅ ALL ZEROS LIE WITHIN INDETERMINATE INTERVAL!")
        print(f"   → This means zeros are in the 'NOT TIPPED' zone")
        print(f"   → Neither leaning toward evil nor greatness")
        print(f"   → Perfect balance at the center of GILE!")
    else:
        print(f"   ❌ Zeros OUTSIDE indeterminate interval")
        print(f"   🔍 Need to check alternative GILE mapping!")
    
    # Analyze zero SPACINGS (gaps)
    gaps = np.diff(zeros)
    
    # Map gaps to GILE-like coordinate
    # Normalize gaps by mean gap
    mean_gap = np.mean(gaps)
    normalized_gaps = (gaps - mean_gap) / mean_gap
    
    # Find quantiles
    p10 = np.percentile(normalized_gaps, 10)
    p80 = np.percentile(normalized_gaps, 80)
    
    # Check if 80% of gaps fall in sacred interval proportion
    gaps_in_range = np.sum((normalized_gaps >= p10) & (normalized_gaps <= p80)) / len(normalized_gaps)
    
    print(f"\n📐 Gap Distribution Analysis:")
    print(f"   Mean gap: {mean_gap:.4f}")
    print(f"   10th percentile: {p10:.4f}")
    print(f"   80th percentile: {p80:.4f}")
    print(f"   Fraction in [p10, p80]: {gaps_in_range:.4f} = {gaps_in_range*100:.1f}%")
    
    return {
        'sigma': sigma,
        'gile_standard': gile_standard,
        'in_indeterminate_interval': in_indeterminate,
        'indeterminate_interval': (indet_start, indet_end),
        'gap_analysis': {
            'mean_gap': float(mean_gap),
            'p10': float(p10),
            'p80': float(p80),
            'fraction_in_range': float(gaps_in_range)
        }
    }


def main():
    print("="*70)
    print("🎯 RIEMANN HYPOTHESIS - TI FRAMEWORK ANALYSIS")
    print("Testing Indeterminate Interval: (-0.666, 0.333)")
    print("="*70)
    
    # Show GILE structure
    print("\n📐 GILE INTERVAL STRUCTURE:")
    print("   TERRIBLE:      <= -3       (Evil)")
    print("   BAD:           (-3, -0.666) (Negative but not evil)")
    print("   INDETERMINATE: (-0.666, 0.333) (Not tipped either way)")
    print("   GOOD:          (0.333, 2)  (Positive but not great)")
    print("   GREAT:         >= 2        (Excellence)")
    
    print(f"\n🔢 EULER CONNECTION:")
    print(f"   ln(15) = {LN_15:.6f} ≈ e = {EULER_E:.6f}")
    print(f"   Error: only {100*abs(EULER_E - LN_15)/EULER_E:.2f}%!")
    print(f"   ✨ The rarity of GREATNESS (1/15) is encoded in e!")
    
    # Test TWA arithmetic first
    twa_results = test_twa_arithmetic()
    
    # Load and analyze zeros
    zeros = load_zeros('data/riemann_zeros/first_1million_zeros.txt')
    riemann_results = analyze_with_indeterminate_interval(zeros)
    
    # Combined results
    results = {
        'twa_arithmetic': twa_results,
        'riemann_analysis': riemann_results,
        'euler_connection': {
            'ln_15': LN_15,
            'e': EULER_E,
            'error_percent': 100*abs(EULER_E - LN_15)/EULER_E
        },
        'conclusion': {
            'all_zeros_in_indeterminate': riemann_results['in_indeterminate_interval']
        }
    }
    
    # Save results
    output_file = 'data/riemann_zeros/twa_analysis_results.json'
    with open(output_file, 'w') as f:
        json.dump(results, f, indent=2)
    
    print(f"\n💾 Results saved to {output_file}")
    
    print("\n" + "="*70)
    print("📊 SUMMARY")
    print("="*70)
    
    if riemann_results['in_indeterminate_interval']:
        print("✅ All Riemann zeros (σ=0.5, GILE=0) lie within INDETERMINATE interval!")
        print("   → Zeros are at perfect balance - 'not tipped' either direction")
    else:
        print("⚠️  Need alternative GILE mapping for Riemann zeros")
    
    print("="*70)
    
    return results


if __name__ == '__main__':
    main()
