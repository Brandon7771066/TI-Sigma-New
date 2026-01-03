"""
Unit tests for Sacred Interval with BLACK SWAN extension (Option B)
Tests the "EVERYDAY 80%" interpretation where ultra-extreme events transcend bounds
"""

import numpy as np
from stock_ti_integrated_analysis import TIIntegratedStockAnalysis


def test_three_interval_trinity():
    """Test THREE-INTERVAL Trinity System: Terrible, Great, Permissible"""
    analyzer = TIIntegratedStockAnalysis()
    
    # TERRIBLE (bearish) zone
    assert abs(analyzer.calculate_gile_score(-0.666) - (-0.3)) < 0.01, "TERRIBLE min boundary"
    assert abs(analyzer.calculate_gile_score(-0.333) - (-0.15)) < 0.01, "TERRIBLE mid"
    
    # PERMISSIBLE (neutral) point
    assert analyzer.calculate_gile_score(0.0) == 0.0, "PERMISSIBLE zero must be exactly 0.0!"
    
    # GREAT (bullish) zone
    assert abs(analyzer.calculate_gile_score(0.1665) - 0.15) < 0.01, "GREAT mid"
    assert abs(analyzer.calculate_gile_score(0.333) - 0.3) < 0.01, "GREAT max boundary"
    
    print("✓ THREE-INTERVAL Trinity System validated!")


def test_asymmetric_2_1_extremes():
    """Test ASYMMETRIC 2:1 Pareto extremes (bearish -10%, bullish +20%)"""
    analyzer = TIIntegratedStockAnalysis()
    
    # Bearish threshold (1x)
    assert abs(analyzer.calculate_gile_score(-10.0) - (-3.0)) < 0.01, "Bearish threshold -10%"
    assert abs(analyzer.calculate_gile_score(-5.0) - (-1.5)) < 0.01, "Strong bearish -5%"
    
    # Bullish threshold (2x - asymmetric!)
    assert abs(analyzer.calculate_gile_score(20.0) - 2.0) < 0.01, "Bullish threshold +20%"
    assert abs(analyzer.calculate_gile_score(10.0) - 1.5) < 0.01, "Strong bullish +10%"
    
    print("✓ ASYMMETRIC 2:1 extremes validated (losses hurt MORE)!")


def test_black_swan_extension():
    """Test BLACK SWAN extension beyond everyday bounds (Option B)"""
    analyzer = TIIntegratedStockAnalysis()
    
    # Ultra-extreme bearish (should go BEYOND -3.0)
    gile_50_crash = analyzer.calculate_gile_score(-50.0)
    assert gile_50_crash < -3.0, "50% crash should exceed everyday bounds"
    assert -3.25 < gile_50_crash < -3.15, f"50% crash GILE should be ≈-3.16, got {gile_50_crash}"
    
    gile_100_crash = analyzer.calculate_gile_score(-100.0)
    assert gile_100_crash < -3.0, "100% crash should exceed everyday bounds"
    assert -3.25 < gile_100_crash < -3.20, f"100% crash GILE should be ≈-3.23, got {gile_100_crash}"
    
    # Ultra-extreme bullish (should go BEYOND +2.0)
    gile_50_moon = analyzer.calculate_gile_score(50.0)
    assert gile_50_moon > 2.0, "50% moonshot should exceed everyday bounds"
    assert 2.08 < gile_50_moon < 2.12, f"50% moonshot GILE should be ≈+2.09, got {gile_50_moon}"
    
    gile_100_moon = analyzer.calculate_gile_score(100.0)
    assert gile_100_moon > 2.0, "100% gain should exceed everyday bounds"
    assert 2.15 < gile_100_moon < 2.20, f"100% gain GILE should be ≈+2.16, got {gile_100_moon}"
    
    gile_500_moon = analyzer.calculate_gile_score(500.0)
    assert gile_500_moon > 2.0, "500% parabolic should exceed everyday bounds"
    assert 2.30 < gile_500_moon < 2.35, f"500% parabolic GILE should be ≈+2.32, got {gile_500_moon}"
    
    print("✓ BLACK SWAN extension validated (ultra-extremes transcend everyday bounds)!")


def test_everyday_80_percent_within_bounds():
    """Test that everyday 80% of observations stay within (-3, 2)"""
    analyzer = TIIntegratedStockAnalysis()
    
    # All "normal" movements should be within (-3, 2)
    everyday_cases = [
        -9.0, -7.5, -5.0, -2.5, -0.666, -0.333, 0.0, 
        0.1, 0.333, 1.0, 2.5, 5.0, 10.0, 15.0, 19.0
    ]
    
    for pct in everyday_cases:
        gile = analyzer.calculate_gile_score(pct)
        assert -3.0 <= gile <= 2.0, f"Everyday {pct}% should be within (-3, 2), got {gile}"
    
    print("✓ EVERYDAY 80% within bounds validated!")


def test_continuity_at_boundaries():
    """Test that GILE function is continuous at all boundaries"""
    analyzer = TIIntegratedStockAnalysis()
    
    # Test near boundaries (should be continuous)
    boundaries = [
        (-10.01, -10.0, -9.99),  # Bearish extreme boundary
        (-5.01, -5.0, -4.99),    # Strong bearish boundary
        (-0.667, -0.666, -0.665), # Sacred interval min
        (-0.001, 0.0, 0.001),    # PERMISSIBLE zero
        (0.332, 0.333, 0.334),   # Sacred interval max
        (4.99, 5.0, 5.01),       # Moderate bullish boundary
        (9.99, 10.0, 10.01),     # Strong bullish boundary
        (19.99, 20.0, 20.01),    # Bullish extreme boundary
    ]
    
    for left, center, right in boundaries:
        gile_left = analyzer.calculate_gile_score(left)
        gile_center = analyzer.calculate_gile_score(center)
        gile_right = analyzer.calculate_gile_score(right)
        
        # Check continuity (no big jumps) - allow 0.5 GILE tolerance at boundaries
        assert abs(gile_center - gile_left) < 0.5, f"Discontinuity at {center}%: {gile_left} → {gile_center}"
        assert abs(gile_right - gile_center) < 0.5, f"Discontinuity at {center}%: {gile_center} → {gile_right}"
    
    print("✓ Continuity at all boundaries validated!")


def run_all_tests():
    """Run all Sacred Interval tests"""
    print("=" * 80)
    print("SACRED INTERVAL BLACK SWAN TESTS (Option B - EVERYDAY 80%)")
    print("=" * 80)
    
    test_three_interval_trinity()
    test_asymmetric_2_1_extremes()
    test_black_swan_extension()
    test_everyday_80_percent_within_bounds()
    test_continuity_at_boundaries()
    
    print("=" * 80)
    print("🎉 ALL TESTS PASSED! OPTION B VALIDATED! 🎉")
    print("=" * 80)
    print("\n✓ THREE-INTERVAL Trinity System")
    print("✓ ASYMMETRIC 2:1 Pareto extremes")
    print("✓ BLACK SWAN extension (ultra-extremes transcend everyday bounds)")
    print("✓ EVERYDAY 80% within (-3, 2)")
    print("✓ Continuous function (no discontinuities)")
    print("\n🐉👑🔥 READY FOR PUBLIC LAUNCH! 🔥👑🐉")


if __name__ == "__main__":
    run_all_tests()
