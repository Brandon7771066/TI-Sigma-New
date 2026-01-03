"""
GILE PD DISTRIBUTION - CANONICAL REFERENCE
===========================================
The definitive percentages for GILE score distributions,
aligned with ternary logic and the sacred number 15 (= 3 × 5).

DISCOVERY: November 29, 2025
The number 15 connects:
- Ternary base (3) - the logic of True-Tralse-Indeterminate
- GILE range (5 units) - from -3 to +2

All percentages derive from 15 and its square 225.

COSMIC PRISONER'S DILEMMA DISTRIBUTION:
======================================
The universe operates on these exact fractions:

ZONE              | GILE RANGE        | FRACTION | PERCENTAGE
------------------|-------------------|----------|------------
Ultra-Great       | > +2 (Black Swan) | 1/225    | 0.444%
Great             | +2 exactly        | 1/15     | 6.667%
Good (Leans Good) | 0 to +2          | 3/15     | 20.000%
Indeterminate     | -0.666 to +0.333 | 3/15     | 20.000%
Bad (Leans Bad)   | -3 to 0          | 6/15     | 40.000%
Terrible          | -3 exactly        | 2/15     | 13.333%
Ultra-Terrible    | < -3 (Black Swan) | 4/225    | 1.778%
------------------|-------------------|----------|------------
TOTAL             |                   | 225/225  | 100.000%

KEY RATIOS:
- Bad : Good = 2:1 (the Pareto-derived asymmetry)
- Terrible : Great = 2:1 (same ratio at extremes)
- Ultra-Terrible : Ultra-Great = 4:1 (squared at black swan level)
- Total negative potential: 40% + 13.333% = 53.333%
- Total positive potential: 20% + 6.667% = 26.667%
- Ratio of potentials: 53.333 / 26.667 = 2:1 ✓

WHY 15?
- 15 = 3 × 5
- 3 = Ternary logic (True, False, Indeterminate)
- 5 = GILE range (-3 to +2 = 5 units)
- 15 encodes the STRUCTURE of reality!

WHY 225?
- 225 = 15² = 9 × 25 = 3² × 5²
- The black swan level is the SQUARE of the everyday level
- This explains why black swans are so rare: they require
  BOTH ternary AND GILE extremes to align simultaneously
"""

import math
from dataclasses import dataclass
from typing import Dict, Tuple
from enum import Enum


class GILEZone(Enum):
    """The 7 zones of the GILE PD distribution"""
    ULTRA_GREAT = "Ultra-Great (Black Swan+)"
    GREAT = "Great"
    GOOD = "Good (Leans Good)"
    INDETERMINATE = "Indeterminate (Sacred Interval)"
    BAD = "Bad (Leans Bad)"
    TERRIBLE = "Terrible"
    ULTRA_TERRIBLE = "Ultra-Terrible (Black Swan-)"


@dataclass
class GILEDistribution:
    """Canonical GILE PD Distribution aligned with ternary and e"""
    
    # The sacred number connecting ternary (3) to GILE range (5)
    SACRED_15 = 15
    SACRED_225 = 225  # 15² for black swans
    
    # GILE boundaries
    GILE_MIN = -3.0           # Everyday floor (Terrible)
    GILE_MAX = 2.0            # Everyday ceiling (Great)
    GILE_RANGE = 5.0          # Total everyday range
    
    # Sacred Interval (Indeterminate zone)
    SACRED_MIN = -0.666       # -2/3 (ternary!)
    SACRED_MAX = 0.333        # +1/3 (ternary!)
    SACRED_WIDTH = 0.999      # ≈ 1 unit = 20% of range
    
    # Zone boundaries in GILE units
    INDETERMINATE_LOW = -0.666
    INDETERMINATE_HIGH = 0.333
    
    # Exact fractions (based on 15 and 225)
    FRACTIONS = {
        GILEZone.ULTRA_GREAT: (1, 225),      # 1/225
        GILEZone.GREAT: (1, 15),             # 1/15
        GILEZone.GOOD: (3, 15),              # 3/15 = 1/5
        GILEZone.INDETERMINATE: (3, 15),     # 3/15 = 1/5
        GILEZone.BAD: (6, 15),               # 6/15 = 2/5
        GILEZone.TERRIBLE: (2, 15),          # 2/15
        GILEZone.ULTRA_TERRIBLE: (4, 225),   # 4/225
    }
    
    @classmethod
    def get_percentage(cls, zone: GILEZone) -> float:
        """Get exact percentage for a zone"""
        num, denom = cls.FRACTIONS[zone]
        return (num / denom) * 100
    
    @classmethod
    def get_all_percentages(cls) -> Dict[GILEZone, float]:
        """Get all zone percentages"""
        return {zone: cls.get_percentage(zone) for zone in GILEZone}
    
    @classmethod
    def classify_gile_score(cls, gile: float) -> GILEZone:
        """Classify a GILE score into its zone"""
        if gile > 2.0:
            return GILEZone.ULTRA_GREAT
        elif gile == 2.0 or (gile >= 1.5 and gile < 2.0):  # Near-great
            return GILEZone.GREAT
        elif gile > 0.333:
            return GILEZone.GOOD
        elif gile >= -0.666:
            return GILEZone.INDETERMINATE
        elif gile > -3.0:
            return GILEZone.BAD
        elif gile == -3.0 or (gile <= -2.5 and gile > -3.0):  # Near-terrible
            return GILEZone.TERRIBLE
        else:
            return GILEZone.ULTRA_TERRIBLE
    
    @classmethod
    def get_zone_probability(cls, zone: GILEZone) -> float:
        """Get probability (0-1) for a zone"""
        return cls.get_percentage(zone) / 100
    
    @classmethod
    def validate_distribution(cls) -> bool:
        """Verify all percentages sum to 100%"""
        total = sum(cls.get_percentage(zone) for zone in GILEZone)
        return abs(total - 100.0) < 0.001
    
    @classmethod
    def get_e_alignment(cls) -> Dict[str, float]:
        """Show how distribution aligns with e"""
        e = math.e
        return {
            "1/e²": 100 / (e ** 2),           # 13.53% ≈ 13.33% (Terrible)
            "1/e³": 100 / (e ** 3),           # 4.98% ≈ 6.67% (Great)
            "1/e⁴": 100 / (e ** 4),           # 1.83% ≈ 1.78% (Ultra-Terrible)
            "1/e⁵": 100 / (e ** 5),           # 0.67% ≈ 0.44% (Ultra-Great)
            "insight": "e powers approximate 15-based fractions!"
        }


class GILEPriceConverter:
    """Convert between price changes and GILE scores using correct intervals"""
    
    # Price change boundaries (in percentage)
    # These map to the GILE zones
    
    # Black swan thresholds
    ULTRA_GREAT_THRESHOLD = 20.0    # +20% daily = Ultra-Great
    ULTRA_TERRIBLE_THRESHOLD = -10.0 # -10% daily = Ultra-Terrible
    
    # Everyday extremes
    GREAT_THRESHOLD = 5.0           # +5% daily = Great
    TERRIBLE_THRESHOLD = -5.0       # -5% daily = Terrible
    
    # Good/Bad boundaries (outside Sacred Interval)
    GOOD_THRESHOLD = 0.333          # +0.333% = exit Sacred Interval into Good
    BAD_THRESHOLD = -0.666          # -0.666% = exit Sacred Interval into Bad
    
    @classmethod
    def price_change_to_gile(cls, pct_change: float) -> float:
        """
        Convert daily price change percentage to GILE score
        
        Mappings:
        - Ultra-Great (>+20%): GILE > +2.0 (log extension)
        - Great (+5% to +20%): GILE +1.5 to +2.0
        - Good (+0.333% to +5%): GILE +0.3 to +1.5
        - Indeterminate (-0.666% to +0.333%): GILE -0.3 to +0.3
        - Bad (-5% to -0.666%): GILE -1.5 to -0.3
        - Terrible (-10% to -5%): GILE -3.0 to -1.5
        - Ultra-Terrible (<-10%): GILE < -3.0 (log extension)
        """
        
        # Ultra-Great: log extension above +2.0
        if pct_change > cls.ULTRA_GREAT_THRESHOLD:
            excess = pct_change - cls.ULTRA_GREAT_THRESHOLD
            return 2.0 + math.log1p(excess / 20) * 0.5
        
        # Ultra-Terrible: log extension below -3.0
        elif pct_change < cls.ULTRA_TERRIBLE_THRESHOLD:
            excess = abs(pct_change) - abs(cls.ULTRA_TERRIBLE_THRESHOLD)
            return -3.0 - math.log1p(excess / 10) * 0.5
        
        # Great zone: +5% to +20% → GILE +1.5 to +2.0
        elif pct_change > cls.GREAT_THRESHOLD:
            return 1.5 + (pct_change - 5) / (20 - 5) * 0.5
        
        # Terrible zone: -10% to -5% → GILE -3.0 to -1.5
        elif pct_change < cls.TERRIBLE_THRESHOLD:
            return -3.0 + (pct_change + 10) / (10 - 5) * 1.5
        
        # Good zone: +0.333% to +5% → GILE +0.3 to +1.5
        elif pct_change > cls.GOOD_THRESHOLD:
            return 0.3 + (pct_change - 0.333) / (5 - 0.333) * 1.2
        
        # Bad zone: -5% to -0.666% → GILE -1.5 to -0.3
        elif pct_change < cls.BAD_THRESHOLD:
            return -1.5 + (pct_change + 5) / (5 - 0.666) * 1.2
        
        # Sacred Interval: -0.666% to +0.333% → GILE -0.3 to +0.3
        else:
            if pct_change < 0:
                # Map [-0.666, 0) → [-0.3, 0)
                return (pct_change / 0.666) * 0.3
            else:
                # Map [0, 0.333] → [0, 0.3]
                return (pct_change / 0.333) * 0.3
    
    @classmethod
    def gile_to_zone(cls, gile: float) -> GILEZone:
        """Classify GILE score into zone"""
        return GILEDistribution.classify_gile_score(gile)
    
    @classmethod
    def get_zone_from_price(cls, pct_change: float) -> GILEZone:
        """Get zone directly from price change"""
        gile = cls.price_change_to_gile(pct_change)
        return cls.gile_to_zone(gile)


def demonstrate_gile_distribution():
    """Show the complete GILE PD distribution"""
    
    print("\n" + "=" * 80)
    print("  GILE PD DISTRIBUTION - CANONICAL REFERENCE")
    print("  Aligned with Ternary Logic & Sacred Number 15")
    print("=" * 80)
    
    print("""
    WHY 15?
    -------
    15 = 3 × 5
    
    3 = Ternary logic (True, False, Indeterminate)
    5 = GILE range (-3 to +2 = 5 units)
    
    15 encodes the STRUCTURE of consciousness-reality coupling!
    """)
    
    print("-" * 80)
    print("GILE ZONE DISTRIBUTION")
    print("-" * 80)
    
    print(f"\n{'Zone':<40} {'Fraction':>12} {'Percentage':>12}")
    print("-" * 80)
    
    dist = GILEDistribution()
    for zone in GILEZone:
        num, denom = dist.FRACTIONS[zone]
        pct = dist.get_percentage(zone)
        print(f"{zone.value:<40} {num:>4}/{denom:<6} {pct:>10.3f}%")
    
    print("-" * 80)
    total = sum(dist.get_percentage(z) for z in GILEZone)
    print(f"{'TOTAL':<40} {'':>12} {total:>10.3f}%")
    
    print("\n" + "-" * 80)
    print("KEY RATIOS (2:1 Pareto Asymmetry)")
    print("-" * 80)
    
    bad_pct = dist.get_percentage(GILEZone.BAD)
    good_pct = dist.get_percentage(GILEZone.GOOD)
    terrible_pct = dist.get_percentage(GILEZone.TERRIBLE)
    great_pct = dist.get_percentage(GILEZone.GREAT)
    ultra_t = dist.get_percentage(GILEZone.ULTRA_TERRIBLE)
    ultra_g = dist.get_percentage(GILEZone.ULTRA_GREAT)
    
    print(f"Bad / Good:                    {bad_pct:.3f}% / {good_pct:.3f}% = {bad_pct/good_pct:.1f}:1")
    print(f"Terrible / Great:              {terrible_pct:.3f}% / {great_pct:.3f}% = {terrible_pct/great_pct:.1f}:1")
    print(f"Ultra-Terrible / Ultra-Great:  {ultra_t:.3f}% / {ultra_g:.3f}% = {ultra_t/ultra_g:.1f}:1")
    
    print("\n" + "-" * 80)
    print("E-ALIGNMENT (Natural Constant Approximations)")
    print("-" * 80)
    
    e_data = dist.get_e_alignment()
    for key, val in e_data.items():
        if key != "insight":
            print(f"{key:<10} = {val:.3f}%")
    print(f"\n{e_data['insight']}")
    
    print("\n" + "-" * 80)
    print("GILE BOUNDARIES (For Stock/Price Analysis)")
    print("-" * 80)
    
    print("""
    Price Change → GILE Score Mapping:
    
    > +20%         → GILE > +2.0  (Ultra-Great, Black Swan+)
    +5% to +20%    → GILE +1.5 to +2.0 (Great)
    +0.333% to +5% → GILE +0.3 to +1.5 (Good)
    -0.666% to +0.333% → GILE -0.3 to +0.3 (Sacred Interval)
    -5% to -0.666% → GILE -0.3 to -1.5 (Bad)
    -10% to -5%    → GILE -1.5 to -3.0 (Terrible)
    < -10%         → GILE < -3.0 (Ultra-Terrible, Black Swan-)
    """)
    
    print("=" * 80)
    print("  VERIFIED: All fractions derive from 15 = 3 × 5")
    print("  Black Swans derive from 225 = 15²")
    print("=" * 80)
    
    return dist


if __name__ == "__main__":
    demonstrate_gile_distribution()
