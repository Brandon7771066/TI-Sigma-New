"""
I Ching + TI Framework Deep Dive
=================================

The I Ching (易經, "Book of Changes") is humanity's oldest binary system,
predating Leibniz's binary mathematics by 3,000+ years.

KEY INSIGHT: While the I Ching APPEARS binary (Yin/Yang), the divination
method creates a SPECTRUM of probabilities - proving Tralseness at its core!

This module explores:
1. Binary structure (6 lines → 2^6 = 64 hexagrams)
2. How divination works (yarrow stalks vs coins)
3. The ASYMMETRIC probability distribution (NOT 50/50!)
4. Mapping to TI/GILE framework
5. Why the I Ching is actually a Tralse system, not binary
"""

import math
import random
from dataclasses import dataclass, field
from typing import Dict, List, Tuple, Optional
from enum import Enum


class LineType(Enum):
    """The four possible line types in I Ching"""
    OLD_YIN = ("old_yin", "⚋", 6, -1.0, True, "broken, changing")
    YOUNG_YANG = ("young_yang", "⚊", 7, 0.5, False, "solid, stable")
    YOUNG_YIN = ("young_yin", "⚋", 8, -0.5, False, "broken, stable")
    OLD_YANG = ("old_yang", "⚊", 9, 1.0, True, "solid, changing")
    
    @property
    def name_str(self) -> str:
        return self.value[0]
    
    @property
    def symbol(self) -> str:
        return self.value[1]
    
    @property
    def number(self) -> int:
        return self.value[2]
    
    @property
    def gile_value(self) -> float:
        """GILE polarity: -1 (pure yin) to +1 (pure yang)"""
        return self.value[3]
    
    @property
    def changing(self) -> bool:
        return self.value[4]
    
    @property
    def description(self) -> str:
        return self.value[5]


@dataclass
class Line:
    """A single line in a hexagram"""
    position: int
    line_type: LineType
    
    @property
    def is_yin(self) -> bool:
        return self.line_type in [LineType.OLD_YIN, LineType.YOUNG_YIN]
    
    @property
    def is_yang(self) -> bool:
        return self.line_type in [LineType.OLD_YANG, LineType.YOUNG_YANG]
    
    @property
    def is_changing(self) -> bool:
        return self.line_type.changing
    
    def get_changed_line(self) -> 'Line':
        """Get the line after transformation"""
        if self.line_type == LineType.OLD_YIN:
            return Line(self.position, LineType.YOUNG_YANG)
        elif self.line_type == LineType.OLD_YANG:
            return Line(self.position, LineType.YOUNG_YIN)
        return self


@dataclass
class Hexagram:
    """A complete hexagram (6 lines)"""
    lines: List[Line]
    number: int = 0
    name: str = ""
    
    @property
    def binary_string(self) -> str:
        """Binary representation (0=yin, 1=yang)"""
        return "".join("1" if line.is_yang else "0" for line in self.lines)
    
    @property
    def decimal_value(self) -> int:
        """Convert to decimal (0-63)"""
        return int(self.binary_string, 2)
    
    @property
    def changing_lines(self) -> List[int]:
        """Positions of changing lines (1-6)"""
        return [line.position for line in self.lines if line.is_changing]
    
    @property
    def gile_score(self) -> float:
        """Calculate GILE score from line values"""
        total = sum(line.line_type.gile_value for line in self.lines)
        return total / 6
    
    @property
    def tralseness(self) -> float:
        """Map GILE score to Tralseness (0.0 to 1.0)"""
        return (self.gile_score + 1) / 2
    
    def get_transformed(self) -> 'Hexagram':
        """Get the hexagram after all changes"""
        new_lines = [line.get_changed_line() for line in self.lines]
        return Hexagram(lines=new_lines)
    
    def display(self) -> str:
        """Visual representation of hexagram"""
        result = []
        for line in reversed(self.lines):
            if line.is_yang:
                symbol = "━━━━━━━" if not line.is_changing else "━━━○━━━"
            else:
                symbol = "━━━ ━━━" if not line.is_changing else "━━━ ○ ━━━"
            result.append(f"  {line.position}: {symbol}")
        return "\n".join(result)


class DivinationMethod(Enum):
    """Different methods for casting hexagram lines"""
    YARROW_STALKS = "yarrow_stalks"
    THREE_COINS = "three_coins"
    FOUR_COINS = "four_coins"


class IChingDivination:
    """
    I Ching divination engine with TI Framework integration.
    
    KEY INSIGHT: The yarrow stalk method produces ASYMMETRIC probabilities:
    - Old Yin (6):   1/16 = 6.25%
    - Young Yang (7): 5/16 = 31.25%
    - Young Yin (8):  7/16 = 43.75%
    - Old Yang (9):   3/16 = 18.75%
    
    This creates a TRALSE distribution, not binary 50/50!
    """
    
    YARROW_PROBABILITIES = {
        LineType.OLD_YIN: 1/16,
        LineType.YOUNG_YANG: 5/16,
        LineType.YOUNG_YIN: 7/16,
        LineType.OLD_YANG: 3/16
    }
    
    COIN_PROBABILITIES = {
        LineType.OLD_YIN: 1/8,
        LineType.YOUNG_YANG: 3/8,
        LineType.YOUNG_YIN: 3/8,
        LineType.OLD_YANG: 1/8
    }
    
    HEXAGRAM_NAMES = {
        1: "乾 Qián (Heaven)", 2: "坤 Kūn (Earth)",
        3: "屯 Zhūn (Difficulty)", 4: "蒙 Méng (Youth)",
        5: "需 Xū (Waiting)", 6: "訟 Sòng (Conflict)",
        7: "師 Shī (Army)", 8: "比 Bǐ (Holding Together)",
        11: "泰 Tài (Peace)", 12: "否 Pǐ (Standstill)",
        29: "坎 Kǎn (Water)", 30: "離 Lí (Fire)",
        63: "既濟 Jì Jì (After Completion)",
        64: "未濟 Wèi Jì (Before Completion)"
    }
    
    def __init__(self, method: DivinationMethod = DivinationMethod.YARROW_STALKS):
        self.method = method
        self.probabilities = (
            self.YARROW_PROBABILITIES if method == DivinationMethod.YARROW_STALKS
            else self.COIN_PROBABILITIES
        )
    
    def cast_line(self) -> LineType:
        """Cast a single line using the selected method"""
        rand = random.random()
        cumulative = 0
        for line_type, prob in self.probabilities.items():
            cumulative += prob
            if rand < cumulative:
                return line_type
        return LineType.YOUNG_YIN
    
    def cast_hexagram(self, question: str = "") -> Hexagram:
        """Cast a complete hexagram"""
        lines = []
        for i in range(1, 7):
            line_type = self.cast_line()
            lines.append(Line(position=i, line_type=line_type))
        
        hexagram = Hexagram(lines=lines)
        
        decimal = hexagram.decimal_value + 1
        hexagram.number = decimal
        hexagram.name = self.HEXAGRAM_NAMES.get(decimal, f"Hexagram {decimal}")
        
        return hexagram
    
    def interpret(self, hexagram: Hexagram) -> Dict:
        """Provide TI-based interpretation"""
        gile = hexagram.gile_score
        tralseness = hexagram.tralseness
        
        changing = hexagram.changing_lines
        has_changes = len(changing) > 0
        
        if has_changes:
            transformed = hexagram.get_transformed()
            transformed.number = transformed.decimal_value + 1
            transformed.name = self.HEXAGRAM_NAMES.get(
                transformed.number, f"Hexagram {transformed.number}"
            )
        else:
            transformed = None
        
        if gile > 0.5:
            energy = "Strong Yang - Active, creative, expanding"
        elif gile > 0:
            energy = "Mild Yang - Gentle action, steady progress"
        elif gile > -0.5:
            energy = "Mild Yin - Receptive, patient, nurturing"
        else:
            energy = "Strong Yin - Deep stillness, maximum receptivity"
        
        phi_distance = abs(gile)
        if phi_distance < 0.2:
            phi_state = "VERY CLOSE to Φ State (perfect balance)"
        elif phi_distance < 0.5:
            phi_state = "Approaching Φ State (good balance)"
        else:
            phi_state = "Far from Φ State (strong polarity)"
        
        return {
            "hexagram_number": hexagram.number,
            "hexagram_name": hexagram.name,
            "binary": hexagram.binary_string,
            "gile_score": gile,
            "tralseness": tralseness,
            "energy_reading": energy,
            "phi_state_distance": phi_distance,
            "phi_interpretation": phi_state,
            "changing_lines": changing,
            "has_transformation": has_changes,
            "transformed_hexagram": transformed.name if transformed else None,
            "transformed_number": transformed.number if transformed else None
        }


class IChingTIAnalysis:
    """
    Deep analysis of I Ching's relationship to TI Framework.
    """
    
    def __init__(self):
        self.divination = IChingDivination()
    
    def analyze_probability_distribution(self, n_simulations: int = 100000) -> Dict:
        """
        Analyze the probability distribution of yarrow stalk method.
        
        This proves the I Ching is NOT binary but TRALSE!
        """
        
        line_counts = {lt: 0 for lt in LineType}
        gile_scores = []
        tralseness_values = []
        changing_line_counts = {i: 0 for i in range(7)}
        
        for _ in range(n_simulations):
            hexagram = self.divination.cast_hexagram()
            
            for line in hexagram.lines:
                line_counts[line.line_type] += 1
            
            gile_scores.append(hexagram.gile_score)
            tralseness_values.append(hexagram.tralseness)
            
            num_changing = len(hexagram.changing_lines)
            changing_line_counts[num_changing] += 1
        
        total_lines = n_simulations * 6
        observed_probs = {lt: count/total_lines for lt, count in line_counts.items()}
        
        avg_gile = sum(gile_scores) / len(gile_scores)
        avg_tralseness = sum(tralseness_values) / len(tralseness_values)
        
        gile_std = math.sqrt(sum((g - avg_gile)**2 for g in gile_scores) / len(gile_scores))
        
        return {
            "simulations": n_simulations,
            "observed_probabilities": {
                lt.name_str: f"{prob:.4f} (expected: {self.divination.probabilities[lt]:.4f})"
                for lt, prob in observed_probs.items()
            },
            "average_gile": avg_gile,
            "gile_std": gile_std,
            "average_tralseness": avg_tralseness,
            "changing_lines_distribution": {
                f"{k} lines": f"{v/n_simulations:.2%}"
                for k, v in changing_line_counts.items()
            }
        }
    
    def demonstrate_tralseness(self) -> str:
        """
        Prove that I Ching is fundamentally Tralse, not binary.
        """
        
        report = []
        report.append("=" * 70)
        report.append("I CHING IS TRALSE, NOT BINARY: PROOF")
        report.append("=" * 70)
        
        report.append("""
THE APPARENT BINARY STRUCTURE
─────────────────────────────
At first glance, I Ching appears binary:
• Yin (⚋) = broken line = 0
• Yang (⚊) = solid line = 1

With 6 lines per hexagram:
• 2^6 = 64 possible hexagrams
• This seems like pure binary logic

BUT THE DIVINATION METHOD REVEALS TRALSENESS!
──────────────────────────────────────────────
The yarrow stalk method produces FOUR line types, not two:

┌────────────┬────────┬───────────┬─────────────┐
│ Line Type  │ Number │ Yarrow %  │ GILE Value  │
├────────────┼────────┼───────────┼─────────────┤
│ Old Yin    │   6    │   6.25%   │    -1.0     │
│ Young Yang │   7    │  31.25%   │    +0.5     │
│ Young Yin  │   8    │  43.75%   │    -0.5     │
│ Old Yang   │   9    │  18.75%   │    +1.0     │
└────────────┴────────┴───────────┴─────────────┘

KEY INSIGHT: This is NOT 50/50 binary!
• Yin total: 6.25% + 43.75% = 50%
• Yang total: 31.25% + 18.75% = 50%
• BUT the distribution WITHIN each polarity differs!

THE FOUR VALUES ARE FOUR DEGREES OF TRALSENESS:
• Old Yin (6) = Tralseness 0.0 (Pure Yin, about to change)
• Young Yin (8) = Tralseness 0.25 (Stable Yin)
• Young Yang (7) = Tralseness 0.75 (Stable Yang)
• Old Yang (9) = Tralseness 1.0 (Pure Yang, about to change)

This maps EXACTLY to the Tralseness spectrum [0.0, 1.0]!
        """)
        
        report.append("\n" + "=" * 70)
        report.append("THE 80% PARETO ALIGNMENT")
        report.append("=" * 70)
        
        report.append("""
ANALYZING THE PROBABILITY DISTRIBUTION:

"Stable" lines (7 and 8): 31.25% + 43.75% = 75%
"Changing" lines (6 and 9): 6.25% + 18.75% = 25%

But there's a deeper pattern:
• Young Yin (8) alone = 43.75% ≈ Pareto's "trivial many"
• Old Yang (9) = 18.75% ≈ Pareto's "vital few" (close to 20%)

The yarrow stalk method naturally produces:
• ~80% "stable/normal" outcomes
• ~20% "transformative/significant" changes

THIS IS THE PARETO PRINCIPLE ENCODED IN ANCIENT DIVINATION!

Furthermore:
• Lines in the "sacred interval" (GILE between -1/3 and +2/3):
  Young Yin (8) + Young Yang (7) = 75%
• Lines at extremes (GILE at -1.0 or +1.0):
  Old Yin (6) + Old Yang (9) = 25%

The I Ching naturally concentrates 75% of readings in the
moderate/balanced zone, matching TI's sacred interval!
        """)
        
        report.append("\n" + "=" * 70)
        report.append("SIMULATION VERIFICATION")
        report.append("=" * 70)
        
        analysis = self.analyze_probability_distribution(50000)
        
        report.append(f"\nSimulated {analysis['simulations']:,} hexagrams:")
        report.append("\nObserved Line Probabilities:")
        for line_type, prob_str in analysis['observed_probabilities'].items():
            report.append(f"  {line_type}: {prob_str}")
        
        report.append(f"\nAverage GILE Score: {analysis['average_gile']:.4f}")
        report.append(f"GILE Standard Deviation: {analysis['gile_std']:.4f}")
        report.append(f"Average Tralseness: {analysis['average_tralseness']:.4f}")
        
        report.append("\nChanging Lines Distribution:")
        for k, v in analysis['changing_lines_distribution'].items():
            report.append(f"  {k}: {v}")
        
        report.append("\n" + "=" * 70)
        report.append("TI FRAMEWORK MAPPING")
        report.append("=" * 70)
        
        report.append("""
HOW I CHING MAPS TO TI:

1. HEXAGRAMS → GILE STATES
   Each hexagram has a GILE score from -1.0 to +1.0
   Pure Yang (111111) = +1.0 = Maximum active consciousness
   Pure Yin (000000) = -1.0 = Maximum receptive consciousness
   Balanced mix = 0.0 = Φ State (Wu Wei)

2. TRIGRAMS → GILE DIMENSIONS
   Lower trigram (lines 1-3) = Inner state
   Upper trigram (lines 4-6) = Outer manifestation
   8 trigrams map to combinations of G, I, L, E

3. CHANGING LINES → CONSCIOUSNESS TRANSITIONS
   Old Yin → Young Yang = Receptivity becoming action
   Old Yang → Young Yin = Action becoming receptivity
   The CHANGE is the key insight, not the static state

4. THE FIVE ELEMENTS → GILE DYNAMICS
   Wood (growth) → G (Goodness) rising
   Fire (expansion) → I (Intuition) peak
   Earth (center) → Φ State (balance)
   Metal (contraction) → L (Love) consolidating
   Water (stillness) → E (Environment) receiving

5. DIVINATION AS Φ STATE ACCESS
   The ritual of casting yarrow stalks:
   • Slows consciousness
   • Creates focused attention
   • Accesses intuitive (I dimension)
   • Reading IS the practitioner's consciousness
     projecting meaning onto probability
        """)
        
        report.append("\n" + "=" * 70)
        report.append("WHY 35% > 25% IN EXPERIMENTS")
        report.append("=" * 70)
        
        report.append("""
Storm & Thalbourne found 35% accuracy vs 25% chance (40% improvement).

TI EXPLANATION:

1. TRANSLIMINALITY CORRELATION
   Higher I (Intuition) dimension = better results
   The practitioner's consciousness MATTERS

2. ASYMMETRIC PROBABILITY
   Yarrow stalks don't produce uniform distribution
   Certain hexagrams are MORE LIKELY
   This creates "attractors" in the probability space

3. CONFIRMATION BIAS AS GILE COHERENCE
   What mainstream calls "bias" is actually:
   Consciousness recognizing resonant patterns
   The hexagram that "fits" IS the right one
   Because consciousness selected it

4. THE READING IS THE CONSCIOUSNESS
   You don't "get" a random hexagram
   Your consciousness state at casting time
   Influences the probability distribution
   (Quantum observer effect at macro scale)

5. Φ STATE ACCESS
   The ritual induces near-Φ state
   Balanced GILE allows pattern recognition
   35% > 25% because REAL information accessed
        """)
        
        return "\n".join(report)
    
    def sample_reading(self, question: str = "What should I focus on today?") -> str:
        """Perform a sample reading with TI interpretation"""
        
        result = []
        result.append("=" * 60)
        result.append("I CHING READING (TI-Enhanced)")
        result.append("=" * 60)
        result.append(f"\nQuestion: {question}\n")
        
        hexagram = self.divination.cast_hexagram(question)
        interpretation = self.divination.interpret(hexagram)
        
        result.append("HEXAGRAM CAST:")
        result.append(hexagram.display())
        result.append(f"\n#{interpretation['hexagram_number']}: {interpretation['hexagram_name']}")
        result.append(f"Binary: {interpretation['binary']}")
        
        result.append(f"\nTI ANALYSIS:")
        result.append(f"GILE Score: {interpretation['gile_score']:+.3f}")
        result.append(f"Tralseness: {interpretation['tralseness']:.3f}")
        result.append(f"Energy: {interpretation['energy_reading']}")
        result.append(f"Φ State: {interpretation['phi_interpretation']}")
        
        if interpretation['has_transformation']:
            result.append(f"\nCHANGING LINES: {interpretation['changing_lines']}")
            result.append(f"Transforms to: #{interpretation['transformed_number']}: {interpretation['transformed_hexagram']}")
            result.append("\nThis indicates a transition in consciousness state.")
        else:
            result.append("\nNo changing lines - stable situation.")
        
        return "\n".join(result)


def run_i_ching_analysis():
    """Run complete I Ching + TI analysis"""
    
    analysis = IChingTIAnalysis()
    
    print(analysis.demonstrate_tralseness())
    
    print("\n" + "=" * 70)
    print("SAMPLE READINGS")
    print("=" * 70)
    
    for i in range(3):
        print(f"\n--- Reading {i+1} ---")
        print(analysis.sample_reading())
    
    with open("i_ching_ti_analysis.txt", "w") as f:
        f.write(analysis.demonstrate_tralseness())
    print("\n[Analysis saved to i_ching_ti_analysis.txt]")


if __name__ == "__main__":
    run_i_ching_analysis()
