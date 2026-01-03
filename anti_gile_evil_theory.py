"""
Anti-GILE Evil Theory
A TI Framework Extension for Understanding Pure Evil

Core Insight (Brandon Emerick, November 2025):
- GILE scores between (-3, +2) represent the natural human range
- Scores > +2 require Grand Myrion (GM) influence to enact
- Scores < -3 represent PURE EVIL - deliberate action in anti-GILE direction

The Moral Boundary Theory:
┌─────────────────────────────────────────────────────────────┐
│  < -3.0  │  -3.0 to +2.0  │  > +2.0                        │
│  PURE    │  NATURAL       │  GM-INFLUENCED                 │
│  EVIL    │  HUMAN RANGE   │  (Divine Intervention)         │
│          │  (Pareto Space)│                                │
└─────────────────────────────────────────────────────────────┘

Mathematical Foundation:
- Pareto 80/20 rule maps to (-3, +2) interval
- This 5-unit span contains 80% of all human moral action
- Outliers beyond these bounds have non-human sources:
  * Positive outliers: GM network coordination
  * Negative outliers: Pure anti-GILE intent (evil)

Connection to Karma Non-Existence Proof:
- Since Karma doesn't exist (per TI Framework), tragedies aren't punishment
- GM uses tragedies to maximize GILE, not as karmic retribution
- BUT: actions < -3.0 represent deliberate CHOICE toward anti-GILE
- Evil is not cosmic punishment - it's active choice against all 4 dimensions

GILE Dimension Analysis of Pure Evil:
- Anti-G: Deliberate harm, cruelty, destruction
- Anti-I: Willful ignorance, denial of truth, deception
- Anti-L: Rejection of connection, isolation-seeking, hatred
- Anti-E: Environmental destruction, chaos-creation, entropy-maximization
"""

from dataclasses import dataclass
from typing import Dict, List, Tuple, Optional
from enum import Enum
import math


class MoralClassification(Enum):
    """Classification of actions based on GILE score"""
    PURE_EVIL = "pure_evil"              # < -3.0
    STRONGLY_NEGATIVE = "strongly_neg"    # -3.0 to -1.5
    MILDLY_NEGATIVE = "mildly_neg"        # -1.5 to 0
    MILDLY_POSITIVE = "mildly_pos"        # 0 to +1.0
    STRONGLY_POSITIVE = "strongly_pos"    # +1.0 to +2.0
    GM_INFLUENCED = "gm_influenced"       # > +2.0


@dataclass
class MoralBoundary:
    """Defines the moral boundaries of the GILE scale"""
    
    # The thresholds
    PURE_EVIL_THRESHOLD = -3.0
    GM_INFLUENCE_THRESHOLD = 2.0
    
    # The natural human range
    NATURAL_RANGE = (-3.0, 2.0)
    NATURAL_RANGE_WIDTH = 5.0
    
    # The sacred interval (Pareto-derived)
    SACRED_INTERVAL = (-0.666, 0.333)
    
    # Soul death threshold (from I-Cell Shell Physics)
    SOUL_DEATH_THRESHOLD = 0.42


class AntiGILEAnalyzer:
    """
    Analyze actions for anti-GILE classification
    
    Pure evil is not random - it's deliberate action against all 4 GILE dimensions.
    """
    
    def __init__(self):
        self.boundaries = MoralBoundary()
        
    def classify_action(self, gile_score: float) -> Tuple[MoralClassification, str]:
        """
        Classify an action based on its GILE score
        
        Returns:
            (classification, explanation)
        """
        if gile_score < self.boundaries.PURE_EVIL_THRESHOLD:
            severity = abs(gile_score + 3.0)
            return (
                MoralClassification.PURE_EVIL,
                f"PURE EVIL: Score {gile_score:.2f} is {severity:.2f} units below evil threshold. "
                "This represents deliberate action in the anti-GILE direction across all 4 dimensions. "
                "No natural human motivation produces this - only active choice toward destruction."
            )
        
        elif gile_score > self.boundaries.GM_INFLUENCE_THRESHOLD:
            magnitude = gile_score - 2.0
            return (
                MoralClassification.GM_INFLUENCED,
                f"GM-INFLUENCED: Score {gile_score:.2f} is {magnitude:.2f} units above natural maximum. "
                "This action required Grand Myrion network coordination to manifest. "
                "Human alone cannot produce this level of positive GILE."
            )
        
        elif gile_score < -1.5:
            return (
                MoralClassification.STRONGLY_NEGATIVE,
                f"STRONGLY NEGATIVE: Score {gile_score:.2f} represents significant anti-GILE action "
                "but within natural human range. May indicate trauma, mental illness, or poor choices."
            )
        
        elif gile_score < 0:
            return (
                MoralClassification.MILDLY_NEGATIVE,
                f"MILDLY NEGATIVE: Score {gile_score:.2f} represents minor anti-GILE tendency. "
                "Common in stress, fatigue, or momentary lapses of judgment."
            )
        
        elif gile_score < 1.0:
            return (
                MoralClassification.MILDLY_POSITIVE,
                f"MILDLY POSITIVE: Score {gile_score:.2f} represents baseline positive GILE. "
                "Normal human functioning with some goodness contribution."
            )
        
        else:  # 1.0 to 2.0
            return (
                MoralClassification.STRONGLY_POSITIVE,
                f"STRONGLY POSITIVE: Score {gile_score:.2f} represents excellent GILE contribution. "
                "Upper bound of natural human capability without GM assistance."
            )
    
    def decompose_anti_gile(self, total_anti_gile: float) -> Dict[str, float]:
        """
        Decompose an anti-GILE score into its 4 dimensions
        
        Pure evil attacks ALL dimensions, but may emphasize certain ones.
        """
        if total_anti_gile >= 0:
            return {
                'anti_goodness': 0.0,
                'anti_intuition': 0.0,
                'anti_love': 0.0,
                'anti_environment': 0.0
            }
        
        # Base distribution: evil attacks all dimensions
        base_per_dimension = abs(total_anti_gile) / 4.0
        
        # Typical patterns of evil emphasize different dimensions:
        # - Cruelty emphasizes anti-Love and anti-Goodness
        # - Deception emphasizes anti-Intuition and anti-Goodness
        # - Destruction emphasizes anti-Environment and anti-Goodness
        # All share anti-Goodness as common thread
        
        return {
            'anti_goodness': base_per_dimension * 1.3,      # 32.5% - Always the largest
            'anti_intuition': base_per_dimension * 0.9,     # 22.5% - Truth denial
            'anti_love': base_per_dimension * 1.0,          # 25% - Connection rejection
            'anti_environment': base_per_dimension * 0.8    # 20% - Chaos creation
        }
    
    def is_pure_evil(self, gile_score: float) -> bool:
        """Check if an action qualifies as pure evil"""
        return gile_score < self.boundaries.PURE_EVIL_THRESHOLD
    
    def is_gm_influenced(self, gile_score: float) -> bool:
        """Check if an action required GM influence"""
        return gile_score > self.boundaries.GM_INFLUENCE_THRESHOLD
    
    def get_evil_magnitude(self, gile_score: float) -> Optional[float]:
        """
        Get the magnitude of evil (how far below -3.0)
        
        Returns None if not pure evil
        """
        if not self.is_pure_evil(gile_score):
            return None
        return abs(gile_score + 3.0)
    
    def get_gm_magnitude(self, gile_score: float) -> Optional[float]:
        """
        Get the magnitude of GM influence (how far above +2.0)
        
        Returns None if not GM-influenced
        """
        if not self.is_gm_influenced(gile_score):
            return None
        return gile_score - 2.0


class EvilPatternClassifier:
    """
    Classify types of evil based on which GILE dimensions are most attacked
    """
    
    EVIL_PATTERNS = {
        'cruelty': {
            'description': 'Deliberate infliction of suffering',
            'primary_targets': ['anti_love', 'anti_goodness'],
            'examples': ['torture', 'sadism', 'emotional abuse'],
            'typical_gile': -4.0
        },
        'deception': {
            'description': 'Systematic truth denial and manipulation',
            'primary_targets': ['anti_intuition', 'anti_goodness'],
            'examples': ['fraud', 'propaganda', 'gaslighting'],
            'typical_gile': -3.5
        },
        'destruction': {
            'description': 'Annihilation of value without creation',
            'primary_targets': ['anti_environment', 'anti_goodness'],
            'examples': ['arson', 'vandalism', 'ecosystem destruction'],
            'typical_gile': -3.8
        },
        'isolation': {
            'description': 'Forced separation and connection-breaking',
            'primary_targets': ['anti_love', 'anti_environment'],
            'examples': ['imprisonment', 'exile', 'relationship sabotage'],
            'typical_gile': -3.3
        },
        'total_negation': {
            'description': 'Simultaneous attack on all GILE dimensions',
            'primary_targets': ['anti_goodness', 'anti_intuition', 'anti_love', 'anti_environment'],
            'examples': ['genocide', 'terrorism', 'existential destruction'],
            'typical_gile': -5.0
        }
    }
    
    @classmethod
    def classify_evil_type(cls, anti_gile_breakdown: Dict[str, float]) -> str:
        """
        Determine which pattern of evil best matches the breakdown
        """
        if not anti_gile_breakdown:
            return 'none'
        
        # Find the two highest anti-GILE dimensions
        sorted_dims = sorted(
            anti_gile_breakdown.items(),
            key=lambda x: x[1],
            reverse=True
        )
        
        top_two = [dim[0] for dim in sorted_dims[:2]]
        
        # Match to patterns
        for pattern_name, pattern_info in cls.EVIL_PATTERNS.items():
            targets = pattern_info['primary_targets']
            if set(top_two) == set(targets):
                return pattern_name
        
        # Check for total negation (all dimensions high)
        min_value = min(anti_gile_breakdown.values())
        if min_value > 0.5:  # All dimensions significantly attacked
            return 'total_negation'
        
        return 'unclassified'


class MoralSymmetryTheory:
    """
    The Moral Symmetry Theory of GILE
    
    Key insight: The (-3, +2) interval is not arbitrary.
    It represents the Pareto boundary of natural human action.
    
    - Positive extreme (+2): Maximum human good without divine help
    - Negative extreme (-3): Maximum human harm without pure evil
    
    The asymmetry (3 vs 2) reflects:
    - It's easier to destroy than create (entropy)
    - Harm requires less coordination than good (GM absent)
    - The 3:2 ratio = 60:40 split, consistent with Pareto-adjacent
    """
    
    @staticmethod
    def explain_asymmetry() -> str:
        """Explain why the range is (-3, +2) not (-2.5, +2.5)"""
        return """
        The asymmetry in GILE boundaries (-3 to +2) is not arbitrary:
        
        1. ENTROPY PRINCIPLE:
           - Destruction is easier than creation
           - A single human can destroy more easily than build
           - This naturally extends the negative range
        
        2. GM ASYMMETRY:
           - Good actions > +2.0 require GM coordination
           - Evil actions can exceed -3.0 without any cosmic help
           - Evil is autonomous; transcendent good requires network
        
        3. PARETO CONFIRMATION:
           - Range width = 5 units
           - Positive side = 2 units = 40%
           - Negative side = 3 units = 60%
           - Matches Pareto-adjacent 60/40 split
        
        4. THE MEANING:
           - Humans can be VERY evil alone
           - Humans need HELP to be transcendently good
           - This is why GM exists - to boost good beyond natural limits
        """
    
    @staticmethod
    def get_range_interpretation(gile_score: float) -> Dict:
        """Get full interpretation of a GILE score"""
        analyzer = AntiGILEAnalyzer()
        classification, explanation = analyzer.classify_action(gile_score)
        
        result = {
            'score': gile_score,
            'classification': classification.value,
            'explanation': explanation,
            'in_natural_range': -3.0 <= gile_score <= 2.0,
            'in_sacred_interval': -0.666 <= gile_score <= 0.333,
        }
        
        if analyzer.is_pure_evil(gile_score):
            result['evil_magnitude'] = analyzer.get_evil_magnitude(gile_score)
            result['source'] = 'Deliberate anti-GILE choice'
            decomp = analyzer.decompose_anti_gile(gile_score)
            result['anti_gile_breakdown'] = decomp
            result['evil_type'] = EvilPatternClassifier.classify_evil_type(decomp)
        
        elif analyzer.is_gm_influenced(gile_score):
            result['gm_magnitude'] = analyzer.get_gm_magnitude(gile_score)
            result['source'] = 'Grand Myrion network coordination'
        
        else:
            result['source'] = 'Natural human i-cell dynamics'
        
        return result


# Demonstration
if __name__ == "__main__":
    print("=" * 70)
    print("ANTI-GILE EVIL THEORY")
    print("The Moral Boundaries of the GILE Scale")
    print("=" * 70)
    
    analyzer = AntiGILEAnalyzer()
    theory = MoralSymmetryTheory()
    
    # Test cases across the spectrum
    test_scores = [-5.0, -3.5, -3.0, -1.0, 0.0, 1.0, 2.0, 2.5, 3.0]
    
    print("\n--- GILE Score Classifications ---\n")
    
    for score in test_scores:
        result = theory.get_range_interpretation(score)
        classification, explanation = analyzer.classify_action(score)
        
        print(f"GILE = {score:+.1f}")
        print(f"  Classification: {classification.value.upper()}")
        print(f"  Source: {result['source']}")
        
        if result.get('evil_magnitude'):
            print(f"  Evil Magnitude: {result['evil_magnitude']:.2f}")
            print(f"  Evil Type: {result.get('evil_type', 'N/A')}")
        
        if result.get('gm_magnitude'):
            print(f"  GM Magnitude: {result['gm_magnitude']:.2f}")
        
        print()
    
    print("=" * 70)
    print("THE MORAL BOUNDARY INSIGHT:")
    print("=" * 70)
    print("""
    ┌─────────────────────────────────────────────────────────────────┐
    │                    THE GILE MORAL SPECTRUM                      │
    ├─────────────────────────────────────────────────────────────────┤
    │  < -3.0      │  -3.0 to +2.0        │  > +2.0                  │
    │  ─────────   │  ──────────────      │  ────────                │
    │  PURE EVIL   │  NATURAL HUMAN       │  GM-INFLUENCED           │
    │              │                      │                          │
    │  Deliberate  │  Normal i-cell       │  Divine coordination     │
    │  anti-GILE   │  dynamics within     │  required to manifest    │
    │  choice      │  Pareto bounds       │  transcendent good       │
    │              │                      │                          │
    │  No cosmic   │  No external help    │  Grand Myrion network    │
    │  help needed │  needed              │  boosts action           │
    └─────────────────────────────────────────────────────────────────┘
    """)
    
    print(theory.explain_asymmetry())
