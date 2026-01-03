"""
TRALSE Epistemology
Truth, Crowds, and the Cure for Bad Thinking

Core Insights (Brandon Emerick, November 2025):

1. ALONENESS FALLACY:
   "Aloneness doesn't cause polarization or other fallacies any more than
   socializing does. The ONLY cure for BAD THINKING is TRUE-TRALSE thinking!"
   
2. WISDOM OF CROWDS IS BS:
   "It gets you the 'socially recognized relative truth.' NOT TRUTH!
   There's a reason why we don't hire 100 or even 1000 people to each bet
   on answers to concrete problems which require actual thinking and
   investigation... except in Dumbocracy!"

These insights formalize the TI Framework's epistemological foundation.
"""

from dataclasses import dataclass
from typing import Dict, List, Tuple
from enum import Enum


class ThinkingMode(Enum):
    """Types of thinking and their truth-finding capacity"""
    SOLO_BAD = "solo_bad"           # Alone + bad logic
    SOLO_TRALSE = "solo_tralse"     # Alone + Tralse logic
    CROWD_BAD = "crowd_bad"         # Crowds + bad logic
    CROWD_TRALSE = "crowd_tralse"   # Crowds + Tralse logic (rare)


class TruthType(Enum):
    """Types of "truth" that different methods produce"""
    ACTUAL_TRUTH = "actual_truth"                   # Objective reality
    SOCIALLY_RECOGNIZED = "socially_recognized"     # What crowds agree on
    RELATIVE_TRUTH = "relative_truth"               # Context-dependent
    TRALSE_TRUTH = "tralse_truth"                   # 4-valued logic truth


@dataclass
class EpistemologicalAnalysis:
    """Analysis of a truth-finding method"""
    method: str
    produces: TruthType
    reliability: float
    explanation: str


class AlonenessVsSocializingFallacy:
    """
    The Aloneness Fallacy Debunked
    
    Common belief: "Isolation causes echo chambers and polarization"
    Reality: Neither aloneness NOR socializing affects truth-finding quality
    
    The ONLY variable that matters: Quality of LOGIC used
    """
    
    @staticmethod
    def explain() -> str:
        return """
        ══════════════════════════════════════════════════════════════════
        THE ALONENESS FALLACY - DEBUNKED
        ══════════════════════════════════════════════════════════════════
        
        COMMON BELIEF:
        "Isolation causes polarization, echo chambers, and bad thinking.
         Socializing with diverse people cures these problems."
        
        THE TRUTH:
        ┌─────────────────────────────────────────────────────────────────┐
        │  Aloneness doesn't cause polarization any more than            │
        │  socializing does.                                             │
        │                                                                 │
        │  BAD LOGIC causes bad thinking.                                │
        │  GOOD LOGIC (Tralse) cures bad thinking.                       │
        │                                                                 │
        │  The social context is IRRELEVANT to truth-finding.            │
        └─────────────────────────────────────────────────────────────────┘
        
        THE MATRIX:
        
                        │ Bad Logic      │ Tralse Logic
        ────────────────┼────────────────┼─────────────────
        Alone           │ Bad thinking   │ TRUTH
        ────────────────┼────────────────┼─────────────────
        Socializing     │ Bad thinking   │ TRUTH
        
        Notice: The ROW doesn't determine outcome. The COLUMN does.
        
        IMPLICATIONS:
        
        1. Telling isolated people to "get out more" doesn't fix thinking
        2. Telling social people to "listen more" doesn't fix thinking
        3. TEACHING TRALSE LOGIC fixes thinking regardless of context
        
        The cure for bad thinking is not MORE PEOPLE.
        The cure for bad thinking is BETTER LOGIC.
        
        The ONLY cure for BAD THINKING is TRUE-TRALSE THINKING.
        """
    
    @staticmethod
    def analyze_scenario(is_alone: bool, uses_tralse: bool) -> EpistemologicalAnalysis:
        """Analyze a thinking scenario"""
        
        if uses_tralse:
            return EpistemologicalAnalysis(
                method=f"{'Solo' if is_alone else 'Social'} + Tralse Logic",
                produces=TruthType.ACTUAL_TRUTH,
                reliability=0.95,
                explanation="Tralse logic produces truth regardless of social context"
            )
        else:
            return EpistemologicalAnalysis(
                method=f"{'Solo' if is_alone else 'Social'} + Bad Logic",
                produces=TruthType.RELATIVE_TRUTH,
                reliability=0.30,
                explanation="Bad logic produces unreliable conclusions regardless of social context"
            )


class WisdomOfCrowdsCritique:
    """
    The "Wisdom of Crowds" Debunked
    
    Crowds produce: "Socially recognized relative truth"
    Crowds do NOT produce: Actual truth
    
    Key insight: We don't hire 1000 people to bet on solutions
    to problems requiring investigation... except in democracy!
    """
    
    @staticmethod
    def explain() -> str:
        return """
        ══════════════════════════════════════════════════════════════════
        THE "WISDOM OF CROWDS" IS BS
        ══════════════════════════════════════════════════════════════════
        
        THE CLAIM:
        "Aggregate many opinions and you get closer to truth"
        
        THE REALITY:
        ┌─────────────────────────────────────────────────────────────────┐
        │  Crowds produce: "SOCIALLY RECOGNIZED RELATIVE TRUTH"          │
        │                                                                 │
        │  Crowds do NOT produce: ACTUAL TRUTH                           │
        │                                                                 │
        │  These are COMPLETELY DIFFERENT THINGS.                        │
        └─────────────────────────────────────────────────────────────────┘
        
        THE DUMBOCRACY INSIGHT:
        
        We would NEVER do this in serious domains:
        
        ❌ "Let's have 1000 people vote on the correct cancer treatment"
        ❌ "Let's poll the audience on quantum mechanics equations"
        ❌ "Let's crowdsource the structural engineering of this bridge"
        
        Why? Because these require:
        - Actual investigation
        - Domain expertise  
        - Logical reasoning
        - Evidence evaluation
        
        BUT we DO this in democracy:
        
        ✓ "Let's have millions vote on complex economic policy"
        ✓ "Let's poll uninformed citizens on foreign policy"
        ✓ "Let's crowdsource governance of society"
        
        THE ABSURDITY IS IDENTICAL.
        
        WHAT CROWDS ACTUALLY DO:
        
        ┌─────────────────────────────────────────────────────────────────┐
        │ INPUT:  Many uninformed opinions                               │
        │ PROCESS: Averaging/voting                                      │
        │ OUTPUT:  The POPULAR answer (not the CORRECT answer)           │
        └─────────────────────────────────────────────────────────────────┘
        
        This is not wisdom. This is AVERAGING IGNORANCE.
        
        The only time "wisdom of crowds" works:
        - Estimating jar of jellybeans (pure statistics)
        - Prediction markets WITH skin in the game
        - Questions with NO expertise required
        
        For anything requiring THOUGHT + INVESTIGATION:
        - One expert with Tralse logic > 1 million uninformed voters
        - Truth is not democratic
        - Reality doesn't care about consensus
        """
    
    @staticmethod
    def what_crowds_produce() -> Dict[str, str]:
        """What different aggregation methods actually produce"""
        return {
            'voting': 'Most popular opinion (not truth)',
            'averaging': 'Mean of guesses (statistical artifact)',
            'consensus': 'Socially acceptable compromise (not truth)',
            'polling': 'Snapshot of current beliefs (not truth)',
            'prediction_markets': 'Best available guess with incentives (closer but not truth)',
            'single_tralse_thinker': 'ACTUAL TRUTH (with proper investigation)'
        }
    
    @staticmethod
    def the_dumbocracy_critique() -> str:
        """Critique of democratic epistemology"""
        return """
        ══════════════════════════════════════════════════════════════════
        DUMBOCRACY: When Crowds Replace Thinking
        ══════════════════════════════════════════════════════════════════
        
        DEFINITION:
        Dumbocracy (n.): A system that aggregates uninformed opinions
        and treats the result as if it were informed decision-making.
        
        THE PATTERN:
        
        1. Complex problem arises (economy, foreign policy, healthcare)
        2. Problem requires: expertise, investigation, Tralse logic
        3. Instead: Ask millions of uninformed people to vote
        4. Treat result as "the will of the people" (actually: average ignorance)
        5. Implement policy based on crowd noise, not truth
        
        THE ABSURDITY TEST:
        
        Would you use this method for:
        
        │ Domain           │ Use Crowds? │ Why Not?                   │
        ├──────────────────┼─────────────┼────────────────────────────┤
        │ Cancer treatment │ NO          │ Requires medical expertise │
        │ Bridge design    │ NO          │ Requires engineering       │
        │ Legal verdict    │ Maybe       │ Jury = structured crowd    │
        │ Tax policy       │ YES (!)     │ ??? Requires economics ??? │
        │ Foreign policy   │ YES (!)     │ ??? Requires geopolitics ? │
        
        The inconsistency is the critique.
        
        THE ALTERNATIVE:
        
        Truth-finding requires:
        1. Investigation (not opinion aggregation)
        2. Expertise (not popularity)
        3. Tralse logic (not voting)
        4. Evidence (not feelings)
        
        One person with these > one million without.
        """


class TralseTruthFinding:
    """
    The Tralse Method: The ONLY cure for bad thinking
    """
    
    TRALSE_VALUES = {
        'TRUE': 'Definitely true, verified',
        'FALSE': 'Definitely false, disproven',
        'TRALSE': 'Both true AND false (paradox, context-dependent)',
        'NEITHER': 'Neither true nor false (undefined, meaningless)'
    }
    
    @staticmethod
    def explain() -> str:
        return """
        ══════════════════════════════════════════════════════════════════
        TRALSE LOGIC: The ONLY Cure for Bad Thinking
        ══════════════════════════════════════════════════════════════════
        
        Binary logic (TRUE/FALSE) creates:
        - False dichotomies
        - Forced choices between wrong options
        - Polarization (my side TRUE, your side FALSE)
        
        Tralse logic (TRUE/FALSE/TRALSE/NEITHER) allows:
        - Paradox recognition (some things are BOTH)
        - Meaninglessness recognition (some questions are NEITHER)
        - Nuance without relativism
        
        THE FOUR VALUES:
        
        ┌─────────────┬────────────────────────────────────────────────┐
        │ TRUE        │ Verified, corresponds to reality               │
        ├─────────────┼────────────────────────────────────────────────┤
        │ FALSE       │ Disproven, contradicts reality                 │
        ├─────────────┼────────────────────────────────────────────────┤
        │ TRALSE      │ Both true AND false (context-dependent,        │
        │             │ paradoxical, or perspective-relative)          │
        ├─────────────┼────────────────────────────────────────────────┤
        │ NEITHER     │ The question itself is malformed,              │
        │             │ meaningless, or undefined                      │
        └─────────────┴────────────────────────────────────────────────┘
        
        WHY THIS CURES BAD THINKING:
        
        Most bad thinking comes from:
        1. Forcing TRALSE situations into TRUE/FALSE → polarization
        2. Treating NEITHER questions as if they have answers → confusion
        3. Binary tribalism → "if you're not TRUE, you're FALSE"
        
        Tralse logic dissolves these by:
        1. Acknowledging paradox without contradiction
        2. Rejecting meaningless questions
        3. Allowing multiple valid perspectives on TRALSE matters
        
        APPLICATION TO CROWDS VS. ALONE:
        
        The question "Does aloneness cause bad thinking?" is NEITHER.
        The question is malformed.
        
        The CORRECT question: "Does the thinker use Tralse logic?"
        THAT determines truth-finding capacity.
        Social context is irrelevant.
        """


# Demonstration
if __name__ == "__main__":
    print("=" * 70)
    print("TRALSE EPISTEMOLOGY")
    print("Truth, Crowds, and the Cure for Bad Thinking")
    print("=" * 70)
    
    print(AlonenessVsSocializingFallacy.explain())
    print(WisdomOfCrowdsCritique.explain())
    print(WisdomOfCrowdsCritique.the_dumbocracy_critique())
    print(TralseTruthFinding.explain())
    
    print("\n" + "=" * 70)
    print("SUMMARY:")
    print("=" * 70)
    print("""
    ┌─────────────────────────────────────────────────────────────────┐
    │                    KEY INSIGHTS                                 │
    ├─────────────────────────────────────────────────────────────────┤
    │                                                                 │
    │  1. Aloneness ≠ Bad Thinking                                   │
    │     Socializing ≠ Good Thinking                                │
    │     TRALSE LOGIC = Good Thinking                               │
    │                                                                 │
    │  2. Wisdom of Crowds = Averaging Ignorance                     │
    │     Produces: "Socially recognized relative truth"             │
    │     Does NOT produce: Actual truth                             │
    │                                                                 │
    │  3. Dumbocracy uses crowd methods for expert problems          │
    │     We wouldn't vote on surgery; why vote on policy?           │
    │                                                                 │
    │  4. The ONLY cure for bad thinking is TRUE-TRALSE thinking     │
    │     Not more people. Not more discussion.                      │
    │     BETTER LOGIC.                                              │
    │                                                                 │
    └─────────────────────────────────────────────────────────────────┘
    """)
