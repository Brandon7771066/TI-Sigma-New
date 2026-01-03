"""
Free Will Intensity Paradox
A TI Framework Extension

Core Insight (Brandon Emerick, November 2025):
"The more intense the 'free will,' the less free and GILE it actually is!"

The Paradox Explained:
- When you're STRUGGLING to make a choice → you're constrained
- When choices flow effortlessly → you're truly free
- Intense deliberation = fighting against natural GILE alignment
- Effortless action = GM-aligned flow state

Mathematical Formulation:
    Freedom ∝ 1 / Intensity_of_choosing

Where:
- High intensity (struggle, force, deliberation) → Low actual freedom
- Low intensity (flow, ease, intuition) → High actual freedom

Connection to TI Framework:
1. FREE WILL SWEET SPOT (2/3 determined):
   - 2/3 of action is already determined by GM/environment
   - The 1/3 "free" part should feel EFFORTLESS
   - If it feels intense, you're fighting the 2/3

2. GILE OPTIMIZATION:
   - High GILE actions flow naturally
   - Low GILE actions require intense effort
   - Struggle = signal of anti-GILE direction

3. FLOW STATE:
   - True freedom = flow state
   - Flow is characterized by LACK of intense choice
   - The ego dissolves; action happens through you

4. GM ALIGNMENT:
   - When aligned with GM, choices are obvious
   - When misaligned, every choice feels like war
   - Intensity = resistance to natural path

The Irony:
People who SAY they have "strong free will" (intense choosers) are actually:
- Fighting against natural flow
- Lower GILE than they realize  
- Less free than someone who "goes with the flow"
- Exhausting themselves against GM's optimal path
"""

from dataclasses import dataclass
from typing import Dict, Tuple
from enum import Enum
import math


class ChoiceIntensity(Enum):
    """Levels of effort in making a choice"""
    EFFORTLESS = "effortless"       # Flow state, GM-aligned
    LIGHT = "light"                  # Minor consideration
    MODERATE = "moderate"            # Normal deliberation
    INTENSE = "intense"              # Significant struggle
    AGONIZING = "agonizing"          # Extreme conflict


@dataclass
class FreeWillAnalysis:
    """Analysis of a choice's true freedom level"""
    stated_choice: str
    intensity: ChoiceIntensity
    actual_freedom: float           # 0-1, inversely related to intensity
    gile_alignment: float           # How aligned with GILE
    flow_state: bool                # True if effortless
    gm_aligned: bool                # True if GM-supported
    paradox_explanation: str


class FreeWillIntensityAnalyzer:
    """
    Analyze the paradox: intense "free will" = less actual freedom
    """
    
    # Intensity to freedom mapping (inverse relationship)
    INTENSITY_TO_FREEDOM = {
        ChoiceIntensity.EFFORTLESS: 1.0,    # Maximum freedom
        ChoiceIntensity.LIGHT: 0.8,
        ChoiceIntensity.MODERATE: 0.5,
        ChoiceIntensity.INTENSE: 0.2,
        ChoiceIntensity.AGONIZING: 0.05     # Almost no freedom
    }
    
    # The 2/3 determination ratio from Free Will Sweet Spot
    DETERMINATION_RATIO = 2/3
    FREE_PORTION = 1/3
    
    def analyze_choice(self, choice_description: str, 
                       intensity: ChoiceIntensity,
                       outcome_gile: float = 0.0) -> FreeWillAnalysis:
        """
        Analyze how free a choice actually is based on its intensity
        
        Args:
            choice_description: What the choice is about
            intensity: How much effort/struggle the choice required
            outcome_gile: The GILE score of the resulting action (-3 to +2)
        
        Returns:
            Complete analysis of the choice's true freedom
        """
        # Calculate actual freedom (inverse of intensity)
        actual_freedom = self.INTENSITY_TO_FREEDOM[intensity]
        
        # Check flow state (effortless = flow)
        flow_state = intensity in [ChoiceIntensity.EFFORTLESS, ChoiceIntensity.LIGHT]
        
        # Calculate GILE alignment
        # High intensity usually means fighting against natural GILE direction
        if intensity == ChoiceIntensity.EFFORTLESS:
            gile_alignment = 0.95  # Almost perfectly aligned
        elif intensity == ChoiceIntensity.LIGHT:
            gile_alignment = 0.75
        elif intensity == ChoiceIntensity.MODERATE:
            gile_alignment = 0.50  # Neutral
        elif intensity == ChoiceIntensity.INTENSE:
            gile_alignment = 0.25  # Fighting the current
        else:  # AGONIZING
            gile_alignment = 0.05  # Severely misaligned
        
        # GM alignment check
        gm_aligned = actual_freedom > 0.5 and gile_alignment > 0.5
        
        # Generate paradox explanation
        explanation = self._generate_explanation(intensity, actual_freedom, gm_aligned)
        
        return FreeWillAnalysis(
            stated_choice=choice_description,
            intensity=intensity,
            actual_freedom=actual_freedom,
            gile_alignment=gile_alignment,
            flow_state=flow_state,
            gm_aligned=gm_aligned,
            paradox_explanation=explanation
        )
    
    def _generate_explanation(self, intensity: ChoiceIntensity,
                             actual_freedom: float,
                             gm_aligned: bool) -> str:
        """Generate explanation of the paradox for this choice"""
        
        if intensity == ChoiceIntensity.EFFORTLESS:
            return (
                "MAXIMUM FREEDOM: This choice flowed naturally, indicating perfect "
                "GM alignment. You didn't 'choose' in the ego sense - the right path "
                "was obvious. This is true free will: alignment with optimal GILE."
            )
        
        elif intensity == ChoiceIntensity.LIGHT:
            return (
                "HIGH FREEDOM: Minor deliberation suggests mostly GM-aligned action. "
                "The 'choice' was more like noticing which direction felt right. "
                "Your i-cell intuition guided you efficiently."
            )
        
        elif intensity == ChoiceIntensity.MODERATE:
            return (
                "MODERATE FREEDOM: Normal deliberation indicates a genuine choice point. "
                "Multiple paths were viable. Some energy was spent deciding, but not "
                "excessively. This is typical human decision-making."
            )
        
        elif intensity == ChoiceIntensity.INTENSE:
            return (
                "LOW FREEDOM: Intense struggle indicates you were fighting against "
                "natural GILE flow. The 'freedom' you felt was actually CONSTRAINT. "
                "True freedom wouldn't require this much effort. Consider: why was "
                "this choice so hard? You may be resisting GM's optimal path."
            )
        
        else:  # AGONIZING
            return (
                "MINIMAL FREEDOM: Agonizing choice = severe misalignment. You are "
                "not exercising 'strong free will' - you are TRAPPED between options, "
                "none of which align with your i-cell's natural direction. This level "
                "of intensity signals that BOTH options may be anti-GILE. The truly "
                "free action might be to reject the entire frame and seek a third path."
            )
    
    def get_freedom_formula(self) -> str:
        """Return the mathematical formulation of the paradox"""
        return """
        FREE WILL INTENSITY PARADOX - Mathematical Formulation
        ═══════════════════════════════════════════════════════
        
        Let I = Intensity of choosing (0 to ∞)
        Let F = Actual freedom (0 to 1)
        Let G = GILE alignment (0 to 1)
        
        CORE EQUATION:
            F = 1 / (1 + I)
        
        As intensity increases, freedom approaches zero.
        As intensity decreases to zero, freedom approaches 1.
        
        GILE RELATIONSHIP:
            G ≈ F (alignment correlates with effortlessness)
        
        When GILE-aligned:
            - Choices feel effortless (I → 0)
            - Freedom is maximized (F → 1)
            - Flow state achieved
        
        When anti-GILE:
            - Choices feel agonizing (I → ∞)
            - Freedom approaches zero (F → 0)
            - Ego struggles against natural path
        
        THE PARADOX RESOLVED:
            "Strong free will" (high intensity) = Low actual freedom
            "Going with the flow" (low intensity) = High actual freedom
            
            The person who THINKS they're most free (intense chooser)
            is actually the LEAST free (fighting against GM alignment).
        """


class FlowStateDetector:
    """
    Detect flow state based on choice intensity
    
    Flow = Effortless action = Maximum freedom = Highest GILE
    """
    
    FLOW_INDICATORS = [
        "felt natural",
        "obvious choice",
        "didn't think about it",
        "just knew",
        "flowed",
        "intuition said",
        "no hesitation",
        "clear path"
    ]
    
    STRUGGLE_INDICATORS = [
        "couldn't decide",
        "agonized over",
        "pros and cons",
        "kept going back and forth",
        "stressed about",
        "forced myself",
        "had to convince",
        "battled with"
    ]
    
    @classmethod
    def detect_from_description(cls, description: str) -> Tuple[bool, float]:
        """
        Detect if a choice description indicates flow state
        
        Returns:
            (is_flow_state, confidence)
        """
        desc_lower = description.lower()
        
        flow_count = sum(1 for ind in cls.FLOW_INDICATORS if ind in desc_lower)
        struggle_count = sum(1 for ind in cls.STRUGGLE_INDICATORS if ind in desc_lower)
        
        total = flow_count + struggle_count
        if total == 0:
            return (False, 0.5)  # Neutral, uncertain
        
        flow_ratio = flow_count / total
        is_flow = flow_ratio > 0.5
        confidence = abs(flow_ratio - 0.5) * 2  # 0 to 1
        
        return (is_flow, confidence)


class TwoThirdsIntegration:
    """
    Integration with the Free Will Sweet Spot (2/3 determined)
    
    Key insight: The 1/3 "free" portion should feel EFFORTLESS.
    If it feels intense, you're fighting the 2/3 determined part.
    """
    
    @staticmethod
    def explain_integration() -> str:
        return """
        INTEGRATION WITH FREE WILL SWEET SPOT (2/3 DETERMINED)
        ══════════════════════════════════════════════════════
        
        The TI Framework establishes:
        - 2/3 of any action is already determined (by GM, environment, past)
        - 1/3 is the "free" portion where choice matters
        
        NEW INSIGHT - The Intensity Paradox reveals:
        - The 1/3 free portion should feel EFFORTLESS
        - If choosing feels INTENSE, you're fighting the 2/3
        - True freedom = smoothly navigating the 1/3
        - False freedom = struggling against the 2/3
        
        WHAT INTENSE CHOOSING MEANS:
        1. You're trying to override the determined 2/3
        2. You're misaligned with GM's optimal path
        3. Your ego wants something different than your i-cell
        4. You're expending energy that should be conserved
        
        THE RESOLUTION:
        - Accept the 2/3 (it's already determined anyway)
        - Navigate the 1/3 with effortless intuition
        - Intensity = signal to reconsider the entire frame
        - Effortlessness = signal you're on the right path
        
        PRACTICAL IMPLICATION:
        When a choice feels agonizing, STOP.
        Ask: "Am I fighting against what's already determined?"
        The answer is usually yes.
        """


# Demonstration
if __name__ == "__main__":
    print("=" * 70)
    print("FREE WILL INTENSITY PARADOX")
    print("'The more intense the free will, the less free and GILE it actually is!'")
    print("=" * 70)
    
    analyzer = FreeWillIntensityAnalyzer()
    
    # Test cases
    test_cases = [
        ("What to eat for breakfast", ChoiceIntensity.EFFORTLESS),
        ("Which route to take to work", ChoiceIntensity.LIGHT),
        ("Whether to take a new job offer", ChoiceIntensity.MODERATE),
        ("Whether to end a relationship", ChoiceIntensity.INTENSE),
        ("Life-or-death ethical dilemma", ChoiceIntensity.AGONIZING),
    ]
    
    print("\n--- Choice Analysis ---\n")
    
    for choice, intensity in test_cases:
        result = analyzer.analyze_choice(choice, intensity)
        
        print(f"Choice: {choice}")
        print(f"  Intensity: {intensity.value.upper()}")
        print(f"  Actual Freedom: {result.actual_freedom:.0%}")
        print(f"  GILE Alignment: {result.gile_alignment:.0%}")
        print(f"  Flow State: {'Yes' if result.flow_state else 'No'}")
        print(f"  GM Aligned: {'Yes' if result.gm_aligned else 'No'}")
        print(f"  Explanation: {result.paradox_explanation[:100]}...")
        print()
    
    print("=" * 70)
    print("THE FORMULA:")
    print("=" * 70)
    print(analyzer.get_freedom_formula())
    
    print("\n" + "=" * 70)
    print("INTEGRATION WITH 2/3 DETERMINED:")
    print("=" * 70)
    print(TwoThirdsIntegration.explain_integration())
    
    print("\n" + "=" * 70)
    print("KEY INSIGHT:")
    print("=" * 70)
    print("""
    The person who BRAGS about their "strong free will"
    (agonizes over decisions, fights against circumstances,
    forces outcomes through sheer determination)
    
    ...is actually the LEAST free person in the room.
    
    True freedom looks like EASE.
    True freedom feels like FLOW.
    True freedom IS effortless alignment with GILE.
    
    The universe (GM) already optimized the path.
    Your only job is to STOP RESISTING IT.
    """)
    
    print("\n" + "=" * 70)
    print("THE GRAND CONCLUSION - Civilization Has It Backwards:")
    print("=" * 70)
    print("""
    ┌─────────────────────────────────────────────────────────────────┐
    │          THE ANTI-GILE LIE CIVILIZATION TEACHES                 │
    ├─────────────────────────────────────────────────────────────────┤
    │  "No pain, no gain"                                             │
    │  "Struggle builds character"                                    │
    │  "If it's hard, it's worth doing"                              │
    │  "Suffering is noble"                                           │
    │  "Fight for what you want"                                      │
    └─────────────────────────────────────────────────────────────────┘
    
    THIS IS PRECISELY BACKWARDS.
    
    ┌─────────────────────────────────────────────────────────────────┐
    │              THE GILE TRUTH                                     │
    ├─────────────────────────────────────────────────────────────────┤
    │  True health = Stimulations you BOTH want AND need              │
    │  True growth = Effortless expansion, not forced pain            │
    │  True success = Flow state, not grinding resistance             │
    │  True freedom = Ease of choice, not agonizing deliberation      │
    │  True GILE = Natural alignment, NOT high compulsion/effort      │
    └─────────────────────────────────────────────────────────────────┘
    
    THE MECHANISM:
    - When something is BOTH wanted AND needed → it flows effortlessly
    - When something is wanted but NOT needed → compulsion/addiction
    - When something is needed but NOT wanted → grinding/suffering
    - When something is neither → why do it at all?
    
    THE SWEET SPOT:
        WANT ∩ NEED = GILE-Optimal Action = Effortless = True Freedom
    
    Pain indicates MISALIGNMENT, not virtue.
    Struggle signals WRONG PATH, not character building.
    Effort without joy is ANTI-GILE, not noble sacrifice.
    
    The civilization that glorifies suffering has been
    systematically optimizing for ANTI-GILE outcomes.
    
    GM's path feels like HOME.
    Not like war.
    """)
    
    print("\n" + "=" * 70)
    print("THE ASCETICISM NUANCE - Why GILE Beats Suffering:")
    print("=" * 70)
    print("""
    ACKNOWLEDGMENT (per "The Sweet Spot" / Paul Bloom):
    - Suffering CAN produce growth in some cases
    - Asceticism has documented benefits
    - People ARE irrational and sometimes find meaning in pain
    - Goodness CAN result even BECAUSE of suffering
    
    BUT HERE'S THE CRITICAL INSIGHT:
    
    ┌─────────────────────────────────────────────────────────────────┐
    │     SUFFERING PATH           vs        GILE PATH               │
    ├─────────────────────────────────────────────────────────────────┤
    │  Slow learning                    Fast learning                │
    │  Painful process                  Effortless process           │
    │  High cost                        Low cost                     │
    │  Uncertain outcomes               Reliable outcomes            │
    │  Trauma risk                      Growth guarantee             │
    │  Burns out i-cell                 Nourishes i-cell             │
    └─────────────────────────────────────────────────────────────────┘
    
    THE ROI CALCULATION:
    
    Suffering ROI = Benefit / (Pain + Time + Trauma Risk)
                  = Low efficiency
    
    GILE ROI      = Benefit / (Ease + Speed + Joy)
                  = High efficiency
    
    EVEN IF suffering produces SOME benefit, GILE produces:
    - The SAME benefit (or more)
    - FASTER
    - With LESS cost
    - And with PLEASURE instead of pain
    
    THE CONCLUSION:
    Asceticism's benefits AREN'T WORTH THE COST
    when GILE can teach you:
        - Faster
        - Better
        - With ease
    
    Suffering is the SLOW, EXPENSIVE, RISKY path.
    GILE is the FAST, CHEAP, SAFE path.
    
    Why take the scenic route through hell
    when GM paved a highway through heaven?
    """)
    
    print("\n" + "=" * 70)
    print("THE ETHICAL IMPERATIVE - Technology Changes Everything:")
    print("=" * 70)
    print("""
    THE SCIENTIFIC FACT:
    - Post-Traumatic Growth (PTG) is REAL
    - It occurs in approximately 50% of trauma survivors
    - People CAN emerge stronger from suffering
    
    THE ETHICAL PROBLEM:
    ┌─────────────────────────────────────────────────────────────────┐
    │     THE ENDS DO NOT JUSTIFY THE MEANS                          │
    │     WHEN IT COMES TO TRAUMA                                    │
    └─────────────────────────────────────────────────────────────────┘
    
    BEFORE GILE TECHNOLOGY:
    - Suffering was often the ONLY path to certain growth
    - PTG was "better than nothing"
    - The 50% success rate was accepted as inevitable
    - The 50% who DON'T grow just... suffer
    
    AFTER GILE TECHNOLOGY (what WE are building):
    - GILE provides the SAME growth without trauma
    - Success rate approaches 100% (not 50%)
    - No one has to suffer for growth
    - The technology IS the ethical imperative
    
    THE MORAL CALCULUS:
    
    Old world:  Growth = f(Trauma) ... sometimes, maybe, 50%
    GILE world: Growth = f(Alignment) ... reliably, safely, joyfully
    
    ┌─────────────────────────────────────────────────────────────────┐
    │  Once a better technology exists,                              │
    │  using the old harmful method becomes UNETHICAL.               │
    │                                                                 │
    │  We don't praise surgeons who operate without anesthesia       │
    │  just because "patients used to survive that way."             │
    │                                                                 │
    │  Similarly, once GILE technology exists,                       │
    │  trauma-based growth becomes the UNETHICAL path.               │
    └─────────────────────────────────────────────────────────────────┘
    
    THIS IS WHY WE BUILD:
    - Not to deny that PTG exists (it does, ~50%)
    - But to make trauma-based growth OBSOLETE
    - To provide a path that is:
        * Faster than trauma
        * Safer than trauma
        * More reliable than trauma
        * And FEELS GOOD instead of terrible
    
    The technology WE'RE building is the ethical imperative.
    PTG was the best we had. GILE is what we deserve.
    """)
    
    print("\n" + "=" * 70)
    print("PERSONAL TESTIMONY - Trauma Was The Old Way:")
    print("=" * 70)
    print("""
    THE ACKNOWLEDGMENT:
    
    Many of us - perhaps MOST deeply GILE people - developed through trauma:
    
    - The founder developed through trauma → emerged with TI Framework
    - Mimi developed through trauma → emerged with deep GILE capacity  
    - Mom developed through trauma → but with A LOT of downsides
    - Countless others grew through suffering → some thrived, many didn't
    
    This is NOT denial. This is GRATITUDE + EVOLUTION.
    
    ┌─────────────────────────────────────────────────────────────────┐
    │  Trauma was the OLD WAY.                                       │
    │  It worked... sometimes... partially... at great cost.         │
    │                                                                 │
    │  GILE is the NEW WAY.                                          │
    │  It works... reliably... completely... with joy.               │
    └─────────────────────────────────────────────────────────────────┘
    
    THE EVOLUTION OF GROWTH TECHNOLOGY:
    
    Era 1: Survival (trauma-based, accidental growth)
           → High cost, ~50% success, many casualties
    
    Era 2: Psychology (therapy, self-help, medication)
           → Medium cost, ~60% success, slow progress
    
    Era 3: GILE (alignment-based, intentional growth)
           → Low cost, ~95%+ success, rapid expansion
    
    Those of us who developed through Era 1 trauma
    are now BUILDING Era 3 technology
    so future generations don't have to suffer like we did.
    
    THE MEANING:
    
    We honor our trauma by making it OBSOLETE.
    We honor our growth by making it ACCESSIBLE.
    We honor our suffering by ensuring others don't have to.
    
    Trauma built us. Now we build GILE.
    The old way created the builders of the new way.
    That's not irony - that's GM's plan all along.
    """)
