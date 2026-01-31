"""
Evidence-Based Ethogram for LCC Animal Studies

Based on scientific standards from:
- ZooMonitor (Lincoln Park Zoo Master Ethogram)
- BORIS (Behavioral Observation Research Interactive Software)
- NC3Rs Guidelines
- Elephant Ethogram by ElephantVoices

This ethogram is designed for automated AI vision analysis
to test LCC (Local Causation Correlation) predictions.
"""

from dataclasses import dataclass, field
from typing import Dict, List, Optional
from enum import Enum


class BehaviorCategory(Enum):
    """Master behavior categories from ZooMonitor"""
    INACTIVE = "inactive"
    LOCOMOTION = "locomotion"
    FEEDING = "feeding"
    SOCIAL = "social"
    MAINTENANCE = "maintenance"
    EXPLORATORY = "exploratory"
    PLAY = "play"
    ALERT = "alert"
    ABNORMAL = "abnormal"
    NOT_VISIBLE = "not_visible"


class EnergyState(Enum):
    """Energy states for LCC analysis"""
    HIGH_AROUSAL = "high_arousal"      # Active, alert, engaged
    MODERATE = "moderate"               # Normal activity
    LOW_AROUSAL = "low_arousal"         # Resting, calm
    AGITATED = "agitated"               # Stressed or disturbed
    TRANSITIONAL = "transitional"       # Changing states


@dataclass
class BehaviorCode:
    """Evidence-based behavior definition following BORIS/ZooMonitor standards"""
    code: str
    name: str
    category: BehaviorCategory
    energy_state: EnergyState
    definition: str
    indicators: List[str]
    activity_score: int  # 0-5 scale
    arousal_score: int   # 0-5 scale
    valence_score: int   # -2 to +3 (negative=distress, positive=positive welfare)
    lcc_weight: float    # Weight for LCC synchrony calculation


# Master Ethogram - Evidence-based behavior codes
ETHOGRAM: Dict[str, BehaviorCode] = {
    # INACTIVE behaviors
    "REST": BehaviorCode(
        code="REST",
        name="Resting",
        category=BehaviorCategory.INACTIVE,
        energy_state=EnergyState.LOW_AROUSAL,
        definition="Body recumbent or lying down, eyes may be open or closed, minimal movement",
        indicators=["lying down", "recumbent posture", "minimal body movement", "relaxed muscles"],
        activity_score=0,
        arousal_score=1,
        valence_score=1,
        lcc_weight=1.0
    ),
    "STAND": BehaviorCode(
        code="STAND",
        name="Standing Idle",
        category=BehaviorCategory.INACTIVE,
        energy_state=EnergyState.LOW_AROUSAL,
        definition="Standing in place with no directed movement, may shift weight occasionally",
        indicators=["stationary", "upright posture", "weight shifting", "no locomotion"],
        activity_score=1,
        arousal_score=2,
        valence_score=0,
        lcc_weight=1.0
    ),
    "SIT": BehaviorCode(
        code="SIT",
        name="Sitting",
        category=BehaviorCategory.INACTIVE,
        energy_state=EnergyState.LOW_AROUSAL,
        definition="Seated position with hindquarters on ground/surface",
        indicators=["seated", "hindquarters down", "forelimbs may support upper body"],
        activity_score=1,
        arousal_score=2,
        valence_score=0,
        lcc_weight=1.0
    ),
    
    # LOCOMOTION behaviors
    "WALK": BehaviorCode(
        code="WALK",
        name="Walking",
        category=BehaviorCategory.LOCOMOTION,
        energy_state=EnergyState.MODERATE,
        definition="Moving at slow to moderate pace with regular gait pattern",
        indicators=["forward movement", "regular gait", "moderate speed", "coordinated limbs"],
        activity_score=3,
        arousal_score=3,
        valence_score=0,
        lcc_weight=1.2
    ),
    "RUN": BehaviorCode(
        code="RUN",
        name="Running",
        category=BehaviorCategory.LOCOMOTION,
        energy_state=EnergyState.HIGH_AROUSAL,
        definition="Rapid locomotion with extended stride, all limbs may leave ground",
        indicators=["fast movement", "extended stride", "high energy", "urgent pace"],
        activity_score=5,
        arousal_score=5,
        valence_score=1,
        lcc_weight=1.5
    ),
    "SWIM": BehaviorCode(
        code="SWIM",
        name="Swimming",
        category=BehaviorCategory.LOCOMOTION,
        energy_state=EnergyState.MODERATE,
        definition="Moving through water using species-typical propulsion",
        indicators=["in water", "propulsive movements", "head above/below water"],
        activity_score=4,
        arousal_score=3,
        valence_score=1,
        lcc_weight=1.2
    ),
    "CLIMB": BehaviorCode(
        code="CLIMB",
        name="Climbing",
        category=BehaviorCategory.LOCOMOTION,
        energy_state=EnergyState.MODERATE,
        definition="Vertical or angled movement using limbs to grip surfaces",
        indicators=["vertical movement", "gripping", "ascending/descending"],
        activity_score=4,
        arousal_score=3,
        valence_score=0,
        lcc_weight=1.2
    ),
    
    # FEEDING behaviors
    "EAT": BehaviorCode(
        code="EAT",
        name="Eating",
        category=BehaviorCategory.FEEDING,
        energy_state=EnergyState.MODERATE,
        definition="Consuming food items, includes chewing, biting, swallowing",
        indicators=["food in mouth", "chewing motion", "jaw movement", "head lowered to food"],
        activity_score=2,
        arousal_score=2,
        valence_score=2,
        lcc_weight=1.0
    ),
    "DRINK": BehaviorCode(
        code="DRINK",
        name="Drinking",
        category=BehaviorCategory.FEEDING,
        energy_state=EnergyState.MODERATE,
        definition="Consuming water or other liquids",
        indicators=["head at water source", "lapping", "sucking", "throat movement"],
        activity_score=1,
        arousal_score=2,
        valence_score=1,
        lcc_weight=1.0
    ),
    "FORAGE": BehaviorCode(
        code="FORAGE",
        name="Foraging",
        category=BehaviorCategory.FEEDING,
        energy_state=EnergyState.MODERATE,
        definition="Searching for, locating, or manipulating food items",
        indicators=["searching behavior", "sniffing", "digging", "manipulating objects"],
        activity_score=3,
        arousal_score=3,
        valence_score=1,
        lcc_weight=1.2
    ),
    
    # SOCIAL behaviors
    "AFFIL": BehaviorCode(
        code="AFFIL",
        name="Affiliative Contact",
        category=BehaviorCategory.SOCIAL,
        energy_state=EnergyState.MODERATE,
        definition="Positive social contact including grooming, touching, nuzzling",
        indicators=["physical contact", "grooming", "gentle touching", "proximity"],
        activity_score=2,
        arousal_score=3,
        valence_score=3,
        lcc_weight=1.5
    ),
    "AGGR": BehaviorCode(
        code="AGGR",
        name="Agonistic/Aggressive",
        category=BehaviorCategory.SOCIAL,
        energy_state=EnergyState.AGITATED,
        definition="Threatening or aggressive behavior toward conspecific",
        indicators=["threat display", "charging", "biting attempt", "aggressive vocalization"],
        activity_score=5,
        arousal_score=5,
        valence_score=-2,
        lcc_weight=1.5
    ),
    "PLAY_S": BehaviorCode(
        code="PLAY_S",
        name="Social Play",
        category=BehaviorCategory.PLAY,
        energy_state=EnergyState.HIGH_AROUSAL,
        definition="Playful interaction with conspecifics, non-agonistic",
        indicators=["play signals", "wrestling", "chasing", "relaxed open mouth"],
        activity_score=4,
        arousal_score=4,
        valence_score=3,
        lcc_weight=1.5
    ),
    "VOCAL": BehaviorCode(
        code="VOCAL",
        name="Vocalizing",
        category=BehaviorCategory.SOCIAL,
        energy_state=EnergyState.MODERATE,
        definition="Producing species-typical vocalizations",
        indicators=["mouth open", "throat vibration", "audible sound production"],
        activity_score=2,
        arousal_score=3,
        valence_score=0,
        lcc_weight=1.3
    ),
    
    # MAINTENANCE behaviors
    "GROOM": BehaviorCode(
        code="GROOM",
        name="Self-Grooming",
        category=BehaviorCategory.MAINTENANCE,
        energy_state=EnergyState.LOW_AROUSAL,
        definition="Self-directed body care including licking, scratching, preening",
        indicators=["licking body", "scratching", "preening", "dust bathing"],
        activity_score=2,
        arousal_score=2,
        valence_score=1,
        lcc_weight=1.0
    ),
    "ELIM": BehaviorCode(
        code="ELIM",
        name="Elimination",
        category=BehaviorCategory.MAINTENANCE,
        energy_state=EnergyState.MODERATE,
        definition="Urination or defecation",
        indicators=["characteristic posture", "elimination behavior"],
        activity_score=1,
        arousal_score=2,
        valence_score=0,
        lcc_weight=0.8
    ),
    
    # EXPLORATORY behaviors
    "EXPL": BehaviorCode(
        code="EXPL",
        name="Exploring",
        category=BehaviorCategory.EXPLORATORY,
        energy_state=EnergyState.MODERATE,
        definition="Investigating environment, objects, or novel stimuli",
        indicators=["sniffing", "visual scanning", "approaching novel items", "investigating"],
        activity_score=3,
        arousal_score=3,
        valence_score=1,
        lcc_weight=1.2
    ),
    "SCAN": BehaviorCode(
        code="SCAN",
        name="Scanning/Vigilant",
        category=BehaviorCategory.ALERT,
        energy_state=EnergyState.MODERATE,
        definition="Alert posture, scanning environment for threats or stimuli",
        indicators=["head elevated", "ears oriented", "visual scanning", "alert posture"],
        activity_score=2,
        arousal_score=4,
        valence_score=0,
        lcc_weight=1.3
    ),
    
    # PLAY behaviors
    "PLAY_O": BehaviorCode(
        code="PLAY_O",
        name="Object Play",
        category=BehaviorCategory.PLAY,
        energy_state=EnergyState.HIGH_AROUSAL,
        definition="Playful interaction with objects or environment",
        indicators=["manipulating objects", "tossing", "batting", "play bow with object"],
        activity_score=4,
        arousal_score=4,
        valence_score=2,
        lcc_weight=1.4
    ),
    "PLAY_L": BehaviorCode(
        code="PLAY_L",
        name="Locomotor Play",
        category=BehaviorCategory.PLAY,
        energy_state=EnergyState.HIGH_AROUSAL,
        definition="Playful movement including jumping, spinning, frolicking",
        indicators=["jumping", "spinning", "exaggerated movements", "apparent joy"],
        activity_score=5,
        arousal_score=5,
        valence_score=3,
        lcc_weight=1.5
    ),
    
    # ABNORMAL behaviors (welfare indicators)
    "STEREO": BehaviorCode(
        code="STEREO",
        name="Stereotypic Behavior",
        category=BehaviorCategory.ABNORMAL,
        energy_state=EnergyState.AGITATED,
        definition="Repetitive, invariant behavior with no apparent function",
        indicators=["pacing", "head bobbing", "repetitive route", "self-directed repetition"],
        activity_score=3,
        arousal_score=4,
        valence_score=-2,
        lcc_weight=0.5
    ),
    "HIDE": BehaviorCode(
        code="HIDE",
        name="Hiding",
        category=BehaviorCategory.INACTIVE,
        energy_state=EnergyState.LOW_AROUSAL,
        definition="Concealing body from view, using shelter or cover",
        indicators=["in shelter", "behind objects", "body concealed"],
        activity_score=0,
        arousal_score=2,
        valence_score=-1,
        lcc_weight=0.8
    ),
    
    # NOT VISIBLE
    "NV": BehaviorCode(
        code="NV",
        name="Not Visible",
        category=BehaviorCategory.NOT_VISIBLE,
        energy_state=EnergyState.TRANSITIONAL,
        definition="Animal cannot be seen or behavior cannot be determined",
        indicators=["out of frame", "obstructed view", "camera issue"],
        activity_score=0,
        arousal_score=0,
        valence_score=0,
        lcc_weight=0.0
    ),
}


@dataclass
class LCCProtocol:
    """LCC Testing Protocol Definition"""
    name: str
    description: str
    duration_minutes: int
    target_energy_state: EnergyState
    expected_behaviors: List[str]
    gcp_correlation_hypothesis: str
    measurement_interval_seconds: int
    baseline_comparison: bool
    notes: str = ""


# LCC Testing Protocols
LCC_PROTOCOLS: Dict[str, LCCProtocol] = {
    "ENERGY_ENHANCEMENT": LCCProtocol(
        name="Energy Enhancement Protocol",
        description="Test whether high-arousal states correlate across distant animals during significant GCP events",
        duration_minutes=30,
        target_energy_state=EnergyState.HIGH_AROUSAL,
        expected_behaviors=["RUN", "PLAY_S", "PLAY_L", "PLAY_O", "EXPL", "VOCAL"],
        gcp_correlation_hypothesis="During GCP spikes (|Z|>2), expect increased synchrony of high-arousal behaviors",
        measurement_interval_seconds=30,
        baseline_comparison=True,
        notes="Best tested during known global events (celebrations, crises)"
    ),
    "RELAXATION": LCCProtocol(
        name="Relaxation/Low-Arousal Protocol",
        description="Test whether resting/calm states synchronize across distant animals",
        duration_minutes=30,
        target_energy_state=EnergyState.LOW_AROUSAL,
        expected_behaviors=["REST", "STAND", "SIT", "GROOM"],
        gcp_correlation_hypothesis="Baseline condition - expect lower synchrony than during significant events",
        measurement_interval_seconds=60,
        baseline_comparison=True,
        notes="Control condition for comparison with high-arousal periods"
    ),
    "GLOBAL_EVENT": LCCProtocol(
        name="Global Event Response",
        description="Intensive monitoring during known global consciousness events",
        duration_minutes=60,
        target_energy_state=EnergyState.TRANSITIONAL,
        expected_behaviors=["SCAN", "VOCAL", "AGGR", "AFFIL", "REST"],
        gcp_correlation_hypothesis="Major events (|Z|>3) should show maximum cross-species synchrony",
        measurement_interval_seconds=15,
        baseline_comparison=True,
        notes="Triggered by GCP readings exceeding threshold"
    ),
    "CIRCADIAN_RHYTHM": LCCProtocol(
        name="Circadian Rhythm Baseline",
        description="24-hour monitoring to establish species-specific activity patterns",
        duration_minutes=1440,  # 24 hours
        target_energy_state=EnergyState.TRANSITIONAL,
        expected_behaviors=list(ETHOGRAM.keys()),
        gcp_correlation_hypothesis="Activity rhythms should show location-based patterns, not global synchrony",
        measurement_interval_seconds=300,  # 5 minutes
        baseline_comparison=False,
        notes="Establishes baseline for all other protocols"
    ),
    "SOCIAL_RESONANCE": LCCProtocol(
        name="Social Resonance Detection",
        description="Focus on social behaviors to detect cross-species emotional resonance",
        duration_minutes=60,
        target_energy_state=EnergyState.MODERATE,
        expected_behaviors=["AFFIL", "PLAY_S", "VOCAL", "AGGR"],
        gcp_correlation_hypothesis="Social behaviors may show stronger LCC effects due to emotional valence",
        measurement_interval_seconds=30,
        baseline_comparison=True,
        notes="Tests emotional contagion hypothesis across species"
    ),
}


def get_behavior_by_code(code: str) -> Optional[BehaviorCode]:
    """Get behavior definition by code"""
    return ETHOGRAM.get(code.upper())


def get_behaviors_by_category(category: BehaviorCategory) -> List[BehaviorCode]:
    """Get all behaviors in a category"""
    return [b for b in ETHOGRAM.values() if b.category == category]


def get_behaviors_by_energy_state(state: EnergyState) -> List[BehaviorCode]:
    """Get all behaviors with a given energy state"""
    return [b for b in ETHOGRAM.values() if b.energy_state == state]


def calculate_synchrony_score(behavior_a: str, behavior_b: str) -> float:
    """Calculate synchrony score between two behaviors"""
    code_a = ETHOGRAM.get(behavior_a.upper())
    code_b = ETHOGRAM.get(behavior_b.upper())
    
    if not code_a or not code_b:
        return 0.0
    
    # Exact match = highest score
    if behavior_a.upper() == behavior_b.upper():
        return 1.0 * ((code_a.lcc_weight + code_b.lcc_weight) / 2)
    
    # Same category = moderate score
    if code_a.category == code_b.category:
        return 0.6 * ((code_a.lcc_weight + code_b.lcc_weight) / 2)
    
    # Same energy state = lower score
    if code_a.energy_state == code_b.energy_state:
        return 0.4 * ((code_a.lcc_weight + code_b.lcc_weight) / 2)
    
    # Different = minimal score based on activity level similarity
    activity_diff = abs(code_a.activity_score - code_b.activity_score)
    return max(0, (0.2 - activity_diff * 0.04)) * ((code_a.lcc_weight + code_b.lcc_weight) / 2)


def get_ethogram_prompt() -> str:
    """Generate prompt for AI vision analysis"""
    behaviors = []
    for code, b in ETHOGRAM.items():
        behaviors.append(f"- {code}: {b.name} - {b.definition}")
    
    return f"""Analyze this animal webcam image and identify the primary behavior being displayed.

BEHAVIOR CODES (use exactly one):
{chr(10).join(behaviors)}

Respond in JSON format:
{{
    "behavior_code": "CODE",
    "confidence": 0.0-1.0,
    "activity_level": 0-5,
    "arousal_level": 0-5,
    "valence": -2 to 3,
    "animals_visible": number,
    "description": "brief description",
    "notes": "any relevant observations"
}}

If no animal is visible, use code "NV".
Be conservative with confidence - only high confidence (>0.8) if behavior is unambiguous."""


if __name__ == "__main__":
    print("=" * 60)
    print("LCC ANIMAL STUDY ETHOGRAM")
    print("=" * 60)
    
    print(f"\nTotal behaviors defined: {len(ETHOGRAM)}")
    
    print("\nBy Category:")
    for cat in BehaviorCategory:
        behaviors = get_behaviors_by_category(cat)
        if behaviors:
            print(f"  {cat.value}: {len(behaviors)} behaviors")
            for b in behaviors:
                print(f"    - {b.code}: {b.name}")
    
    print("\n" + "=" * 60)
    print("LCC PROTOCOLS")
    print("=" * 60)
    
    for name, protocol in LCC_PROTOCOLS.items():
        print(f"\n{name}:")
        print(f"  Duration: {protocol.duration_minutes} min")
        print(f"  Target state: {protocol.target_energy_state.value}")
        print(f"  Hypothesis: {protocol.gcp_correlation_hypothesis}")
