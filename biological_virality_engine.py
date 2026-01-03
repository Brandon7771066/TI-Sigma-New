"""
Biological Virality Engine
Models concept spread using REAL virology + acoustic resonance theory

CORE INSIGHT: Ideas don't "spread" linearly - they RESONATE harmonically!
Viral content = Perfect frequency match with audience's i-cell oscillation

KEY MECHANISMS:
1. R0 (Basic Reproduction Number) - How many people does one infected person share with?
2. Mutation Rate - How fast does the concept evolve as it spreads?
3. Host Susceptibility - What GILE state makes someone receptive?
4. Transmission Vector - Which platform amplifies this frequency?
5. Acoustic Resonance - Does it harmonize with existing beliefs?
"""

from typing import Dict, List, Any, Tuple, Optional
from dataclasses import dataclass
from enum import Enum
import math


class TransmissionVector(Enum):
    """Social media platforms as viral transmission vectors"""
    TIKTOK = "tiktok"          # High R0, short incubation, youth susceptible
    TWITTER = "twitter"        # Medium R0, instant transmission, controversy-driven
    YOUTUBE = "youtube"        # Low R0, long incubation, deep engagement
    INSTAGRAM = "instagram"    # Medium R0, visual transmission, aesthetic susceptible
    LINKEDIN = "linkedin"      # Low R0, professional filter, credibility-driven
    PODCAST = "podcast"        # Very low R0, very long incubation, high retention
    BOOK = "book"              # Ultra-low R0, ultra-long incubation, permanent impact


class HostSusceptibility(Enum):
    """Audience GILE states and their viral susceptibility"""
    LOW_GILE = "low_gile"              # Desperate for dopamine → susceptible to junk
    NEUTRAL_GILE = "neutral_gile"      # Moderate filtering → susceptible to emotion
    HIGH_GILE = "high_gile"            # Strong discernment → only resonant truth spreads
    CRISIS_STATE = "crisis"            # Existential seeking → susceptible to meaning
    FLOW_STATE = "flow"                # Peak performance → susceptible to optimization


@dataclass
class ConceptGenome:
    """The 'genetic code' of a viral concept"""
    core_idea: str                     # Central thesis (immutable like DNA)
    memetic_packaging: str             # How it's presented (mutable like protein coat)
    emotional_payload: str             # What emotion it triggers (viral mechanism)
    cognitive_load: float              # How hard to understand (0-1, 0=easy)
    gile_signature: Tuple[float, float, float, float]  # (G, I, L, E) resonance frequency
    novelty_score: float               # How new/surprising (0-1)
    actionability: float               # Can you DO something with it? (0-1)


@dataclass
class ViralMetrics:
    """Epidemiological metrics for concept spread"""
    R0: float                          # Basic reproduction number (shares per person)
    mutation_rate: float               # How fast it evolves (0-1 per transmission)
    incubation_period: float           # Time to "get it" (hours)
    infection_duration: float          # How long it stays in mind (days)
    herd_immunity_threshold: float     # % exposed before spread stops
    doubling_time: float               # Hours to double infected population
    peak_virality_time: float          # When does it hit maximum spread? (days)


@dataclass
class AcousticProperties:
    """Musical/acoustic properties of concept resonance"""
    fundamental_frequency: float       # Core GILE frequency (Hz)
    harmonic_richness: float          # Number of overtones (meanings)
    dissonance_level: float           # Cognitive dissonance (0-1)
    amplitude: float                  # Emotional intensity (0-1)
    resonance_bandwidth: float        # Range of frequencies it couples with
    beat_frequency: Optional[float]   # Controversy = two interfering frequencies


class BiologicalViralityEngine:
    """
    Models concept spread using epidemiology + acoustic resonance
    """
    
    # Platform-specific R0 multipliers (how much each platform amplifies spread)
    PLATFORM_R0_MULTIPLIERS = {
        TransmissionVector.TIKTOK: 5.2,        # Extremely high viral coefficient
        TransmissionVector.TWITTER: 2.8,       # Moderate viral coefficient
        TransmissionVector.YOUTUBE: 1.4,       # Lower but more stable
        TransmissionVector.INSTAGRAM: 2.1,     # Visual boost
        TransmissionVector.LINKEDIN: 0.9,      # Professional filter reduces spread
        TransmissionVector.PODCAST: 0.6,       # Very targeted audience
        TransmissionVector.BOOK: 0.3,          # Slow burn, long tail
    }
    
    # Susceptibility by GILE state (how likely to share)
    GILE_SUSCEPTIBILITY = {
        HostSusceptibility.LOW_GILE: 0.85,       # Will share anything dopaminergic
        HostSusceptibility.NEUTRAL_GILE: 0.55,   # Moderate filtering
        HostSusceptibility.HIGH_GILE: 0.25,      # Strong discernment
        HostSusceptibility.CRISIS_STATE: 0.95,   # Desperate for answers
        HostSusceptibility.FLOW_STATE: 0.40,     # Selective sharing
    }
    
    def __init__(self):
        pass
    
    def calculate_R0(
        self,
        genome: ConceptGenome,
        platform: TransmissionVector,
        target_audience: HostSusceptibility
    ) -> float:
        """
        Calculate Basic Reproduction Number (R0)
        R0 = (Base shareability) × (Platform amplification) × (Audience susceptibility)
        
        R0 < 1: Concept dies out
        R0 = 1: Endemic (stable spread)
        R0 > 1: Epidemic (exponential growth)
        R0 > 3: Pandemic potential
        """
        # Base shareability from concept properties
        base_shareability = self._calculate_base_shareability(genome)
        
        # Platform amplification
        platform_multiplier = self.PLATFORM_R0_MULTIPLIERS[platform]
        
        # Audience susceptibility
        susceptibility = self.GILE_SUSCEPTIBILITY[target_audience]
        
        R0 = base_shareability * platform_multiplier * susceptibility
        
        return R0
    
    def _calculate_base_shareability(self, genome: ConceptGenome) -> float:
        """
        Calculate intrinsic shareability of concept
        Based on: emotion, novelty, actionability, cognitive load
        """
        # Emotional payload (higher = more shareable)
        emotion_factor = self._score_emotion(genome.emotional_payload)
        
        # Novelty (U-shaped: too familiar OR too novel both work)
        novelty_factor = min(genome.novelty_score, 1 - genome.novelty_score) * 2
        
        # Actionability (can you DO something?)
        action_factor = genome.actionability
        
        # Cognitive load (INVERSE: easier = more viral)
        ease_factor = 1 - genome.cognitive_load
        
        # GILE magnitude (how "strong" is the concept?)
        gile_magnitude = sum(genome.gile_signature) / 4
        
        # Combine factors (weighted average)
        base = (
            emotion_factor * 0.35 +      # Emotion is PRIMARY driver
            novelty_factor * 0.25 +      # Novelty gets attention
            action_factor * 0.20 +       # Actionable content spreads
            ease_factor * 0.15 +         # Easy concepts spread faster
            gile_magnitude * 0.05        # GILE quality (minor factor for virality)
        )
        
        return base
    
    def _score_emotion(self, emotion: str) -> float:
        """
        Score emotional payload for viral potential
        High-arousal emotions spread faster (anger, awe, excitement)
        Low-arousal emotions spread slower (sadness, contentment)
        """
        emotion_scores = {
            # High-arousal positive
            'awe': 0.95,
            'excitement': 0.90,
            'inspiration': 0.85,
            'joy': 0.80,
            
            # High-arousal negative
            'anger': 0.95,
            'outrage': 0.92,
            'fear': 0.88,
            'anxiety': 0.75,
            
            # Medium-arousal
            'surprise': 0.70,
            'curiosity': 0.65,
            'validation': 0.60,
            
            # Low-arousal positive
            'contentment': 0.40,
            'peace': 0.35,
            'gratitude': 0.30,
            
            # Low-arousal negative
            'sadness': 0.50,
            'melancholy': 0.45,
            'disappointment': 0.42,
        }
        
        return emotion_scores.get(emotion.lower(), 0.50)
    
    def calculate_mutation_rate(self, genome: ConceptGenome, platform: TransmissionVector) -> float:
        """
        Calculate mutation rate (how fast concept evolves as it spreads)
        
        High mutation = Concept gets remixed/adapted (memes!)
        Low mutation = Concept stays pure (quotes, facts)
        """
        # Core idea complexity affects mutation
        # Simple ideas mutate more (easier to remix)
        simplicity_factor = 1 - genome.cognitive_load
        
        # Actionability increases mutation (people try variations)
        action_factor = genome.actionability
        
        # Platform effect (TikTok = high mutation, Books = low mutation)
        platform_mutation_rates = {
            TransmissionVector.TIKTOK: 0.85,
            TransmissionVector.TWITTER: 0.70,
            TransmissionVector.INSTAGRAM: 0.65,
            TransmissionVector.YOUTUBE: 0.45,
            TransmissionVector.LINKEDIN: 0.30,
            TransmissionVector.PODCAST: 0.20,
            TransmissionVector.BOOK: 0.10,
        }
        
        platform_factor = platform_mutation_rates[platform]
        
        # Combine
        mutation_rate = (
            simplicity_factor * 0.3 +
            action_factor * 0.2 +
            platform_factor * 0.5
        )
        
        return mutation_rate
    
    def calculate_acoustic_resonance(
        self,
        genome: ConceptGenome,
        audience_gile: Tuple[float, float, float, float]
    ) -> AcousticProperties:
        """
        Calculate acoustic/musical properties of concept resonance
        
        KEY INSIGHT: Concepts spread through HARMONIC COUPLING, not contagion!
        When concept frequency matches audience frequency → RESONANCE!
        """
        # Fundamental frequency = average GILE score
        # Map GILE (-3 to +2) to frequency range (50Hz - 500Hz)
        concept_gile_avg = sum(genome.gile_signature) / 4
        fundamental_freq = self._gile_to_frequency(concept_gile_avg)
        
        audience_gile_avg = sum(audience_gile) / 4
        audience_freq = self._gile_to_frequency(audience_gile_avg)
        
        # Harmonic richness = how many "meanings" does concept have?
        # Complex ideas have more overtones
        harmonic_richness = (1 - genome.cognitive_load) * 5 + genome.novelty_score * 3
        
        # Dissonance = frequency mismatch between concept and audience
        frequency_diff = abs(fundamental_freq - audience_freq)
        dissonance = min(frequency_diff / 100, 1.0)  # Normalize to 0-1
        
        # Amplitude = emotional intensity
        amplitude = self._score_emotion(genome.emotional_payload)
        
        # Resonance bandwidth = how wide a range of frequencies it couples with
        # High novelty + low cognitive load = wider bandwidth
        resonance_bandwidth = genome.novelty_score * 50 + (1 - genome.cognitive_load) * 30
        
        # Beat frequency = if there's controversy (two conflicting ideas)
        # Detectable when dissonance is moderate (not too aligned, not too different)
        beat_frequency = None
        if 0.2 < dissonance < 0.6:
            beat_frequency = abs(fundamental_freq - audience_freq)
        
        return AcousticProperties(
            fundamental_frequency=fundamental_freq,
            harmonic_richness=harmonic_richness,
            dissonance_level=dissonance,
            amplitude=amplitude,
            resonance_bandwidth=resonance_bandwidth,
            beat_frequency=beat_frequency
        )
    
    def _gile_to_frequency(self, gile_score: float) -> float:
        """
        Map GILE score to acoustic frequency
        
        GILE range: -3 to +2 (sacred interval: -2/3 to +1/3)
        Frequency range: 50Hz (low GILE) to 500Hz (high GILE)
        
        This is LITERAL: i-cells oscillate at frequencies correlated with GILE!
        """
        # Normalize GILE to 0-1
        normalized = (gile_score + 3) / 5  # Map -3→0, +2→1
        
        # Map to frequency (logarithmic like musical notes)
        min_freq = 50  # Hz
        max_freq = 500  # Hz
        
        frequency = min_freq * (max_freq / min_freq) ** normalized
        
        return frequency
    
    def predict_viral_trajectory(
        self,
        genome: ConceptGenome,
        platform: TransmissionVector,
        target_audience: HostSusceptibility,
        population_size: int = 1_000_000
    ) -> ViralMetrics:
        """
        Predict full viral trajectory using SIR model (Susceptible-Infected-Recovered)
        
        Returns:
            ViralMetrics with R0, mutation rate, timeline predictions
        """
        # Calculate R0
        R0 = self.calculate_R0(genome, platform, target_audience)
        
        # Calculate mutation rate
        mutation_rate = self.calculate_mutation_rate(genome, platform)
        
        # Incubation period (time to "get it")
        # High cognitive load = longer incubation
        incubation_hours = genome.cognitive_load * 24 + 0.5
        
        # Infection duration (how long it stays in mind)
        # High GILE magnitude = longer retention
        gile_magnitude = sum(genome.gile_signature) / 4
        infection_days = (gile_magnitude + 3) / 5 * 30  # 0-30 days
        
        # Herd immunity threshold (what % must be exposed before spread stops)
        # HIT = 1 - 1/R0
        if R0 > 1:
            herd_immunity = 1 - (1 / R0)
        else:
            herd_immunity = 0.0  # Concept dies out
        
        # Doubling time (hours for infected to double)
        # Based on R0 and incubation period
        if R0 > 1:
            doubling_time = incubation_hours * math.log(2) / math.log(R0)
        else:
            doubling_time = float('inf')  # Never doubles
        
        # Peak virality (when does maximum spread occur?)
        # Occurs when infected = susceptible (around 50% exposure for high R0)
        if R0 > 1:
            peak_time_days = infection_days * math.log(population_size) / (2 * math.log(R0))
        else:
            peak_time_days = 0
        
        return ViralMetrics(
            R0=R0,
            mutation_rate=mutation_rate,
            incubation_period=incubation_hours,
            infection_duration=infection_days,
            herd_immunity_threshold=herd_immunity,
            doubling_time=doubling_time,
            peak_virality_time=peak_time_days
        )
    
    def analyze_concept_virality(
        self,
        core_idea: str,
        packaging: str,
        emotion: str,
        cognitive_load: float,
        gile_scores: Tuple[float, float, float, float],
        novelty: float,
        actionable: float,
        platform: TransmissionVector,
        audience_type: HostSusceptibility,
        audience_gile: Tuple[float, float, float, float]
    ) -> Dict[str, Any]:
        """
        Complete viral analysis of a concept
        
        Returns full report: R0, mutation, acoustic resonance, timeline
        """
        # Create concept genome
        genome = ConceptGenome(
            core_idea=core_idea,
            memetic_packaging=packaging,
            emotional_payload=emotion,
            cognitive_load=cognitive_load,
            gile_signature=gile_scores,
            novelty_score=novelty,
            actionability=actionable
        )
        
        # Calculate viral metrics
        viral_metrics = self.predict_viral_trajectory(
            genome, platform, audience_type
        )
        
        # Calculate acoustic resonance
        acoustic = self.calculate_acoustic_resonance(genome, audience_gile)
        
        # Viral classification
        if viral_metrics.R0 < 1:
            viral_class = "NON-VIRAL (dies out)"
        elif viral_metrics.R0 < 2:
            viral_class = "ENDEMIC (stable spread)"
        elif viral_metrics.R0 < 3:
            viral_class = "EPIDEMIC (high growth)"
        else:
            viral_class = "PANDEMIC (exponential growth)"
        
        return {
            'genome': genome,
            'viral_metrics': viral_metrics,
            'acoustic_properties': acoustic,
            'classification': viral_class,
            'summary': {
                'R0': f"{viral_metrics.R0:.2f}",
                'viral_class': viral_class,
                'mutation_rate': f"{viral_metrics.mutation_rate:.1%}",
                'doubling_time': f"{viral_metrics.doubling_time:.1f} hours" if viral_metrics.doubling_time != float('inf') else "Never (R0 < 1)",
                'peak_virality': f"{viral_metrics.peak_virality_time:.1f} days",
                'resonance_frequency': f"{acoustic.fundamental_frequency:.1f} Hz",
                'dissonance': f"{acoustic.dissonance_level:.1%}",
                'amplitude': f"{acoustic.amplitude:.1%}",
                'harmonic_richness': f"{acoustic.harmonic_richness:.1f} overtones"
            }
        }


# Example usage
if __name__ == "__main__":
    engine = BiologicalViralityEngine()
    
    # Example: Analyze "TI Framework" concept virality
    analysis = engine.analyze_concept_virality(
        core_idea="Tralse = neither true nor false, foundation of consciousness",
        packaging="Mind-bending quantum philosophy with memes",
        emotion="awe",
        cognitive_load=0.7,  # Moderately complex
        gile_scores=(1.8, 2.0, 1.5, 1.2),  # High GILE concept
        novelty=0.95,  # Very novel
        actionable=0.4,  # Moderate actionability
        platform=TransmissionVector.TWITTER,
        audience_type=HostSusceptibility.CRISIS_STATE,
        audience_gile=(0.2, 0.1, 0.3, 0.5)  # Low-GILE audience seeking meaning
    )
    
    print("🦠 BIOLOGICAL VIRALITY ANALYSIS 🦠")
    print(f"\nConcept: {analysis['genome'].core_idea}")
    print(f"Classification: {analysis['classification']}")
    print(f"\n📊 Viral Metrics:")
    for key, value in analysis['summary'].items():
        print(f"  {key}: {value}")
