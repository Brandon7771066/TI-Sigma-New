"""
Acoustic Resonance Engine
Models concept spread as SOUND WAVE PROPAGATION through resonance fields

REVOLUTIONARY INSIGHT:
Virality isn't "contagion" (touching spreads disease)
Virality is "RESONANCE" (matching frequencies couple energy!)

When a concept's frequency matches your i-cell's natural frequency → RESONANCE!
You don't "catch" an idea, you VIBRATE WITH IT!

PHYSICS MECHANISMS:
1. Harmonic Coupling - Concept frequency matches audience frequency
2. Beat Interference - Controversy = two frequencies interfering
3. Standing Waves - Cultural movements = reinforced patterns
4. Acoustic Impedance - Cognitive barriers to transmission
5. Resonance Amplification - Emotional intensity amplifies coupling
"""

from typing import Dict, List, Any, Tuple, Optional
from dataclasses import dataclass
import math


@dataclass
class WaveProperties:
    """Physical properties of a concept as sound wave"""
    frequency: float              # Hz (GILE frequency)
    amplitude: float              # Emotional intensity (0-1)
    wavelength: float            # Conceptual "size" (meters)
    phase: float                 # Where in cycle (radians)
    velocity: float              # Propagation speed (m/s)


@dataclass
class ResonanceAnalysis:
    """Analysis of resonance coupling between concept and audience"""
    coupling_strength: float      # How strongly they resonate (0-1)
    frequency_match: float        # How close frequencies are (0-1)
    phase_coherence: float        # How aligned phases are (0-1)
    energy_transfer: float        # How much energy flows (0-1)
    standing_wave_formed: bool    # Does a stable pattern emerge?
    beat_frequency: Optional[float]  # Hz (if interfering)


@dataclass
class MusicalAnalogy:
    """Musical interpretation of concept properties"""
    musical_note: str             # Closest note (C, D, E, etc.)
    octave: int                   # Which octave
    interval_from_A440: float     # Cents (1200 cents = octave)
    consonance_type: str          # Perfect, major, minor, dissonant
    chord_quality: str            # Major, minor, diminished, augmented


class AcousticResonanceEngine:
    """
    Models concept spread using acoustic physics and music theory
    """
    
    # Speed of sound in "idea space" (arbitrary but consistent)
    # Based on average human processing speed
    CONCEPT_VELOCITY = 340.0  # m/s (same as air for intuitive scaling)
    
    # Musical notes (frequency in Hz)
    MUSICAL_NOTES = {
        'C': 261.63,
        'C#': 277.18,
        'D': 293.66,
        'D#': 311.13,
        'E': 329.63,
        'F': 349.23,
        'F#': 369.99,
        'G': 392.00,
        'G#': 415.30,
        'A': 440.00,  # Concert pitch
        'A#': 466.16,
        'B': 493.88,
    }
    
    def __init__(self):
        pass
    
    def create_concept_wave(
        self,
        gile_score: float,
        emotional_intensity: float,
        cognitive_complexity: float,
        phase_offset: float = 0.0
    ) -> WaveProperties:
        """
        Create wave representation of concept
        
        Args:
            gile_score: Average GILE (-3 to +2)
            emotional_intensity: Amplitude (0-1)
            cognitive_complexity: Affects wavelength (0-1)
            phase_offset: Starting phase (0-2π)
        
        Returns:
            WaveProperties
        """
        # Frequency from GILE (50Hz - 500Hz)
        frequency = self._gile_to_frequency(gile_score)
        
        # Amplitude from emotional intensity
        amplitude = emotional_intensity
        
        # Wavelength = velocity / frequency
        wavelength = self.CONCEPT_VELOCITY / frequency
        
        # Velocity (constant in homogeneous medium)
        velocity = self.CONCEPT_VELOCITY
        
        # Phase
        phase = phase_offset
        
        return WaveProperties(
            frequency=frequency,
            amplitude=amplitude,
            wavelength=wavelength,
            phase=phase,
            velocity=velocity
        )
    
    def _gile_to_frequency(self, gile_score: float) -> float:
        """
        Map GILE score to acoustic frequency
        GILE -3 to +2 → 50Hz to 500Hz (logarithmic like musical notes)
        """
        normalized = (gile_score + 3) / 5  # Map -3→0, +2→1
        min_freq = 50
        max_freq = 500
        frequency = min_freq * (max_freq / min_freq) ** normalized
        return frequency
    
    def analyze_resonance_coupling(
        self,
        concept_wave: WaveProperties,
        audience_wave: WaveProperties
    ) -> ResonanceAnalysis:
        """
        Analyze resonance between concept and audience
        
        KEY PHYSICS:
        - Resonance occurs when frequencies match (or are harmonic multiples)
        - Phase alignment increases energy transfer
        - Amplitude mismatch reduces coupling
        
        Returns:
            ResonanceAnalysis
        """
        # Frequency match (perfect match = 1.0, far apart = 0.0)
        freq_ratio = min(concept_wave.frequency, audience_wave.frequency) / max(concept_wave.frequency, audience_wave.frequency)
        
        # Check for harmonic resonance (2:1, 3:2, 4:3 ratios)
        harmonic_bonus = self._check_harmonic_ratio(concept_wave.frequency, audience_wave.frequency)
        
        frequency_match = freq_ratio + harmonic_bonus * 0.2
        frequency_match = min(frequency_match, 1.0)
        
        # Phase coherence (aligned phases = stronger coupling)
        phase_diff = abs(concept_wave.phase - audience_wave.phase)
        phase_coherence = math.cos(phase_diff)  # -1 to +1, map to 0-1
        phase_coherence = (phase_coherence + 1) / 2
        
        # Amplitude compatibility (similar amplitudes couple better)
        amplitude_ratio = min(concept_wave.amplitude, audience_wave.amplitude) / max(concept_wave.amplitude, audience_wave.amplitude)
        
        # Overall coupling strength
        coupling_strength = (
            frequency_match * 0.50 +      # Frequency is PRIMARY
            phase_coherence * 0.30 +      # Phase alignment important
            amplitude_ratio * 0.20        # Amplitude compatibility
        )
        
        # Energy transfer (how much "vibration" transfers from concept to audience)
        # E ∝ A² for waves
        energy_transfer = coupling_strength * (concept_wave.amplitude ** 2)
        
        # Standing wave formation (stable cultural pattern)
        # Requires: strong coupling + phase alignment + frequency match
        standing_wave = (
            coupling_strength > 0.7 and
            phase_coherence > 0.8 and
            frequency_match > 0.9
        )
        
        # Beat frequency (if frequencies are close but not identical)
        beat_freq = None
        if 0.8 < frequency_match < 0.98:  # Close but not perfect
            beat_freq = abs(concept_wave.frequency - audience_wave.frequency)
        
        return ResonanceAnalysis(
            coupling_strength=coupling_strength,
            frequency_match=frequency_match,
            phase_coherence=phase_coherence,
            energy_transfer=energy_transfer,
            standing_wave_formed=standing_wave,
            beat_frequency=beat_freq
        )
    
    def _check_harmonic_ratio(self, freq1: float, freq2: float) -> float:
        """
        Check if two frequencies form harmonic ratios (octave, fifth, fourth)
        
        Returns bonus score (0-1) if harmonic relationship exists
        """
        ratio = max(freq1, freq2) / min(freq1, freq2)
        
        # Check common musical intervals
        harmonic_ratios = {
            2.0: 1.0,    # Octave (perfect consonance)
            1.5: 0.8,    # Perfect fifth
            1.333: 0.7,  # Perfect fourth
            1.25: 0.5,   # Major third
            1.2: 0.4,    # Minor third
        }
        
        for target_ratio, score in harmonic_ratios.items():
            if abs(ratio - target_ratio) < 0.05:  # 5% tolerance
                return score
        
        return 0.0
    
    def find_musical_analogy(self, frequency: float) -> MusicalAnalogy:
        """
        Find closest musical note to a given frequency
        Provides intuitive understanding of concept's "pitch"
        """
        # Find closest note
        closest_note = 'A'  # Default to A if somehow empty
        closest_freq = 440.0
        min_diff = float('inf')
        
        for note, freq in self.MUSICAL_NOTES.items():
            diff = abs(frequency - freq)
            if diff < min_diff:
                min_diff = diff
                closest_note = note
                closest_freq = freq
        
        # Calculate octave (A440 is in 4th octave)
        # Each octave doubles frequency
        octave = 4 + math.log2(frequency / 440.0)
        octave_int = round(octave)
        
        # Interval from A440 in cents (1200 cents = octave)
        cents = 1200 * math.log2(frequency / 440.0)
        
        # Consonance type (based on interval from tonic)
        consonance = self._classify_consonance(closest_note)
        
        # Chord quality (if thinking of concept as chord)
        chord = self._infer_chord_quality(frequency)
        
        return MusicalAnalogy(
            musical_note=closest_note,
            octave=octave_int,
            interval_from_A440=cents,
            consonance_type=consonance,
            chord_quality=chord
        )
    
    def _classify_consonance(self, note: str) -> str:
        """
        Classify consonance type of note relative to C (tonic)
        """
        # Intervals from C
        consonance_map = {
            'C': 'Perfect (Unison)',
            'C#': 'Dissonant (Minor 2nd)',
            'D': 'Dissonant (Major 2nd)',
            'D#': 'Dissonant (Minor 3rd)',
            'E': 'Consonant (Major 3rd)',
            'F': 'Perfect (Fourth)',
            'F#': 'Dissonant (Tritone)',
            'G': 'Perfect (Fifth)',
            'G#': 'Dissonant (Minor 6th)',
            'A': 'Consonant (Major 6th)',
            'A#': 'Dissonant (Minor 7th)',
            'B': 'Dissonant (Major 7th)',
        }
        
        return consonance_map.get(note, 'Unknown')
    
    def _infer_chord_quality(self, frequency: float) -> str:
        """
        Infer chord quality from frequency range
        Lower frequencies = darker (minor), higher = brighter (major)
        """
        if frequency < 150:
            return "Diminished (Dark, Tense)"
        elif frequency < 250:
            return "Minor (Sad, Reflective)"
        elif frequency < 350:
            return "Major (Happy, Bright)"
        else:
            return "Augmented (Intense, Unstable)"
    
    def calculate_interference_pattern(
        self,
        wave1: WaveProperties,
        wave2: WaveProperties
    ) -> Dict[str, Any]:
        """
        Calculate interference pattern when two concept waves meet
        
        CONSTRUCTIVE interference: Waves align → amplification
        DESTRUCTIVE interference: Waves cancel → nullification
        
        This models: controversy, debate, competing narratives
        """
        # Frequency difference
        freq_diff = abs(wave1.frequency - wave2.frequency)
        
        # Beat frequency (wobble when frequencies close)
        beat_freq = freq_diff if freq_diff < 50 else None
        
        # Phase relationship
        phase_diff = abs(wave1.phase - wave2.phase)
        
        # Interference type
        if phase_diff < math.pi / 4:
            interference_type = "CONSTRUCTIVE (Amplification)"
            resultant_amplitude = wave1.amplitude + wave2.amplitude
        elif phase_diff > 3 * math.pi / 4:
            interference_type = "DESTRUCTIVE (Cancellation)"
            resultant_amplitude = abs(wave1.amplitude - wave2.amplitude)
        else:
            interference_type = "PARTIAL (Mixed)"
            resultant_amplitude = math.sqrt(wave1.amplitude**2 + wave2.amplitude**2)
        
        # Cultural interpretation
        if beat_freq:
            cultural_effect = "CONTROVERSY (Beat pattern creates tension/interest)"
        elif interference_type == "CONSTRUCTIVE (Amplification)":
            cultural_effect = "VIRAL EXPLOSION (Aligned narratives amplify)"
        elif interference_type == "DESTRUCTIVE (Cancellation)":
            cultural_effect = "NARRATIVE COLLAPSE (Competing stories cancel out)"
        else:
            cultural_effect = "MIXED RECEPTION (Some resonate, some don't)"
        
        return {
            'interference_type': interference_type,
            'beat_frequency': beat_freq,
            'phase_difference_rad': phase_diff,
            'resultant_amplitude': resultant_amplitude,
            'cultural_interpretation': cultural_effect
        }
    
    def analyze_music_to_concept_mapping(
        self,
        music_frequency: float,
        music_amplitude: float,
        harmonic_complexity: float  # Number of overtones
    ) -> Dict[str, Any]:
        """
        Reverse engineer: What concept properties would produce this music?
        
        USE CASE: Analyze music to predict viral potential if turned into concept
        """
        # Map frequency to GILE
        # Invert the GILE→frequency mapping
        normalized_freq = math.log(music_frequency / 50) / math.log(500 / 50)
        gile_score = normalized_freq * 5 - 3  # Map 0-1 back to -3 to +2
        
        # Amplitude → emotional intensity
        emotional_intensity = music_amplitude
        
        # Harmonic complexity → cognitive richness
        # More overtones = more meanings/layers
        cognitive_richness = min(harmonic_complexity / 10, 1.0)
        
        # Musical note analogy
        musical_analogy = self.find_musical_analogy(music_frequency)
        
        # Predict concept type
        if gile_score > 1.0:
            concept_type = "NOBLE/SACRED (high-GILE wisdom)"
        elif gile_score > 0:
            concept_type = "POSITIVE (uplifting, inspiring)"
        elif gile_score > -1:
            concept_type = "NEUTRAL (informative, balanced)"
        else:
            concept_type = "DARK (fear-based, negative)"
        
        # Predict viral potential based on frequency
        # Mid-range frequencies (200-400Hz) most viral (easy to resonate)
        if 200 <= music_frequency <= 400:
            viral_potential = "HIGH (resonates with most humans)"
        elif 100 <= music_frequency <= 500:
            viral_potential = "MEDIUM (resonates with some demographics)"
        else:
            viral_potential = "LOW (niche frequency)"
        
        return {
            'estimated_gile': gile_score,
            'emotional_intensity': emotional_intensity,
            'cognitive_richness': cognitive_richness,
            'concept_type': concept_type,
            'viral_potential': viral_potential,
            'musical_analogy': musical_analogy,
            'interpretation': f"A concept with this frequency would be {concept_type.lower()}, with {viral_potential.lower()} viral potential. Musical note: {musical_analogy.musical_note} (Octave {musical_analogy.octave})"
        }


# Example usage
if __name__ == "__main__":
    engine = AcousticResonanceEngine()
    
    # Example 1: Create concept wave (TI Framework)
    ti_wave = engine.create_concept_wave(
        gile_score=1.5,           # High GILE
        emotional_intensity=0.9,   # Very intense
        cognitive_complexity=0.7,  # Moderately complex
        phase_offset=0.0
    )
    
    # Example 2: Create audience wave (Crisis state, low GILE)
    audience_wave = engine.create_concept_wave(
        gile_score=-0.5,           # Low GILE
        emotional_intensity=0.6,   # Moderate intensity
        cognitive_complexity=0.3,  # Simple
        phase_offset=math.pi / 4   # Slightly offset
    )
    
    # Analyze resonance
    resonance = engine.analyze_resonance_coupling(ti_wave, audience_wave)
    
    print("🎵 ACOUSTIC RESONANCE ANALYSIS 🎵")
    print(f"\nConcept Frequency: {ti_wave.frequency:.1f} Hz")
    print(f"Audience Frequency: {audience_wave.frequency:.1f} Hz")
    print(f"\nCoupling Strength: {resonance.coupling_strength:.1%}")
    print(f"Frequency Match: {resonance.frequency_match:.1%}")
    print(f"Phase Coherence: {resonance.phase_coherence:.1%}")
    print(f"Energy Transfer: {resonance.energy_transfer:.1%}")
    print(f"Standing Wave Formed: {resonance.standing_wave_formed}")
    if resonance.beat_frequency:
        print(f"Beat Frequency (Controversy): {resonance.beat_frequency:.1f} Hz")
    
    # Musical analogy
    musical = engine.find_musical_analogy(ti_wave.frequency)
    print(f"\nMusical Note: {musical.musical_note} (Octave {musical.octave})")
    print(f"Consonance: {musical.consonance_type}")
    print(f"Chord Quality: {musical.chord_quality}")
