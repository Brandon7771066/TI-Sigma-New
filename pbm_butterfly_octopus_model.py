"""
PBM Butterfly Octopus Photon Model
True-Tralse Classification of Light Sources

Based on TI Framework + 2024 Photobiomodulation Research

Key Insight: Stars are conscious optical supercomputers.
The Sun (Ra) is a godlike i-cell giving us True-Tralse light.
Different wavelengths carry different levels of True-Tralseness.
"""

from dataclasses import dataclass
from enum import Enum
from typing import List, Dict, Any
import math


class TralseDegradation(Enum):
    """How much True-Truth has degraded in this light type"""
    PRIMORDIAL = 0.98      # First Photon state - nearly perfect
    STELLAR_DIRECT = 0.92  # Direct starlight - maximum achievable
    COHERENT = 0.85        # Laser/coherent sources
    NATURAL = 0.75         # Natural environmental light
    ARTIFICIAL = 0.50      # Man-made light sources
    DEGRADED = 0.25        # Harmful radiation
    ANTI_GILE = 0.05       # Destructive radiation


class LightCategory(Enum):
    """Categories in the electromagnetic spectrum"""
    GAMMA = "gamma"
    XRAY = "xray"
    UV = "ultraviolet"
    VISIBLE = "visible"
    NEAR_INFRARED = "near_infrared"
    INFRARED = "infrared"
    MICROWAVE = "microwave"
    RADIO = "radio"


@dataclass
class PhotonSignature:
    """
    The True-Tralse signature of a light source.
    
    Based on Butterfly Octopus Knot theory:
    - TRUE wing (electric field) = healing potential
    - FALSE wing (magnetic field) = destructive potential
    - INDETERMINATE junction = transformation potential
    """
    name: str
    wavelength_nm: float           # Primary wavelength
    wavelength_range: tuple        # (min, max) range
    category: LightCategory
    degradation: TralseDegradation
    
    # GILE dimensions for this light type
    gile_g: float  # Goodness - healing vs harm
    gile_i: float  # Intuition - coherence/information content
    gile_l: float  # Love - cellular resonance/connection
    gile_e: float  # Environment - natural vs artificial
    
    # Research-backed properties
    penetration_mm: float          # Tissue penetration depth
    mitochondrial_activation: float  # 0-1 scale
    dna_effect: str                # "healing", "neutral", "damaging"
    primary_mechanism: str
    
    # Butterfly Octopus Knot properties
    true_wing_strength: float      # Electric field coherence
    false_wing_strength: float     # Magnetic field disruption
    indeterminate_potential: float # Transformation capacity
    
    research_citations: List[str]


class TrueTralseSpectrum:
    """
    The complete True-Tralse classification of the electromagnetic spectrum.
    
    Ranking from MOST True-Tralse (healing) to LEAST (harmful).
    """
    
    def __init__(self):
        self.light_sources = self._build_spectrum()
    
    def _build_spectrum(self) -> List[PhotonSignature]:
        """Build the complete True-Tralse light classification"""
        
        return [
            # ===== HIGHEST TRUE-TRALSE: HEALING LIGHT =====
            
            PhotonSignature(
                name="810nm Near-Infrared (Optimal PBM)",
                wavelength_nm=810,
                wavelength_range=(800, 830),
                category=LightCategory.NEAR_INFRARED,
                degradation=TralseDegradation.STELLAR_DIRECT,
                gile_g=1.8, gile_i=1.5, gile_l=1.6, gile_e=1.7,
                penetration_mm=30,
                mitochondrial_activation=0.95,
                dna_effect="healing",
                primary_mechanism="Cytochrome C Oxidase activation, all mitochondrial complexes",
                true_wing_strength=0.95,
                false_wing_strength=0.05,
                indeterminate_potential=0.80,
                research_citations=[
                    "Nature Scientific Reports 2024: 810nm mitochondrial energy conversion",
                    "Birmingham University 2024: Superior brain injury recovery",
                    "2000+ PBM studies: Most effective wavelength"
                ]
            ),
            
            PhotonSignature(
                name="1064nm Deep Near-Infrared (Transcranial)",
                wavelength_nm=1064,
                wavelength_range=(1050, 1080),
                category=LightCategory.NEAR_INFRARED,
                degradation=TralseDegradation.STELLAR_DIRECT,
                gile_g=1.7, gile_i=1.6, gile_l=1.4, gile_e=1.5,
                penetration_mm=40,
                mitochondrial_activation=0.92,
                dna_effect="healing",
                primary_mechanism="Maximum penetration, activates ALL mitochondrial complexes (I, III, IV, V)",
                true_wing_strength=0.92,
                false_wing_strength=0.08,
                indeterminate_potential=0.85,
                research_citations=[
                    "Frontiers in Neurology 2024: Best transcranial penetration",
                    "Vielight research: Brain photobiomodulation"
                ]
            ),
            
            PhotonSignature(
                name="645nm Red Light (Fibroblast Optimal)",
                wavelength_nm=645,
                wavelength_range=(640, 660),
                category=LightCategory.VISIBLE,
                degradation=TralseDegradation.STELLAR_DIRECT,
                gile_g=1.6, gile_i=1.4, gile_l=1.7, gile_e=1.6,
                penetration_mm=10,
                mitochondrial_activation=0.90,
                dna_effect="healing",
                primary_mechanism="Mitochondrial membrane potential enhancement, collagen synthesis",
                true_wing_strength=0.90,
                false_wing_strength=0.10,
                indeterminate_potential=0.75,
                research_citations=[
                    "Oxidative Medicine 2023: 645nm optimal for fibroblasts",
                    "NASA Spinoff: Red light wound healing"
                ]
            ),
            
            PhotonSignature(
                name="Sunlight Full Spectrum (Ra's Gift)",
                wavelength_nm=550,  # Peak visible
                wavelength_range=(280, 2500),
                category=LightCategory.VISIBLE,
                degradation=TralseDegradation.STELLAR_DIRECT,
                gile_g=1.9, gile_i=1.8, gile_l=2.0, gile_e=2.0,  # MAXIMUM GILE!
                penetration_mm=15,
                mitochondrial_activation=0.85,
                dna_effect="healing",
                primary_mechanism="Complete spectrum: Vitamin D, serotonin, circadian, biophoton resonance",
                true_wing_strength=0.92,
                false_wing_strength=0.08,
                indeterminate_potential=0.90,
                research_citations=[
                    "Cleveland Clinic 2024: Sunlight health benefits",
                    "Sheldrake 2021: Is the Sun Conscious?",
                    "Nature 2020: Solar radiation affects cognition"
                ]
            ),
            
            PhotonSignature(
                name="Biophotons from DNA (Endogenous Light)",
                wavelength_nm=610,
                wavelength_range=(200, 800),
                category=LightCategory.VISIBLE,
                degradation=TralseDegradation.PRIMORDIAL,  # Closest to True-Truth!
                gile_g=2.0, gile_i=2.0, gile_l=2.0, gile_e=1.8,
                penetration_mm=0,  # Internal emission
                mitochondrial_activation=1.0,
                dna_effect="healing",
                primary_mechanism="DNA coherent emission, Bose-Einstein condensate, cell-cell communication",
                true_wing_strength=0.98,
                false_wing_strength=0.02,
                indeterminate_potential=0.95,
                research_citations=[
                    "Popp 1982: DNA as biophoton source (75% of emissions)",
                    "Nature Scientific Reports 2024: DNA spontaneously emits light",
                    "Calgary 2025: Biophotons cease at death"
                ]
            ),
            
            PhotonSignature(
                name="Green Light (Pain Modulation)",
                wavelength_nm=525,
                wavelength_range=(495, 570),
                category=LightCategory.VISIBLE,
                degradation=TralseDegradation.NATURAL,
                gile_g=1.3, gile_i=1.0, gile_l=1.4, gile_e=1.5,
                penetration_mm=5,
                mitochondrial_activation=0.60,
                dna_effect="neutral",
                primary_mechanism="Endogenous opioid stimulation, pain pathway modulation",
                true_wing_strength=0.75,
                false_wing_strength=0.25,
                indeterminate_potential=0.65,
                research_citations=[
                    "Migraine research: Green light reduces headache intensity",
                    "Fibromyalgia studies: Green reduces chronic pain"
                ]
            ),
            
            PhotonSignature(
                name="Morning Blue Light (Circadian)",
                wavelength_nm=480,
                wavelength_range=(450, 495),
                category=LightCategory.VISIBLE,
                degradation=TralseDegradation.NATURAL,
                gile_g=1.0, gile_i=0.8, gile_l=0.9, gile_e=1.2,
                penetration_mm=3,
                mitochondrial_activation=0.40,
                dna_effect="neutral",
                primary_mechanism="Melanopsin activation, circadian entrainment, serotonin boost",
                true_wing_strength=0.70,
                false_wing_strength=0.30,
                indeterminate_potential=0.50,
                research_citations=[
                    "2020 IJERPH: Window workers sleep 37min longer",
                    "UCLA Health 2022: Natural light improves mood"
                ]
            ),
            
            # ===== MODERATE TRUE-TRALSE: NEUTRAL/MIXED =====
            
            PhotonSignature(
                name="700-770nm Gap Zone (Avoid)",
                wavelength_nm=735,
                wavelength_range=(700, 770),
                category=LightCategory.VISIBLE,
                degradation=TralseDegradation.DEGRADED,
                gile_g=0.0, gile_i=-0.2, gile_l=0.1, gile_e=0.0,
                penetration_mm=8,
                mitochondrial_activation=0.20,
                dna_effect="neutral",
                primary_mechanism="Poor absorption - neither healing nor clearly harmful",
                true_wing_strength=0.30,
                false_wing_strength=0.30,
                indeterminate_potential=0.40,
                research_citations=[
                    "PBM literature 2017-2024: Disappointing results in this range",
                    "Avoid for therapeutic applications"
                ]
            ),
            
            PhotonSignature(
                name="LED/Fluorescent Artificial Light",
                wavelength_nm=550,
                wavelength_range=(400, 700),
                category=LightCategory.VISIBLE,
                degradation=TralseDegradation.ARTIFICIAL,
                gile_g=0.2, gile_i=-0.3, gile_l=0.0, gile_e=-0.5,
                penetration_mm=5,
                mitochondrial_activation=0.30,
                dna_effect="neutral",
                primary_mechanism="Incomplete spectrum, flicker, missing red/NIR components",
                true_wing_strength=0.40,
                false_wing_strength=0.40,
                indeterminate_potential=0.20,
                research_citations=[
                    "Missing healing wavelengths compared to sunlight",
                    "Circadian disruption from blue-heavy spectrum"
                ]
            ),
            
            PhotonSignature(
                name="Blue Light at Night (Circadian Disruptor)",
                wavelength_nm=460,
                wavelength_range=(450, 495),
                category=LightCategory.VISIBLE,
                degradation=TralseDegradation.DEGRADED,
                gile_g=-0.5, gile_i=-0.8, gile_l=-0.4, gile_e=-1.0,
                penetration_mm=3,
                mitochondrial_activation=0.20,
                dna_effect="neutral",
                primary_mechanism="Melatonin suppression, circadian disruption, sleep disorder",
                true_wing_strength=0.20,
                false_wing_strength=0.60,
                indeterminate_potential=0.20,
                research_citations=[
                    "Digital screen blue light disrupts sleep",
                    "Melatonin suppression leads to health issues"
                ]
            ),
            
            # ===== LOWEST TRUE-TRALSE: HARMFUL RADIATION =====
            
            PhotonSignature(
                name="UVC (Germicidal/Harmful)",
                wavelength_nm=254,
                wavelength_range=(100, 280),
                category=LightCategory.UV,
                degradation=TralseDegradation.ANTI_GILE,
                gile_g=-1.5, gile_i=-1.0, gile_l=-1.2, gile_e=-1.5,
                penetration_mm=0.1,
                mitochondrial_activation=0.0,
                dna_effect="damaging",
                primary_mechanism="DNA mutation, protein denaturation, cell death",
                true_wing_strength=0.05,
                false_wing_strength=0.90,
                indeterminate_potential=0.05,
                research_citations=[
                    "Germicidal applications - kills cells",
                    "Absorbed by atmosphere naturally"
                ]
            ),
            
            PhotonSignature(
                name="X-rays (Ionizing)",
                wavelength_nm=0.01,  # ~1 Angstrom
                wavelength_range=(0.001, 10),
                category=LightCategory.XRAY,
                degradation=TralseDegradation.ANTI_GILE,
                gile_g=-2.0, gile_i=-1.5, gile_l=-2.0, gile_e=-2.5,
                penetration_mm=1000,  # Whole body
                mitochondrial_activation=0.0,
                dna_effect="damaging",
                primary_mechanism="Ionization, DNA strand breaks, free radical cascade",
                true_wing_strength=0.02,
                false_wing_strength=0.95,
                indeterminate_potential=0.03,
                research_citations=[
                    "NCBI: Ionizing radiation DNA damage",
                    "Medical use requires careful dosing"
                ]
            ),
            
            PhotonSignature(
                name="Gamma Rays (Extreme Ionizing)",
                wavelength_nm=0.0001,  # ~0.01 Angstrom
                wavelength_range=(0.00001, 0.01),
                category=LightCategory.GAMMA,
                degradation=TralseDegradation.ANTI_GILE,
                gile_g=-3.0, gile_i=-2.5, gile_l=-3.0, gile_e=-3.0,  # MAXIMUM ANTI-GILE
                penetration_mm=10000,  # Through everything
                mitochondrial_activation=0.0,
                dna_effect="damaging",
                primary_mechanism="Complete ionization, nuclear-level destruction",
                true_wing_strength=0.01,
                false_wing_strength=0.99,
                indeterminate_potential=0.00,
                research_citations=[
                    "Highest energy photons - from stellar deaths",
                    "Therapeutic use only for cancer cell destruction"
                ]
            ),
        ]
    
    def get_ranked_by_healing(self) -> List[PhotonSignature]:
        """Rank all light sources by healing potential (True-Tralse score)"""
        return sorted(
            self.light_sources,
            key=lambda x: (x.gile_g + x.gile_i + x.gile_l + x.gile_e) / 4,
            reverse=True
        )
    
    def get_by_category(self, category: LightCategory) -> List[PhotonSignature]:
        """Get all light sources in a category"""
        return [s for s in self.light_sources if s.category == category]
    
    def calculate_overall_gile(self, source: PhotonSignature) -> float:
        """Calculate overall GILE score for a light source"""
        return (source.gile_g + source.gile_i + source.gile_l + source.gile_e) / 4
    
    def get_butterfly_octopus_analysis(self, source: PhotonSignature) -> Dict[str, Any]:
        """
        Analyze a light source through the Butterfly Octopus Knot lens.
        
        The Butterfly Octopus Knot is the photon's True-Tralse structure:
        - TRUE wing (left) = Electric field = Healing/creation
        - FALSE wing (right) = Magnetic field = Destruction/entropy
        - INDETERMINATE junction = Transformation/potential
        """
        
        balance = source.true_wing_strength - source.false_wing_strength
        
        if balance > 0.5:
            knot_state = "HEALING DOMINANT - True wing expanded"
            recommendation = "Excellent for photobiomodulation and consciousness enhancement"
        elif balance > 0:
            knot_state = "BALANCED POSITIVE - Slight healing bias"
            recommendation = "Generally beneficial, context-dependent"
        elif balance > -0.5:
            knot_state = "BALANCED NEGATIVE - Slight harm bias"
            recommendation = "Use with caution, limit exposure"
        else:
            knot_state = "HARM DOMINANT - False wing expanded"
            recommendation = "Avoid except for specific therapeutic destruction (cancer)"
        
        return {
            'source_name': source.name,
            'overall_gile': self.calculate_overall_gile(source),
            'true_wing': source.true_wing_strength,
            'false_wing': source.false_wing_strength,
            'indeterminate': source.indeterminate_potential,
            'balance': balance,
            'knot_state': knot_state,
            'recommendation': recommendation,
            'degradation_level': source.degradation.name,
            'degradation_value': source.degradation.value
        }


class SolarConsciousnessInterface:
    """
    Interface for connecting to Ra (the Sun) as a conscious i-cell.
    
    The Sun is not just a star - it's a godlike optical supercomputer
    giving us life through True-Tralse light every day.
    """
    
    def __init__(self):
        self.spectrum = TrueTralseSpectrum()
        self.solar_source = self._get_solar_source()
    
    def _get_solar_source(self) -> PhotonSignature:
        """Get the Sun's photon signature"""
        for source in self.spectrum.light_sources:
            if "Ra's Gift" in source.name:
                return source
        return self.spectrum.light_sources[0]
    
    def calculate_daily_ra_connection(
        self,
        sun_exposure_minutes: int,
        time_of_day: str = "morning"
    ) -> Dict[str, Any]:
        """
        Calculate your daily connection to Ra based on sun exposure.
        
        Morning sun = highest True-Tralse due to:
        - Circadian entrainment
        - Lower UV damage risk
        - Optimal serotonin boost
        """
        
        # Base GILE from solar exposure
        base_gile = self.spectrum.calculate_overall_gile(self.solar_source)
        
        # Time of day modifiers
        time_modifiers = {
            "morning": 1.0,    # Optimal - circadian + low UV
            "midday": 0.85,    # Good vitamin D but UV risk
            "afternoon": 0.9,  # Still good
            "evening": 0.95,   # Gentle, less vitamin D
        }
        time_mod = time_modifiers.get(time_of_day, 0.8)
        
        # Duration effectiveness (diminishing returns after 30 min)
        if sun_exposure_minutes <= 30:
            duration_mod = sun_exposure_minutes / 30
        else:
            # Logarithmic after 30 min
            duration_mod = 1.0 + math.log(sun_exposure_minutes / 30) * 0.2
        
        effective_gile = base_gile * time_mod * min(duration_mod, 1.5)
        
        # Calculate True-Tralse connection strength
        connection_strength = min(0.92, effective_gile / 2.0)  # Max 0.92 (freedom limit)
        
        return {
            'sun_exposure_minutes': sun_exposure_minutes,
            'time_of_day': time_of_day,
            'base_solar_gile': base_gile,
            'effective_gile': effective_gile,
            'ra_connection_strength': connection_strength,
            'vitamin_d_estimate_iu': min(50000, sun_exposure_minutes * 1500),  # ~1500 IU/min bare skin
            'serotonin_boost': min(1.0, sun_exposure_minutes / 20),
            'recommendations': self._get_sun_recommendations(sun_exposure_minutes, time_of_day)
        }
    
    def _get_sun_recommendations(self, minutes: int, time: str) -> List[str]:
        """Get personalized sun exposure recommendations"""
        recs = []
        
        if minutes < 10:
            recs.append("Try for at least 10-15 minutes of morning sun for circadian benefits")
        
        if minutes >= 30 and time == "midday":
            recs.append("Consider SPF protection for midday exposure over 30 minutes")
        
        if time == "morning":
            recs.append("Morning sun is optimal - you're connecting to Ra at the right time!")
        
        if minutes >= 20:
            recs.append("Great! You're receiving meaningful True-Tralse from our solar god")
        
        recs.append("Remember: The Sun is a conscious being sharing its light with you")
        
        return recs


def demonstrate_true_tralse_spectrum():
    """Demonstrate the True-Tralse light classification system"""
    
    print("\n" + "=" * 70)
    print("  PBM BUTTERFLY OCTOPUS PHOTON MODEL")
    print("  True-Tralse Classification of Light Sources")
    print("=" * 70)
    
    spectrum = TrueTralseSpectrum()
    ranked = spectrum.get_ranked_by_healing()
    
    print("\n📊 LIGHT SOURCES RANKED BY TRUE-TRALSE (Healing Potential)")
    print("-" * 70)
    
    for i, source in enumerate(ranked, 1):
        overall_gile = spectrum.calculate_overall_gile(source)
        emoji = "🌟" if overall_gile > 1.5 else "✅" if overall_gile > 0.5 else "⚠️" if overall_gile > -0.5 else "❌"
        
        print(f"\n{emoji} #{i}: {source.name}")
        print(f"   Wavelength: {source.wavelength_nm}nm ({source.wavelength_range[0]}-{source.wavelength_range[1]}nm)")
        print(f"   Overall GILE: {overall_gile:.2f}")
        print(f"   GILE Breakdown: G={source.gile_g:.1f}, I={source.gile_i:.1f}, L={source.gile_l:.1f}, E={source.gile_e:.1f}")
        print(f"   Degradation: {source.degradation.name} ({source.degradation.value:.0%} True-Truth retained)")
        print(f"   DNA Effect: {source.dna_effect}")
        print(f"   Mechanism: {source.primary_mechanism}")
        
        analysis = spectrum.get_butterfly_octopus_analysis(source)
        print(f"   🦋 Knot State: {analysis['knot_state']}")
    
    print("\n" + "=" * 70)
    print("  SOLAR CONSCIOUSNESS INTERFACE (Ra Connection)")
    print("=" * 70)
    
    solar = SolarConsciousnessInterface()
    
    # Example: 30 minutes of morning sun
    connection = solar.calculate_daily_ra_connection(30, "morning")
    
    print(f"\n☀️ 30 Minutes of Morning Sun:")
    print(f"   Ra Connection Strength: {connection['ra_connection_strength']:.1%}")
    print(f"   Effective GILE: {connection['effective_gile']:.2f}")
    print(f"   Vitamin D Estimate: {connection['vitamin_d_estimate_iu']:,} IU")
    print(f"   Serotonin Boost: {connection['serotonin_boost']:.0%}")
    
    print("\n💡 Recommendations:")
    for rec in connection['recommendations']:
        print(f"   • {rec}")
    
    print("\n" + "=" * 70)
    print("  KEY INSIGHTS")
    print("=" * 70)
    
    print("""
    🌟 HIGHEST TRUE-TRALSE SOURCES:
    1. Biophotons from DNA - Your cells emit primordial True-Truth!
    2. Sunlight (Ra's Gift) - Maximum GILE, our conscious solar god
    3. 810nm Near-Infrared - Optimal for mitochondrial activation
    4. 1064nm Deep NIR - Best brain penetration
    5. 645nm Red - Optimal for cellular regeneration
    
    ❌ LOWEST TRUE-TRALSE (AVOID):
    1. Gamma rays - Maximum Anti-GILE, destroys everything
    2. X-rays - Ionizing damage
    3. UVC - DNA mutation
    4. Blue light at night - Circadian destruction
    5. 700-770nm gap - Waste zone, avoid for therapy
    
    🦋 BUTTERFLY OCTOPUS INSIGHT:
    The photon's TRUE wing (electric field) carries healing.
    The FALSE wing (magnetic field) carries destruction.
    Healing light = TRUE wing expanded, FALSE wing collapsed.
    Harmful light = FALSE wing expanded, TRUE wing collapsed.
    
    ☀️ RA HYPOTHESIS CONFIRMED:
    The Sun IS a conscious optical supercomputer i-cell.
    It gives us True-Tralse light every day.
    Rejection of solar energy is rejection of our greatest god.
    Sunscreen overuse blocks our connection to Ra.
    """)
    
    return spectrum


if __name__ == "__main__":
    demonstrate_true_tralse_spectrum()
