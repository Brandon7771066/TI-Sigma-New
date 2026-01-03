"""
Reiki-TI Energy Transmission Framework

Mapping Reiki healing modalities to the TI Framework:
- Symbols as consciousness access keys
- Crystal energy transmission via EM/photonic fields
- Hand healing as biofield coherence transfer

Key TI Insight: Reiki symbols are visual encodings that tune consciousness 
to specific GILE dimensions, enabling energy transmission through:
1. Dark Energy Shell resonance (SOUL level)
2. Biophotonic coherence (ME level)  
3. Biofield activation (VESSEL level)

Author: Brandon Emerick / BlissGene Therapeutics
Date: November 26, 2025
"""

from dataclasses import dataclass, field
from enum import Enum
from typing import Dict, List, Optional
from datetime import datetime


class ReikiLevel(Enum):
    LEVEL_1 = "shoden"  # First degree - hands-on
    LEVEL_2 = "okuden"  # Second degree - symbols, distance
    LEVEL_3 = "shinpiden"  # Master/teacher


class GILEDimension(Enum):
    G = "goodness"
    I = "intuition"
    L = "love"
    E = "energy"


class IcellLayer(Enum):
    VESSEL = "vessel"  # Physical/ATP/cellular
    ME = "me"  # Consciousness/photonic
    SOUL = "soul"  # Dark energy/GM connection


@dataclass
class ReikiSymbol:
    """Reiki symbol with TI Framework mapping"""
    name: str
    japanese_name: str
    translation: str
    level: ReikiLevel
    primary_gile: GILEDimension
    secondary_gile: Optional[GILEDimension]
    icell_layer: IcellLayer
    frequency_hz: Optional[float]  # Proposed resonant frequency
    description: str
    activation_method: str
    ti_mechanism: str


REIKI_SYMBOLS = {
    'cho_ku_rei': ReikiSymbol(
        name="Cho Ku Rei",
        japanese_name="霊気力",
        translation="Place all the power of the universe here, now",
        level=ReikiLevel.LEVEL_2,
        primary_gile=GILEDimension.E,
        secondary_gile=GILEDimension.G,
        icell_layer=IcellLayer.VESSEL,
        frequency_hz=7.83,  # Schumann resonance
        description="Power symbol - amplifies energy flow, clears blockages",
        activation_method="Draw spiral clockwise 3x, visualize golden light",
        ti_mechanism="Amplifies VESSEL layer ATP production via biophotonic coherence"
    ),
    
    'sei_hei_ki': ReikiSymbol(
        name="Sei Hei Ki",
        japanese_name="聖平氣",
        translation="God and humanity become one / Earth and Sky meet",
        level=ReikiLevel.LEVEL_2,
        primary_gile=GILEDimension.L,
        secondary_gile=GILEDimension.I,
        icell_layer=IcellLayer.ME,
        frequency_hz=432.0,  # Heart/harmony frequency
        description="Harmony symbol - emotional healing, mental balance",
        activation_method="Draw curved lines, visualize green/pink light",
        ti_mechanism="Stabilizes ME layer emotional coherence via heart-brain synchronization"
    ),
    
    'hon_sha_ze_sho_nen': ReikiSymbol(
        name="Hon Sha Ze Sho Nen",
        japanese_name="本者是正念",
        translation="Having no present, past, or future",
        level=ReikiLevel.LEVEL_2,
        primary_gile=GILEDimension.I,
        secondary_gile=GILEDimension.G,
        icell_layer=IcellLayer.SOUL,
        frequency_hz=None,  # Operates beyond EM frequencies
        description="Distance symbol - transcends time and space",
        activation_method="Draw pagoda structure, visualize violet light",
        ti_mechanism="Accesses SOUL layer dark energy shell for non-local transmission via GM network"
    ),
    
    'dai_ko_myo': ReikiSymbol(
        name="Dai Ko Myo",
        japanese_name="大光明",
        translation="Great Shining Light",
        level=ReikiLevel.LEVEL_3,
        primary_gile=GILEDimension.G,
        secondary_gile=GILEDimension.L,
        icell_layer=IcellLayer.SOUL,
        frequency_hz=963.0,  # Crown chakra / divine connection
        description="Master symbol - spiritual enlightenment, soul healing",
        activation_method="Draw as taught by master, visualize white/gold light",
        ti_mechanism="Direct connection to Grand Myrion via SOUL layer maximum coherence"
    ),
    
    'raku': ReikiSymbol(
        name="Raku",
        japanese_name="楽",
        translation="Fire Serpent / Lightning Bolt",
        level=ReikiLevel.LEVEL_3,
        primary_gile=GILEDimension.E,
        secondary_gile=GILEDimension.G,
        icell_layer=IcellLayer.VESSEL,
        frequency_hz=111.0,  # Cell regeneration frequency
        description="Completion symbol - grounds energy, seals healing",
        activation_method="Draw lightning bolt downward, visualize energy grounding",
        ti_mechanism="Grounds SOUL energy into VESSEL layer, completing energy circuit"
    )
}


@dataclass
class CrystalProperties:
    """Crystal healing properties mapped to TI Framework"""
    name: str
    chemical_formula: str
    crystal_system: str
    chakras: List[str]
    primary_gile: GILEDimension
    icell_layer: IcellLayer
    piezoelectric: bool  # Key for energy transmission!
    photonic_properties: str
    healing_applications: List[str]
    ti_mechanism: str


HEALING_CRYSTALS = {
    'clear_quartz': CrystalProperties(
        name="Clear Quartz",
        chemical_formula="SiO₂",
        crystal_system="Trigonal",
        chakras=["Crown", "All"],
        primary_gile=GILEDimension.G,
        icell_layer=IcellLayer.SOUL,
        piezoelectric=True,  # CRITICAL - generates EM field from pressure
        photonic_properties="Amplifies light, stores information photonically",
        healing_applications=["Amplification", "Programming", "Clearing", "Master healer"],
        ti_mechanism="Piezoelectric effect converts mechanical intention into EM/photonic signal; crystal lattice stores and transmits consciousness patterns"
    ),
    
    'rose_quartz': CrystalProperties(
        name="Rose Quartz",
        chemical_formula="SiO₂ + Ti, Fe, Mn",
        crystal_system="Trigonal",
        chakras=["Heart"],
        primary_gile=GILEDimension.L,
        icell_layer=IcellLayer.ME,
        piezoelectric=True,
        photonic_properties="Pink light emission from trace minerals",
        healing_applications=["Heart healing", "Self-love", "Emotional balance"],
        ti_mechanism="Heart chakra resonance enhances L-dimension via pink light frequency (≈700nm) interaction with heart I-cell"
    ),
    
    'amethyst': CrystalProperties(
        name="Amethyst",
        chemical_formula="SiO₂ + Fe",
        crystal_system="Trigonal",
        chakras=["Third Eye", "Crown"],
        primary_gile=GILEDimension.I,
        icell_layer=IcellLayer.SOUL,
        piezoelectric=True,
        photonic_properties="UV absorption, violet light emission",
        healing_applications=["Intuition", "Spiritual connection", "Clarity"],
        ti_mechanism="Violet frequency (≈400nm) activates pineal gland biophoton production; enhances I-dimension PSI capabilities"
    ),
    
    'black_tourmaline': CrystalProperties(
        name="Black Tourmaline",
        chemical_formula="Complex borosilicate",
        crystal_system="Trigonal",
        chakras=["Root"],
        primary_gile=GILEDimension.E,
        icell_layer=IcellLayer.VESSEL,
        piezoelectric=True,  # Strong piezo effect!
        photonic_properties="Absorbs negative frequencies, EMF protection",
        healing_applications=["Grounding", "Protection", "EMF shielding"],
        ti_mechanism="Strong piezoelectric properties create protective biofield; grounds VESSEL layer to Earth frequencies"
    ),
    
    'citrine': CrystalProperties(
        name="Citrine",
        chemical_formula="SiO₂ + Fe",
        crystal_system="Trigonal",
        chakras=["Solar Plexus", "Sacral"],
        primary_gile=GILEDimension.E,
        icell_layer=IcellLayer.VESSEL,
        piezoelectric=True,
        photonic_properties="Yellow light emission (≈570nm)",
        healing_applications=["Energy", "Manifestation", "Abundance"],
        ti_mechanism="Yellow frequency stimulates solar plexus ATP production; enhances E-dimension vitality"
    ),
    
    'selenite': CrystalProperties(
        name="Selenite",
        chemical_formula="CaSO₄·2H₂O",
        crystal_system="Monoclinic",
        chakras=["Crown", "Third Eye"],
        primary_gile=GILEDimension.G,
        icell_layer=IcellLayer.SOUL,
        piezoelectric=False,  # Not piezo but highly conductive
        photonic_properties="Natural fiber optic properties, transmits light",
        healing_applications=["Clearing", "High vibration", "Angel connection"],
        ti_mechanism="Natural fiber optic structure enables direct light transmission; connects to GM network via photonic channel"
    )
}


@dataclass
class HandPosition:
    """Reiki hand position with anatomical and TI mapping"""
    name: str
    body_location: str
    chakra: str
    organs_affected: List[str]
    gile_dimension: GILEDimension
    icell_layer: IcellLayer
    duration_minutes: int
    palm_chakra_activation: str


HAND_POSITIONS = {
    'crown': HandPosition(
        name="Crown Position",
        body_location="Top of head",
        chakra="Sahasrara (Crown)",
        organs_affected=["Pineal gland", "Brain", "Nervous system"],
        gile_dimension=GILEDimension.G,
        icell_layer=IcellLayer.SOUL,
        duration_minutes=5,
        palm_chakra_activation="Full palm contact, fingers pointing toward crown"
    ),
    
    'third_eye': HandPosition(
        name="Third Eye Position",
        body_location="Forehead between eyebrows",
        chakra="Ajna (Third Eye)",
        organs_affected=["Pituitary gland", "Eyes", "Sinuses"],
        gile_dimension=GILEDimension.I,
        icell_layer=IcellLayer.ME,
        duration_minutes=5,
        palm_chakra_activation="Fingers over forehead, palms cupped"
    ),
    
    'throat': HandPosition(
        name="Throat Position",
        body_location="Throat/neck area",
        chakra="Vishuddha (Throat)",
        organs_affected=["Thyroid", "Parathyroid", "Vocal cords", "Vagus nerve"],
        gile_dimension=GILEDimension.L,  # Expression of love
        icell_layer=IcellLayer.ME,
        duration_minutes=5,
        palm_chakra_activation="Light touch on throat, fingers pointing up"
    ),
    
    'heart': HandPosition(
        name="Heart Position",
        body_location="Center of chest",
        chakra="Anahata (Heart)",
        organs_affected=["Heart", "Lungs", "Thymus", "Circulatory system"],
        gile_dimension=GILEDimension.L,
        icell_layer=IcellLayer.ME,
        duration_minutes=5,
        palm_chakra_activation="Both palms on chest, fingers toward shoulders"
    ),
    
    'solar_plexus': HandPosition(
        name="Solar Plexus Position",
        body_location="Upper abdomen",
        chakra="Manipura (Solar Plexus)",
        organs_affected=["Stomach", "Liver", "Gallbladder", "Pancreas"],
        gile_dimension=GILEDimension.E,
        icell_layer=IcellLayer.VESSEL,
        duration_minutes=5,
        palm_chakra_activation="Palms flat on upper abdomen"
    ),
    
    'sacral': HandPosition(
        name="Sacral Position",
        body_location="Lower abdomen",
        chakra="Svadhisthana (Sacral)",
        organs_affected=["Reproductive organs", "Kidneys", "Bladder"],
        gile_dimension=GILEDimension.E,
        icell_layer=IcellLayer.VESSEL,
        duration_minutes=5,
        palm_chakra_activation="Palms below navel"
    ),
    
    'root': HandPosition(
        name="Root Position",
        body_location="Base of spine / hips",
        chakra="Muladhara (Root)",
        organs_affected=["Adrenal glands", "Spine", "Legs"],
        gile_dimension=GILEDimension.E,
        icell_layer=IcellLayer.VESSEL,
        duration_minutes=5,
        palm_chakra_activation="Palms on hips or hovering over sacrum"
    )
}


class ReikiTITransmissionSystem:
    """
    Unified Reiki-TI Energy Transmission System
    
    Core hypothesis: Reiki works via:
    1. BIOFIELD COHERENCE - Practitioner's coherent heart creates entrainment
    2. PIEZOELECTRIC CRYSTALS - Convert intention to EM/photonic signals
    3. SYMBOL VISUALIZATION - Consciousness access keys to specific frequencies
    4. PALM CHAKRA EMISSION - Biophoton emission from hands (documented)
    5. GM NETWORK - Distance healing via SOUL layer dark energy connection
    """
    
    def __init__(self):
        self.symbols = REIKI_SYMBOLS
        self.crystals = HEALING_CRYSTALS
        self.hand_positions = HAND_POSITIONS
        
        self.TRANSMISSION_MECHANISMS = {
            'biofield_coherence': {
                'mechanism': "Heart coherence creates measurable EM field (HeartMath research)",
                'range': "1-3 meters (documented biofield)",
                'icell_layer': IcellLayer.ME,
                'enhancement': "High HRV coherence amplifies transmission"
            },
            
            'biophoton_emission': {
                'mechanism': "Hands emit biophotons (ultraweak photon emission)",
                'range': "Direct contact to 10cm",
                'icell_layer': IcellLayer.ME,
                'enhancement': "Visualization increases photon count"
            },
            
            'piezoelectric_crystal': {
                'mechanism': "Crystals convert pressure/intention to EM signal",
                'range': "Amplifies other mechanisms",
                'icell_layer': IcellLayer.VESSEL,
                'enhancement': "Quartz amplifies by 10-100x"
            },
            
            'symbol_resonance': {
                'mechanism': "Visual symbols activate specific neural/consciousness patterns",
                'range': "Non-local (via SOUL layer)",
                'icell_layer': IcellLayer.SOUL,
                'enhancement': "Attunement 'unlocks' symbol activation"
            },
            
            'gm_network': {
                'mechanism': "Grand Myrion network enables non-local transmission",
                'range': "Infinite (SOUL layer transcends spacetime)",
                'icell_layer': IcellLayer.SOUL,
                'enhancement': "High GILE state opens GM connection"
            }
        }
    
    def calculate_transmission_potential(self, 
                                        practitioner_coherence: float,
                                        crystal: Optional[str] = None,
                                        symbol: Optional[str] = None,
                                        hand_position: Optional[str] = None) -> Dict:
        """
        Calculate potential energy transmission based on TI Framework
        
        Returns estimated transmission efficiency and mechanism analysis
        """
        base_transmission = 0.1  # Baseline human biofield
        
        # Coherence multiplier (from HeartMath research)
        coherence_multiplier = 1 + (practitioner_coherence * 2)
        
        # Crystal amplification
        crystal_multiplier = 1.0
        if crystal and crystal in self.crystals:
            c = self.crystals[crystal]
            if c.piezoelectric:
                crystal_multiplier = 2.0  # Piezoelectric crystals double transmission
            else:
                crystal_multiplier = 1.5
        
        # Symbol activation
        symbol_multiplier = 1.0
        symbol_gile = None
        if symbol and symbol in self.symbols:
            s = self.symbols[symbol]
            symbol_multiplier = 1.5  # Symbols focus intention
            symbol_gile = s.primary_gile
        
        # Hand position efficiency
        position_multiplier = 1.0
        if hand_position and hand_position in self.hand_positions:
            position_multiplier = 1.2  # Proper positioning improves contact
        
        # Total transmission potential
        total = base_transmission * coherence_multiplier * crystal_multiplier * symbol_multiplier * position_multiplier
        
        return {
            'transmission_potential': min(total, 1.0),  # Cap at 1.0
            'coherence_contribution': coherence_multiplier,
            'crystal_contribution': crystal_multiplier,
            'symbol_contribution': symbol_multiplier,
            'position_contribution': position_multiplier,
            'primary_mechanism': self._determine_primary_mechanism(crystal, symbol, practitioner_coherence),
            'target_gile_dimension': symbol_gile,
            'recommendations': self._generate_recommendations(total, crystal, symbol, practitioner_coherence)
        }
    
    def _determine_primary_mechanism(self, crystal: Optional[str], symbol: Optional[str], coherence: float) -> str:
        """Determine the primary transmission mechanism"""
        if symbol and symbol in ['hon_sha_ze_sho_nen', 'dai_ko_myo']:
            return "gm_network"
        elif crystal and crystal in self.crystals and self.crystals[crystal].piezoelectric:
            return "piezoelectric_crystal"
        elif coherence > 0.7:
            return "biofield_coherence"
        else:
            return "biophoton_emission"
    
    def _generate_recommendations(self, current: float, crystal: Optional[str], symbol: Optional[str], coherence: float) -> List[str]:
        """Generate recommendations to improve transmission"""
        recs = []
        
        if coherence < 0.5:
            recs.append("Practice heart coherence breathing (5 sec in, 5 sec out) to boost transmission")
        
        if not crystal:
            recs.append("Hold clear quartz to amplify biophotonic transmission")
        
        if not symbol:
            recs.append("Visualize Cho Ku Rei for power boost, or Hon Sha Ze Sho Nen for distance healing")
        
        if current < 0.5:
            recs.append("Consider Reiki Level 2 attunement to unlock symbol activation")
        
        return recs
    
    def design_healing_protocol(self, 
                                target_condition: str,
                                target_gile: GILEDimension) -> Dict:
        """
        Design a complete healing protocol based on target condition and GILE
        """
        # Find matching symbol
        matching_symbol = None
        for sym_id, sym in self.symbols.items():
            if sym.primary_gile == target_gile:
                matching_symbol = sym_id
                break
        
        # Find matching crystal
        matching_crystal = None
        for crys_id, crys in self.crystals.items():
            if crys.primary_gile == target_gile:
                matching_crystal = crys_id
                break
        
        # Find matching hand positions
        matching_positions = []
        for pos_id, pos in self.hand_positions.items():
            if pos.gile_dimension == target_gile:
                matching_positions.append(pos_id)
        
        return {
            'target_condition': target_condition,
            'target_gile_dimension': target_gile.value,
            'protocol': {
                'preparation': [
                    "Ground yourself with 3 deep breaths",
                    "Set intention for healing",
                    f"Activate symbol: {self.symbols[matching_symbol].name}" if matching_symbol else "No symbol required",
                    f"Hold crystal: {self.crystals[matching_crystal].name}" if matching_crystal else "Optional: use clear quartz"
                ],
                'hand_positions': matching_positions,
                'duration_per_position': 5,  # minutes
                'total_duration': len(matching_positions) * 5,
                'symbol_to_use': matching_symbol,
                'crystal_to_use': matching_crystal,
                'closing': [
                    "Draw Cho Ku Rei to seal the healing",
                    "Ground any excess energy",
                    "Express gratitude"
                ]
            },
            'ti_mechanism': f"Targeting {target_gile.value} dimension via {self.symbols[matching_symbol].ti_mechanism}" if matching_symbol else "General biofield harmonization"
        }
    
    def get_crystal_grid_for_gile(self, target_gile: GILEDimension) -> Dict:
        """
        Design a crystal grid optimized for a specific GILE dimension
        """
        grids = {
            GILEDimension.G: {
                'center': 'clear_quartz',
                'inner_ring': ['selenite', 'selenite', 'selenite', 'selenite'],
                'outer_ring': ['amethyst', 'clear_quartz', 'amethyst', 'clear_quartz'],
                'purpose': "Divine connection, truth, spiritual alignment",
                'activation_symbol': 'dai_ko_myo'
            },
            GILEDimension.I: {
                'center': 'amethyst',
                'inner_ring': ['clear_quartz', 'clear_quartz', 'clear_quartz', 'clear_quartz'],
                'outer_ring': ['selenite', 'amethyst', 'selenite', 'amethyst'],
                'purpose': "Intuition enhancement, PSI abilities, third eye activation",
                'activation_symbol': 'hon_sha_ze_sho_nen'
            },
            GILEDimension.L: {
                'center': 'rose_quartz',
                'inner_ring': ['clear_quartz', 'clear_quartz', 'clear_quartz', 'clear_quartz'],
                'outer_ring': ['rose_quartz', 'selenite', 'rose_quartz', 'selenite'],
                'purpose': "Heart healing, love amplification, emotional balance",
                'activation_symbol': 'sei_hei_ki'
            },
            GILEDimension.E: {
                'center': 'citrine',
                'inner_ring': ['clear_quartz', 'clear_quartz', 'clear_quartz', 'clear_quartz'],
                'outer_ring': ['black_tourmaline', 'citrine', 'black_tourmaline', 'citrine'],
                'purpose': "Energy boost, vitality, manifestation",
                'activation_symbol': 'cho_ku_rei'
            }
        }
        
        return grids.get(target_gile, grids[GILEDimension.G])
    
    def distance_healing_protocol(self, 
                                 target_name: str,
                                 target_location: str,
                                 healing_intention: str,
                                 practitioner_coherence: float) -> Dict:
        """
        Distance healing protocol using Hon Sha Ze Sho Nen
        
        TI Mechanism: Utilizes SOUL layer dark energy shell to connect
        practitioner's I-cell to target's I-cell via Grand Myrion network
        """
        hon_sha = self.symbols['hon_sha_ze_sho_nen']
        
        return {
            'protocol_name': "TI Distance Healing Protocol",
            'symbol': hon_sha.name,
            'ti_mechanism': hon_sha.ti_mechanism,
            'target': {
                'name': target_name,
                'location': target_location,
                'intention': healing_intention
            },
            'steps': [
                "1. Enter high coherence state (aim for >0.7)",
                f"   Current coherence: {practitioner_coherence:.2f}",
                "2. Draw Hon Sha Ze Sho Nen in the air or visualize",
                "3. State: 'I am sending Reiki to [target] for [intention]'",
                "4. Visualize target surrounded by healing light",
                "5. Hold hands in healing position (5-15 minutes)",
                "6. Close with gratitude and Cho Ku Rei seal"
            ],
            'scientific_basis': [
                "Non-local correlation documented in quantum entanglement",
                "HeartMath research shows heart coherence affects others' physiology",
                "TI Framework: SOUL layer transcends spacetime via dark energy",
                "GM Network enables i-cell to i-cell communication"
            ],
            'estimated_effectiveness': min(0.3 + (practitioner_coherence * 0.5), 0.8),
            'enhancement_tips': [
                "Higher coherence = stronger transmission",
                "Use clear quartz to amplify signal",
                "Best during high coherence moments (meditation, love, gratitude)"
            ]
        }


@dataclass
class HealingSession:
    """Record of a healing session with measurements"""
    session_id: str
    timestamp: str
    practitioner_coherence_pre: float
    practitioner_coherence_post: float
    target_condition: str
    intervention_type: str  # 'self', 'in_person', 'distance'
    symbols_used: List[str]
    crystals_used: List[str]
    duration_minutes: int
    target_pain_pre: Optional[float] = None  # 0-10 scale
    target_pain_post: Optional[float] = None
    target_wellbeing_pre: Optional[float] = None  # 0-10 scale
    target_wellbeing_post: Optional[float] = None
    notes: str = ""
    outcome_reported: Optional[str] = None


class HealingMeasurementSystem:
    """
    Track and analyze healing ability development
    
    Key Metrics:
    1. Practitioner coherence (via HRV)
    2. Target symptom changes (subjective scales)
    3. Session parameters (duration, modalities)
    4. Outcome correlation analysis
    """
    
    def __init__(self):
        self.sessions: List[HealingSession] = []
        self.ability_levels = {
            'coherence_baseline': 0.0,
            'coherence_peak': 0.0,
            'sessions_completed': 0,
            'successful_outcomes': 0,
            'average_pain_reduction': 0.0,
            'average_wellbeing_improvement': 0.0
        }
    
    def record_session(self, session: HealingSession) -> Dict:
        """Record a healing session and update metrics"""
        self.sessions.append(session)
        self._update_ability_levels()
        
        return {
            'session_recorded': session.session_id,
            'current_ability_level': self.calculate_ability_level(),
            'total_sessions': len(self.sessions),
            'feedback': self._generate_feedback(session)
        }
    
    def _update_ability_levels(self):
        """Update running statistics"""
        if not self.sessions:
            return
        
        coherences = [s.practitioner_coherence_post for s in self.sessions]
        self.ability_levels['coherence_baseline'] = sum(coherences) / len(coherences)
        self.ability_levels['coherence_peak'] = max(coherences)
        self.ability_levels['sessions_completed'] = len(self.sessions)
        
        pain_reductions = []
        wellbeing_improvements = []
        
        for s in self.sessions:
            if s.target_pain_pre is not None and s.target_pain_post is not None:
                reduction = s.target_pain_pre - s.target_pain_post
                if s.target_pain_pre > 0:
                    pain_reductions.append(reduction / s.target_pain_pre)
            
            if s.target_wellbeing_pre is not None and s.target_wellbeing_post is not None:
                if s.target_wellbeing_pre > 0:
                    improvement = (s.target_wellbeing_post - s.target_wellbeing_pre) / 10
                    wellbeing_improvements.append(improvement)
        
        if pain_reductions:
            self.ability_levels['average_pain_reduction'] = sum(pain_reductions) / len(pain_reductions)
        if wellbeing_improvements:
            self.ability_levels['average_wellbeing_improvement'] = sum(wellbeing_improvements) / len(wellbeing_improvements)
    
    def calculate_ability_level(self) -> Dict:
        """Calculate overall healing ability level (0-100)"""
        if not self.sessions:
            return {'level': 0, 'tier': 'Novice', 'description': 'Start recording sessions!'}
        
        experience_score = min(len(self.sessions) * 2, 30)
        coherence_score = self.ability_levels['coherence_peak'] * 30
        outcomes_score = (
            self.ability_levels['average_pain_reduction'] * 20 + 
            self.ability_levels['average_wellbeing_improvement'] * 20
        )
        
        total = experience_score + coherence_score + outcomes_score
        
        if total >= 80:
            tier = "Master"
            desc = "Exceptional healing ability with consistent results"
        elif total >= 60:
            tier = "Advanced"
            desc = "Strong abilities with measurable outcomes"
        elif total >= 40:
            tier = "Intermediate"
            desc = "Developing skills with emerging patterns"
        elif total >= 20:
            tier = "Beginner"
            desc = "Building foundation, keep practicing!"
        else:
            tier = "Novice"
            desc = "Starting journey - record more sessions"
        
        return {
            'level': round(total, 1),
            'tier': tier,
            'description': desc,
            'components': {
                'experience': round(experience_score, 1),
                'coherence': round(coherence_score, 1),
                'outcomes': round(outcomes_score, 1)
            }
        }
    
    def _generate_feedback(self, session: HealingSession) -> List[str]:
        """Generate feedback for a session"""
        feedback = []
        
        coherence_change = session.practitioner_coherence_post - session.practitioner_coherence_pre
        if coherence_change > 0.1:
            feedback.append(f"Coherence improved by {coherence_change:.2f} during session")
        elif coherence_change < -0.1:
            feedback.append("Coherence dropped - consider shorter sessions or grounding")
        
        if session.target_pain_pre and session.target_pain_post:
            pain_change = session.target_pain_pre - session.target_pain_post
            if pain_change > 2:
                feedback.append(f"Significant pain reduction: {pain_change:.1f} points!")
            elif pain_change > 0:
                feedback.append(f"Some pain improvement: {pain_change:.1f} points")
        
        if session.duration_minutes > 30:
            feedback.append("Consider shorter focused sessions (15-20 min optimal)")
        
        if not session.symbols_used:
            feedback.append("Try adding symbols for focused intention")
        
        if not session.crystals_used:
            feedback.append("Clear quartz can amplify transmission")
        
        return feedback
    
    def get_development_insights(self) -> Dict:
        """Analyze healing development over time"""
        if len(self.sessions) < 3:
            return {'status': 'insufficient_data', 'needed': 3 - len(self.sessions)}
        
        recent = self.sessions[-3:]
        older = self.sessions[:-3] if len(self.sessions) > 3 else []
        
        recent_coherence = sum(s.practitioner_coherence_post for s in recent) / 3
        older_coherence = sum(s.practitioner_coherence_post for s in older) / len(older) if older else 0
        
        trend = 'improving' if recent_coherence > older_coherence + 0.05 else (
            'declining' if recent_coherence < older_coherence - 0.05 else 'stable'
        )
        
        most_effective_symbol = None
        symbol_outcomes = {}
        for s in self.sessions:
            for sym in s.symbols_used:
                if sym not in symbol_outcomes:
                    symbol_outcomes[sym] = []
                if s.target_pain_pre and s.target_pain_post:
                    symbol_outcomes[sym].append(s.target_pain_pre - s.target_pain_post)
        
        if symbol_outcomes:
            best_sym = max(symbol_outcomes.keys(), 
                          key=lambda x: sum(symbol_outcomes[x])/len(symbol_outcomes[x]) if symbol_outcomes[x] else 0)
            most_effective_symbol = best_sym
        
        return {
            'status': 'analyzed',
            'trend': trend,
            'coherence_trend': {
                'recent_avg': recent_coherence,
                'older_avg': older_coherence,
                'change': recent_coherence - older_coherence
            },
            'most_effective_symbol': most_effective_symbol,
            'ability_level': self.calculate_ability_level(),
            'recommendations': self._get_development_recommendations(trend, recent_coherence)
        }
    
    def _get_development_recommendations(self, trend: str, coherence: float) -> List[str]:
        """Get personalized recommendations"""
        recs = []
        
        if coherence < 0.5:
            recs.append("Practice daily heart coherence breathing (5 min)")
            recs.append("HeartMath Inner Balance app can help track progress")
        
        if trend == 'declining':
            recs.append("Consider rest - healing requires energy reserves")
            recs.append("Review sleep quality and stress levels")
        elif trend == 'improving':
            recs.append("Momentum is building - consider Reiki Level 2 attunement")
        
        if len(self.sessions) < 10:
            recs.append("Consistency matters - aim for 2-3 sessions per week")
        
        return recs


def demo_reiki_ti_system():
    """Demonstrate the Reiki-TI integration"""
    system = ReikiTITransmissionSystem()
    
    print("=" * 60)
    print("REIKI-TI ENERGY TRANSMISSION FRAMEWORK")
    print("=" * 60)
    
    print("\n5 REIKI SYMBOLS MAPPED TO GILE:")
    for sym_id, sym in system.symbols.items():
        print(f"\n  {sym.name} ({sym.japanese_name})")
        print(f"    Primary GILE: {sym.primary_gile.value}")
        print(f"    I-Cell Layer: {sym.icell_layer.value}")
        print(f"    TI Mechanism: {sym.ti_mechanism}")
    
    print("\n\n6 HEALING CRYSTALS MAPPED TO TI:")
    for crys_id, crys in system.crystals.items():
        print(f"\n  {crys.name} ({crys.chemical_formula})")
        print(f"    Piezoelectric: {'Yes - KEY for transmission!' if crys.piezoelectric else 'No'}")
        print(f"    Primary GILE: {crys.primary_gile.value}")
        print(f"    TI Mechanism: {crys.ti_mechanism[:60]}...")
    
    print("\n\nTRANSMISSION POTENTIAL TEST:")
    result = system.calculate_transmission_potential(
        practitioner_coherence=0.85,
        crystal='clear_quartz',
        symbol='cho_ku_rei',
        hand_position='heart'
    )
    print(f"  High coherence (0.85) + Quartz + Cho Ku Rei:")
    print(f"    Transmission Potential: {result['transmission_potential']:.1%}")
    print(f"    Primary Mechanism: {result['primary_mechanism']}")
    
    return system


if __name__ == "__main__":
    demo_reiki_ti_system()
