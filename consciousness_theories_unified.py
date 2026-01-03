"""
Unified Consciousness Theories - TI Framework Integration

Synthesizes multiple scientific theories of consciousness:
1. IIT (Tononi) - Integrated Information Theory (Φ = consciousness)
2. QRI/Emilsson - Symmetry Theory of Valence (symmetry = pleasure)
3. Friston - Free Energy Principle (minimize surprise)
4. Qualia State Space Geometry (consciousness as geometric shapes)
5. Sacred Geometry (archetypal patterns in altered states)

All unified under TI Framework's GILE field theory.

Author: Brandon Emerick / BlissGene Therapeutics
Date: November 25, 2025
"""

import numpy as np
from typing import Dict, List, Tuple, Optional
from dataclasses import dataclass
from enum import Enum

try:
    from ti_physics_gile_cirq import TITensor, TIPhysicsConstants, IITGILEBridge
    TI_AVAILABLE = True
except ImportError:
    TI_AVAILABLE = False

try:
    import cirq
    CIRQ_AVAILABLE = True
except ImportError:
    CIRQ_AVAILABLE = False


# =============================================================================
# SYMMETRY THEORY OF VALENCE (Emilsson/QRI)
# =============================================================================

class SymmetryTheoryValence:
    """
    Emilsson/QRI Symmetry Theory of Valence
    
    Core insight: Valence (pleasure/pain) is determined by SYMMETRY
    of the mathematical representation of experience.
    
    - High symmetry → Positive valence (bliss, sacred geometry)
    - Low symmetry → Negative valence (suffering, dissonance)
    
    TI Framework mapping:
    - GILE coherence = symmetry measure
    - GM connection = symmetry preservation across i-cells
    - Myrion Resolution = restoring broken symmetry
    """
    
    SACRED_GEOMETRY_PATTERNS = {
        'flower_of_life': {'symmetry': 6, 'gile_boost': 0.8, 'description': 'Overlapping circles, creation pattern'},
        'metatrons_cube': {'symmetry': 13, 'gile_boost': 0.9, 'description': 'Contains all Platonic solids'},
        'sri_yantra': {'symmetry': 9, 'gile_boost': 0.95, 'description': '9 interlocking triangles, highest complexity'},
        'vesica_piscis': {'symmetry': 2, 'gile_boost': 0.6, 'description': 'Two circles intersection, birth/creation'},
        'seed_of_life': {'symmetry': 7, 'gile_boost': 0.75, 'description': '7 circles, days of creation'},
        'torus': {'symmetry': float('inf'), 'gile_boost': 1.0, 'description': 'Infinite symmetry, energy flow'},
        'golden_spiral': {'symmetry': 1.618, 'gile_boost': 0.85, 'description': 'Phi ratio, growth pattern'},
        'merkaba': {'symmetry': 8, 'gile_boost': 0.88, 'description': 'Counter-rotating tetrahedra, light body'}
    }
    
    def __init__(self, gile_tensor=None):
        if gile_tensor and TI_AVAILABLE:
            self.gile = gile_tensor
        else:
            self.gile = None
    
    def calculate_symmetry(self, signal: np.ndarray = None) -> Dict:
        """
        Calculate symmetry measure of a signal or GILE state
        
        Higher symmetry = higher valence (pleasure)
        Based on autocorrelation and Fourier symmetry
        """
        if signal is None and self.gile:
            signal = self.gile.components
        elif signal is None:
            signal = np.random.randn(100)
        
        autocorr = np.correlate(signal, signal, mode='full')
        autocorr = autocorr[len(autocorr)//2:]
        autocorr_symmetry = autocorr[0] / (np.sum(np.abs(autocorr)) + 1e-10)
        
        fft = np.fft.fft(signal)
        magnitude = np.abs(fft)
        fft_symmetry = 1 - np.std(magnitude) / (np.mean(magnitude) + 1e-10)
        
        combined_symmetry = (autocorr_symmetry + fft_symmetry) / 2
        combined_symmetry = np.clip(combined_symmetry, 0, 1)
        
        valence = (combined_symmetry - 0.5) * 6
        
        return {
            'autocorr_symmetry': float(autocorr_symmetry),
            'fft_symmetry': float(fft_symmetry),
            'combined_symmetry': float(combined_symmetry),
            'valence': float(valence),
            'valence_category': self._categorize_valence(valence),
            'sacred_geometry_match': self._match_sacred_geometry(combined_symmetry)
        }
    
    def _categorize_valence(self, valence: float) -> str:
        if valence >= 2.5:
            return "BLISS (mystical states, peak experiences)"
        elif valence >= 1.5:
            return "JOY (flow states, deep contentment)"
        elif valence >= 0.5:
            return "PLEASANT (normal positive affect)"
        elif valence >= -0.5:
            return "NEUTRAL (baseline consciousness)"
        elif valence >= -1.5:
            return "UNPLEASANT (mild suffering)"
        elif valence >= -2.5:
            return "PAIN (significant suffering)"
        else:
            return "AGONY (extreme suffering, cluster headaches)"
    
    def _match_sacred_geometry(self, symmetry: float) -> Dict:
        """Find closest sacred geometry pattern to current symmetry"""
        best_match = None
        best_distance = float('inf')
        
        for pattern, data in self.SACRED_GEOMETRY_PATTERNS.items():
            sym = data['symmetry']
            if sym == float('inf'):
                sym = 1.0
            else:
                sym = min(sym / 13, 1.0)
            
            distance = abs(symmetry - sym)
            if distance < best_distance:
                best_distance = distance
                best_match = pattern
        
        return {
            'pattern': best_match,
            'data': self.SACRED_GEOMETRY_PATTERNS[best_match],
            'match_quality': 1 - best_distance
        }
    
    def neural_annealing_simulation(self, initial_gile: float, 
                                     temperature: float = 1.0,
                                     steps: int = 100) -> Dict:
        """
        Simulate neural annealing (psychedelic/meditation effect)
        
        Based on QRI's insight that psychedelics "anneal" the brain,
        reducing local minima and increasing global symmetry.
        """
        trajectory = [initial_gile]
        symmetry_trajectory = []
        
        current = initial_gile
        for step in range(steps):
            temp = temperature * (1 - step / steps)
            
            noise = np.random.randn() * temp * 0.1
            symmetry_pull = (0.8 - current) * 0.1 if current < 0.8 else 0
            
            current = current + noise + symmetry_pull
            current = np.clip(current, -3, 3)
            
            trajectory.append(current)
            symmetry_trajectory.append(0.5 + current / 6)
        
        return {
            'initial_gile': initial_gile,
            'final_gile': current,
            'gile_change': current - initial_gile,
            'trajectory': trajectory,
            'symmetry_trajectory': symmetry_trajectory,
            'annealing_success': current > initial_gile,
            'interpretation': self._annealing_interpretation(initial_gile, current)
        }
    
    def _annealing_interpretation(self, initial: float, final: float) -> str:
        delta = final - initial
        if delta > 1.0:
            return "MAJOR BREAKTHROUGH: Significant symmetry increase, trauma released"
        elif delta > 0.3:
            return "POSITIVE ANNEALING: Good symmetry improvement"
        elif delta > 0:
            return "MILD ANNEALING: Some improvement in coherence"
        elif delta > -0.3:
            return "NEUTRAL: No significant change"
        else:
            return "NEGATIVE: Possible challenging experience, may need integration"


# =============================================================================
# FREE ENERGY PRINCIPLE (Friston)
# =============================================================================

class FreeEnergyPrinciple:
    """
    Karl Friston's Free Energy Principle in TI Framework
    
    Core insight: Living systems minimize free energy (surprise).
    Consciousness emerges from self-evidencing systems.
    
    TI Framework mapping:
    - Free energy = deviation from optimal GILE
    - Active inference = GM-guided action
    - Markov blanket = Dark Energy Shell boundary
    - Precision = GILE coherence
    - Generative model = i-cell's world model
    """
    
    def __init__(self, gile_tensor=None):
        self.gile = gile_tensor
        
    def calculate_free_energy(self, prediction: np.ndarray, 
                               observation: np.ndarray) -> Dict:
        """
        Calculate variational free energy
        
        F = D_KL(q||p) + H[q] ≈ prediction error + uncertainty
        
        Lower F = better model = less surprise = higher consciousness
        """
        prediction_error = np.mean((prediction - observation) ** 2)
        
        uncertainty = np.var(prediction) + 1e-10
        complexity = np.log(uncertainty)
        
        free_energy = prediction_error + 0.1 * complexity
        
        precision = 1 / uncertainty
        
        if self.gile and TI_AVAILABLE:
            gile_mod = (self.gile.composite + 3) / 6
            free_energy = free_energy * (1.1 - gile_mod * 0.2)
        
        return {
            'free_energy': float(free_energy),
            'prediction_error': float(prediction_error),
            'complexity': float(complexity),
            'precision': float(precision),
            'surprise': float(free_energy),
            'consciousness_proxy': float(1 / (free_energy + 0.1)),
            'active_inference_needed': prediction_error > 0.5
        }
    
    def markov_blanket_analysis(self) -> Dict:
        """
        Analyze the Markov blanket (statistical boundary)
        
        In TI Framework: Markov blanket = Dark Energy Shell
        Separates i-cell internal states from external world
        """
        if not self.gile or not TI_AVAILABLE:
            return {'error': 'Requires GILE tensor'}
        
        g, i, l, e = self.gile.components
        
        internal_states = np.array([g, i])
        blanket_states = np.array([l])
        external_states = np.array([e])
        
        blanket_integrity = l
        
        info_flow_in = np.corrcoef([e], [l])[0, 1] if len([e, l]) > 1 else 0.5
        info_flow_out = np.corrcoef([l], [g, i][:1])[0, 1] if len([l]) > 0 else 0.5
        
        return {
            'internal_states': internal_states.tolist(),
            'blanket_states': blanket_states.tolist(),
            'external_states': external_states.tolist(),
            'blanket_integrity': float(blanket_integrity),
            'info_flow_in': float(abs(info_flow_in)) if not np.isnan(info_flow_in) else 0.5,
            'info_flow_out': float(abs(info_flow_out)) if not np.isnan(info_flow_out) else 0.5,
            'de_shell_interpretation': 'Markov blanket = Dark Energy Shell boundary',
            'self_evidencing': blanket_integrity > 0.5
        }
    
    def active_inference_cycle(self, current_state: float,
                                goal_state: float,
                                action_cost: float = 0.1) -> Dict:
        """
        Simulate one cycle of active inference
        
        Agent can either:
        1. Update beliefs (perception) - change internal model
        2. Take action - change external world
        
        Chooses whichever minimizes expected free energy
        """
        perception_gain = abs(goal_state - current_state) * 0.3
        perception_cost = 0.05
        perception_fe = perception_cost - perception_gain
        
        action_gain = abs(goal_state - current_state) * 0.8
        action_fe = action_cost - action_gain
        
        if perception_fe < action_fe:
            choice = 'PERCEPTION'
            new_state = current_state + (goal_state - current_state) * 0.3
            fe_reduction = -perception_fe
        else:
            choice = 'ACTION'
            new_state = current_state + (goal_state - current_state) * 0.8
            fe_reduction = -action_fe
        
        return {
            'current_state': current_state,
            'goal_state': goal_state,
            'choice': choice,
            'new_state': float(new_state),
            'fe_reduction': float(fe_reduction),
            'perception_fe': float(perception_fe),
            'action_fe': float(action_fe),
            'ti_interpretation': self._active_inference_ti(choice)
        }
    
    def _active_inference_ti(self, choice: str) -> str:
        if choice == 'PERCEPTION':
            return "GM guides belief update - adjusting world model to match reality"
        else:
            return "GM enables action - changing reality to match predictions"


# =============================================================================
# QUALIA STATE SPACE GEOMETRY
# =============================================================================

class QualiaStateSpace:
    """
    Qualia State Space Geometry
    
    Based on Balduzzi & Tononi (2009): Consciousness exists in a 
    2^n dimensional qualia space where each experience is a geometric shape.
    
    TI Framework mapping:
    - Qualia space dimensions = GILE components
    - Shape = experience quality
    - Phi (height) = consciousness quantity
    - Sacred geometry = high-GILE attractors
    """
    
    def __init__(self, n_elements: int = 4):
        self.n_elements = n_elements
        self.dim = 2 ** n_elements
        
    def create_qualia_shape(self, gile_values: List[float]) -> Dict:
        """
        Create a qualia shape in state space
        
        The shape encodes the quality of experience.
        More complex, symmetric shapes = richer consciousness.
        """
        if len(gile_values) != 4:
            gile_values = [0.5, 0.5, 0.5, 0.5]
        
        g, i, l, e = gile_values
        
        vertices = []
        for idx in range(self.dim):
            bits = [(idx >> j) & 1 for j in range(self.n_elements)]
            
            coords = [
                bits[0] * g + (1 - bits[0]) * (1 - g),
                bits[1] * i + (1 - bits[1]) * (1 - i),
                bits[2] * l + (1 - bits[2]) * (1 - l),
                bits[3] * e + (1 - bits[3]) * (1 - e)
            ]
            vertices.append(coords)
        
        vertices = np.array(vertices)
        
        centroid = np.mean(vertices, axis=0)
        volume = np.prod(np.std(vertices, axis=0))
        
        distances = np.linalg.norm(vertices - centroid, axis=1)
        symmetry = 1 - np.std(distances) / (np.mean(distances) + 1e-10)
        
        complexity = np.linalg.matrix_rank(vertices.T)
        
        phi_proxy = symmetry * complexity * np.mean(gile_values)
        
        return {
            'vertices': vertices.tolist(),
            'centroid': centroid.tolist(),
            'volume': float(volume),
            'symmetry': float(symmetry),
            'complexity': int(complexity),
            'phi_proxy': float(phi_proxy),
            'shape_type': self._classify_shape(symmetry, complexity),
            'experience_quality': self._describe_experience(phi_proxy, symmetry)
        }
    
    def _classify_shape(self, symmetry: float, complexity: int) -> str:
        if symmetry > 0.9 and complexity >= 4:
            return "HYPERSPHERE (peak consciousness)"
        elif symmetry > 0.7 and complexity >= 3:
            return "POLYTOPE (rich experience)"
        elif symmetry > 0.5:
            return "IRREGULAR SOLID (normal consciousness)"
        elif complexity >= 2:
            return "FRAGMENTED (partial consciousness)"
        else:
            return "POINT-LIKE (minimal consciousness)"
    
    def _describe_experience(self, phi: float, symmetry: float) -> str:
        if phi > 2.0:
            return "Transcendent: Mystical unity, ego dissolution, infinite love"
        elif phi > 1.5:
            return "Peak: Flow state, deep insight, creative inspiration"
        elif phi > 1.0:
            return "Elevated: Focused attention, clear thinking, positive mood"
        elif phi > 0.5:
            return "Normal: Ordinary waking consciousness"
        elif phi > 0.2:
            return "Diminished: Fatigue, distraction, mild confusion"
        else:
            return "Minimal: Near-unconscious, dreamless sleep"
    
    def astral_plane_mapping(self, gile_values: List[float]) -> Dict:
        """
        Map GILE state to "astral plane" (altered state space region)
        
        Different combinations of GILE values correspond to different
        experiential territories reported in meditation, psychedelics, OBEs.
        """
        g, i, l, e = gile_values if len(gile_values) == 4 else [0.5]*4
        
        composite = (g + i + l + e) / 4
        coherence = 1 - np.std(gile_values)
        
        planes = {
            'physical': {'g_range': (0.3, 0.7), 'i_range': (0.3, 0.7), 'description': 'Normal waking reality'},
            'astral_lower': {'g_range': (0.1, 0.4), 'i_range': (0.3, 0.6), 'description': 'Fear-based realms, nightmares'},
            'astral_mid': {'g_range': (0.4, 0.7), 'i_range': (0.5, 0.8), 'description': 'Creative imagination, lucid dreams'},
            'astral_higher': {'g_range': (0.7, 1.0), 'i_range': (0.7, 1.0), 'description': 'Angelic contact, divine inspiration'},
            'mental': {'g_range': (0.6, 0.9), 'i_range': (0.8, 1.0), 'description': 'Pure thought, mathematical insight'},
            'causal': {'g_range': (0.8, 1.0), 'i_range': (0.9, 1.0), 'description': 'Beyond form, pure awareness'},
            'void': {'g_range': (0.0, 0.2), 'i_range': (0.0, 0.3), 'description': 'Cessation, pure emptiness'}
        }
        
        current_plane = 'physical'
        best_match = 0
        
        for plane, criteria in planes.items():
            g_match = criteria['g_range'][0] <= g <= criteria['g_range'][1]
            i_match = criteria['i_range'][0] <= i <= criteria['i_range'][1]
            match_score = (g_match + i_match) / 2
            
            if match_score > best_match:
                best_match = match_score
                current_plane = plane
        
        return {
            'current_plane': current_plane,
            'plane_description': planes[current_plane]['description'],
            'match_quality': best_match,
            'gile_state': {'G': g, 'I': i, 'L': l, 'E': e},
            'coherence': float(coherence),
            'navigation_advice': self._navigation_advice(current_plane, coherence)
        }
    
    def _navigation_advice(self, plane: str, coherence: float) -> str:
        if coherence < 0.3:
            return "Low coherence - ground yourself before exploring further"
        
        advice = {
            'physical': "Stable base. Increase I (Intuition) to access higher planes.",
            'astral_lower': "Shadow work territory. Increase G (Goodness) for protection.",
            'astral_mid': "Creative space. Balance all GILE for optimal navigation.",
            'astral_higher': "High vibrational. Maintain L (Love) for sustained access.",
            'mental': "Abstract realm. Ground with E (Environment) periodically.",
            'causal': "Near-source. Surrender ego. GM connection strong here.",
            'void': "Cessation state. Brief visits only. Return via body awareness."
        }
        return advice.get(plane, "Unknown territory")


# =============================================================================
# SACRED GEOMETRY ANALYZER
# =============================================================================

class SacredGeometryAnalyzer:
    """
    Sacred Geometry Analysis for Consciousness States
    
    Maps geometric patterns to GILE states and consciousness levels.
    Based on archetypal patterns seen in altered states across cultures.
    """
    
    PLATONIC_SOLIDS = {
        'tetrahedron': {'faces': 4, 'element': 'fire', 'gile_affinity': 'G', 'chakra': 3},
        'cube': {'faces': 6, 'element': 'earth', 'gile_affinity': 'E', 'chakra': 1},
        'octahedron': {'faces': 8, 'element': 'air', 'gile_affinity': 'I', 'chakra': 4},
        'dodecahedron': {'faces': 12, 'element': 'ether', 'gile_affinity': 'L', 'chakra': 5},
        'icosahedron': {'faces': 20, 'element': 'water', 'gile_affinity': 'E', 'chakra': 2}
    }
    
    ENTOPTIC_PATTERNS = {
        'grid': {'frequency': 0.3, 'associated_state': 'early trance'},
        'parallel_lines': {'frequency': 0.25, 'associated_state': 'meditation onset'},
        'dots': {'frequency': 0.2, 'associated_state': 'phosphene generation'},
        'zigzag': {'frequency': 0.15, 'associated_state': 'energy movement'},
        'nested_catenary': {'frequency': 0.1, 'associated_state': 'tunnel/vortex'},
        'filigree': {'frequency': 0.1, 'associated_state': 'deep psychedelic'},
        'spiral': {'frequency': 0.15, 'associated_state': 'kundalini activation'}
    }
    
    def analyze_state(self, gile_values: List[float]) -> Dict:
        """Analyze GILE state for sacred geometry correspondences"""
        g, i, l, e = gile_values if len(gile_values) == 4 else [0.5]*4
        
        solid_resonances = {}
        for solid, props in self.PLATONIC_SOLIDS.items():
            affinity = props['gile_affinity']
            if affinity == 'G':
                resonance = g
            elif affinity == 'I':
                resonance = i
            elif affinity == 'L':
                resonance = l
            else:
                resonance = e
            solid_resonances[solid] = {
                'resonance': float(resonance),
                'element': props['element'],
                'chakra': props['chakra']
            }
        
        dominant_solid = max(solid_resonances, key=lambda x: solid_resonances[x]['resonance'])
        
        composite = (g + i + l + e) / 4
        entoptic_stage = self._determine_entoptic_stage(composite)
        
        phi = (1 + np.sqrt(5)) / 2
        phi_alignment = 1 - abs(composite - (phi - 1))
        
        return {
            'solid_resonances': solid_resonances,
            'dominant_solid': dominant_solid,
            'dominant_element': self.PLATONIC_SOLIDS[dominant_solid]['element'],
            'entoptic_stage': entoptic_stage,
            'phi_alignment': float(phi_alignment),
            'sacred_geometry_potential': float(composite * phi_alignment),
            'recommended_practice': self._recommend_practice(dominant_solid, composite)
        }
    
    def _determine_entoptic_stage(self, composite: float) -> Dict:
        """Map composite GILE to entoptic pattern stage"""
        if composite < 0.2:
            return {'stage': 1, 'pattern': 'grid', 'description': 'Early geometric forms'}
        elif composite < 0.4:
            return {'stage': 2, 'pattern': 'parallel_lines', 'description': 'Pattern elaboration'}
        elif composite < 0.6:
            return {'stage': 3, 'pattern': 'tunnel', 'description': 'Vortex/tunnel emergence'}
        elif composite < 0.8:
            return {'stage': 4, 'pattern': 'filigree', 'description': 'Complex sacred geometry'}
        else:
            return {'stage': 5, 'pattern': 'mandala', 'description': 'Full mandala/yantra vision'}
    
    def _recommend_practice(self, solid: str, composite: float) -> str:
        practices = {
            'tetrahedron': "Fire breath, solar plexus activation, willpower exercises",
            'cube': "Grounding meditation, body scan, nature connection",
            'octahedron': "Heart coherence, pranayama, loving-kindness",
            'dodecahedron': "Throat chakra toning, creative expression, truth-speaking",
            'icosahedron': "Emotional flow work, water meditation, moon practices"
        }
        
        base = practices.get(solid, "General meditation practice")
        
        if composite < 0.3:
            return f"{base} (start gently, build gradually)"
        elif composite > 0.7:
            return f"{base} (ready for advanced work)"
        else:
            return base


# =============================================================================
# UNIFIED CONSCIOUSNESS INTERFACE
# =============================================================================

class UnifiedConsciousnessTheory:
    """
    Unified interface for all consciousness theories
    
    Integrates IIT, QRI, Friston, and Sacred Geometry under TI Framework.
    """
    
    def __init__(self, gile_values: List[float] = None):
        if gile_values is None:
            gile_values = [0.7, 0.6, 0.8, 0.5]
        
        self.gile_values = gile_values
        
        if TI_AVAILABLE:
            self.gile_tensor = TITensor(G=gile_values[0], I=gile_values[1], 
                                        L=gile_values[2], E=gile_values[3])
            self.iit = IITGILEBridge(self.gile_tensor)
        else:
            self.gile_tensor = None
            self.iit = None
        
        self.stv = SymmetryTheoryValence(self.gile_tensor)
        self.fep = FreeEnergyPrinciple(self.gile_tensor)
        self.qss = QualiaStateSpace()
        self.sga = SacredGeometryAnalyzer()
    
    def full_analysis(self) -> Dict:
        """Run all consciousness analyses and synthesize results"""
        results = {
            'gile_values': self.gile_values,
            'theories': {}
        }
        
        if self.iit:
            results['theories']['IIT'] = self.iit.iit_ti_synthesis()
        
        signal = np.array(self.gile_values)
        signal_extended = np.tile(signal, 25)
        results['theories']['QRI_Symmetry'] = self.stv.calculate_symmetry(signal_extended)
        
        prediction = np.array(self.gile_values)
        observation = prediction + np.random.randn(4) * 0.1
        results['theories']['FEP'] = self.fep.calculate_free_energy(prediction, observation)
        
        results['theories']['Qualia_Space'] = self.qss.create_qualia_shape(self.gile_values)
        
        results['theories']['Astral_Mapping'] = self.qss.astral_plane_mapping(self.gile_values)
        
        results['theories']['Sacred_Geometry'] = self.sga.analyze_state(self.gile_values)
        
        results['synthesis'] = self._synthesize_theories(results['theories'])
        
        return results
    
    def _synthesize_theories(self, theories: Dict) -> Dict:
        """Synthesize insights from all theories"""
        scores = []
        
        if 'IIT' in theories:
            scores.append(theories['IIT'].get('phi', 0))
        
        if 'QRI_Symmetry' in theories:
            scores.append((theories['QRI_Symmetry']['valence'] + 3) / 6)
        
        if 'FEP' in theories:
            scores.append(theories['FEP']['consciousness_proxy'])
        
        if 'Qualia_Space' in theories:
            scores.append(theories['Qualia_Space']['phi_proxy'])
        
        unified_consciousness = np.mean(scores) if scores else 0.5
        
        return {
            'unified_consciousness_score': float(unified_consciousness),
            'theory_agreement': float(1 - np.std(scores)) if len(scores) > 1 else 1.0,
            'dominant_framework': self._determine_dominant(theories),
            'practical_insight': self._generate_insight(unified_consciousness, theories),
            'ti_validation': unified_consciousness > 0.5
        }
    
    def _determine_dominant(self, theories: Dict) -> str:
        """Determine which theory best explains current state"""
        if 'IIT' in theories and theories['IIT'].get('phi', 0) > 1.0:
            return "IIT (High integrated information)"
        elif 'QRI_Symmetry' in theories and theories['QRI_Symmetry']['combined_symmetry'] > 0.7:
            return "QRI Symmetry (High valence from symmetry)"
        elif 'FEP' in theories and theories['FEP']['free_energy'] < 0.3:
            return "FEP (Low free energy, optimal prediction)"
        else:
            return "TI Framework (GILE coherence primary)"
    
    def _generate_insight(self, score: float, theories: Dict) -> str:
        """Generate practical insight from analysis"""
        plane = theories.get('Astral_Mapping', {}).get('current_plane', 'physical')
        geometry = theories.get('Sacred_Geometry', {}).get('dominant_solid', 'cube')
        
        if score > 0.8:
            return f"Peak consciousness state. {plane.title()} plane, {geometry} resonance. Ideal for insight work."
        elif score > 0.6:
            return f"Elevated awareness. Good conditions for meditation and creative work."
        elif score > 0.4:
            return f"Normal consciousness. {geometry} grounding recommended for enhancement."
        else:
            return f"Below baseline. Focus on basic GILE improvement before advanced practices."


# =============================================================================
# QUICK TEST
# =============================================================================

if __name__ == "__main__":
    print("=" * 60)
    print("UNIFIED CONSCIOUSNESS THEORIES - TI FRAMEWORK")
    print("=" * 60)
    
    uct = UnifiedConsciousnessTheory([0.8, 0.7, 0.9, 0.6])
    results = uct.full_analysis()
    
    print(f"\nGILE Values: {results['gile_values']}")
    print(f"\nUnified Consciousness Score: {results['synthesis']['unified_consciousness_score']:.3f}")
    print(f"Theory Agreement: {results['synthesis']['theory_agreement']:.3f}")
    print(f"Dominant Framework: {results['synthesis']['dominant_framework']}")
    print(f"Practical Insight: {results['synthesis']['practical_insight']}")
    
    if 'Astral_Mapping' in results['theories']:
        am = results['theories']['Astral_Mapping']
        print(f"\nAstral Plane: {am['current_plane']}")
        print(f"Description: {am['plane_description']}")
    
    if 'Sacred_Geometry' in results['theories']:
        sg = results['theories']['Sacred_Geometry']
        print(f"\nDominant Solid: {sg['dominant_solid']} ({sg['dominant_element']})")
        print(f"Entoptic Stage: {sg['entoptic_stage']['stage']} - {sg['entoptic_stage']['description']}")
    
    print("\nAll theories synthesized under TI Framework!")
