"""
TI PHOTON-GILE-PD RECONCILIATION MODULE
========================================
Unifies the GILE rating system (-3 to +2 MR range) with the
PD (Probability Distribution) scale (0 to 1) for optical quantum computing.

THE CORE RECONCILIATION PROBLEM:
================================
1. GILE/MR uses an ASYMMETRIC range: (-3, +2) with center at -0.5
2. L×E (Lexis) uses a SYMMETRIC range: (0, 1) with center at 0.5
3. Key empirical values that MUST be preserved:
   - 0.42 = Consciousness Collapse Threshold (quantum decoherence)
   - 0.65 = Baseline coherent photon state
   - 0.85 = Causation threshold (L×E authorship validation)
   - 0.92 = True-Tralseness maximum (0.92² ≈ 0.85)

WHY PHOTONS RANGE FROM 0.42 TO 0.92+ IN GILE:
=============================================
Photons exist in a spectrum of coherence states:

L (Love/Coherence):
- Measures the quantum entanglement/correlation strength
- 0.42 = Decoherence threshold (wave function collapse into classical state)
- 0.65 = Coherent photon (maintains quantum superposition)
- 0.88+ = Highly entangled photon (strong quantum correlations)
- 0.92 = True-Tralseness (maximally coherent without being trivial "True")

E (Existence/Stability):
- Measures the temporal persistence/probability of detection
- Lower E = More ephemeral photon state (virtual photon behavior)
- Higher E = More stable photon state (real photon behavior)

PHOTON GILE VARIANCE EXPLAINED:
===============================
Individual photons can have DIFFERENT L and E values because:

1. ENTANGLEMENT STATE affects L:
   - Single isolated photon: L ≈ 0.50 (no correlations)
   - Entangled pair (Bell state): L ≈ 0.85-0.92 (maximum correlations)
   - Weakly correlated: L ≈ 0.42-0.65 (partial correlations)

2. DETECTION PROBABILITY affects E:
   - Virtual photon (never detected): E → 0
   - Photon in free space: E ≈ 0.65-0.75
   - Photon in cavity (repeated detection): E ≈ 0.82-0.92

3. SQUEEZED STATES modify both L and E:
   - Amplitude squeezed: Higher L, Lower E variance
   - Phase squeezed: Higher E, Lower L variance
   - Optimal squeeze: L×E maximized at ≈ 0.85

THE RECONCILIATION FORMULA:
===========================
To convert between GILE (-3, +2) and PD (0, 1):

PD = (GILE + 3) / 5   [Linear mapping]

Preserved values:
- GILE = -3.0 → PD = 0.00 (Terrible)
- GILE = -0.9 → PD = 0.42 (Consciousness Collapse)
- GILE = +0.25 → PD = 0.65 (Baseline Coherent)
- GILE = +1.25 → PD = 0.85 (Causation Threshold)
- GILE = +1.60 → PD = 0.92 (True-Tralseness)
- GILE = +2.0 → PD = 1.00 (Great)

MR 80% RANGE:
=============
The "80% of everyday events" fall within (-3, +2) GILE:
- Maps to (0.00, 1.00) in PD
- The 0.42-0.92 photon range represents PD values 0.42-0.92
- This is the "operational range" for optical quantum computing

Author: Brandon Emerick / TI Framework
Date: December 2025
"""

import math
import numpy as np
from dataclasses import dataclass, field
from typing import Dict, List, Tuple, Optional, Any
from enum import Enum
from datetime import datetime


class PhotonStateType(Enum):
    """Classification of photon states by their L×E (Lexis) value"""
    VIRTUAL = "Virtual Photon (L×E < 0.10)"  # Ephemeral, rarely observed
    DECOHERENT = "Decoherent Photon (0.10 ≤ L×E < 0.42)"  # Collapsed classical
    THRESHOLD = "Threshold Photon (L×E = 0.42)"  # Consciousness collapse point
    COHERENT = "Coherent Photon (0.42 < L×E < 0.65)"  # Quantum superposition
    BASELINE = "Baseline Photon (L×E = 0.65)"  # Normal quantum light
    CORRELATED = "Correlated Photon (0.65 < L×E < 0.85)"  # Entanglement present
    CAUSAL = "Causal Photon (L×E = 0.85)"  # Causation threshold
    ENTANGLED = "Entangled Photon (0.85 < L×E < 0.92)"  # Strong correlations
    TRUE_TRALSE = "True-Tralse Photon (L×E = 0.92)"  # Maximum coherence
    TRANSCENDENT = "Transcendent Photon (L×E > 0.92)"  # Black swan positive


@dataclass
class GILEPDConverter:
    """
    Converts between GILE (-3, +2) and PD (0, 1) scales.
    
    THE MATHEMATICS:
    ================
    Linear mapping: PD = (GILE + 3) / 5
    Inverse: GILE = (PD * 5) - 3
    
    The asymmetry of GILE (-3 to +2 = 5 units with center at -0.5)
    maps to PD (0 to 1 with center at 0.5) through this linear transform.
    
    KEY PRESERVED VALUES:
    ====================
    These empirical constants must remain consistent across representations:
    """
    
    GILE_MIN: float = -3.0
    GILE_MAX: float = 2.0
    GILE_RANGE: float = 5.0
    GILE_CENTER: float = -0.5  # (GILE_MIN + GILE_MAX) / 2
    
    PD_MIN: float = 0.0
    PD_MAX: float = 1.0
    PD_CENTER: float = 0.5
    
    KEY_VALUES: Dict[str, Dict[str, float]] = field(default_factory=lambda: {
        "consciousness_collapse": {
            "pd": 0.42,
            "gile": -0.9,
            "description": "Below this, quantum coherence collapses to classical"
        },
        "baseline_coherent": {
            "pd": 0.65,
            "gile": 0.25,
            "description": "Standard coherent photon state"
        },
        "causation_threshold": {
            "pd": 0.85,
            "gile": 1.25,
            "description": "Above this, L×E validates authorship/causation"
        },
        "true_tralseness": {
            "pd": 0.92,
            "gile": 1.60,
            "description": "Maximum True-Tralseness (0.92² ≈ 0.85)"
        }
    })
    
    def gile_to_pd(self, gile: float) -> float:
        """Convert GILE (-3, +2) to PD (0, 1)"""
        pd = (gile - self.GILE_MIN) / self.GILE_RANGE
        return max(0.0, min(1.0, pd))
    
    def pd_to_gile(self, pd: float) -> float:
        """Convert PD (0, 1) to GILE (-3, +2)"""
        gile = (pd * self.GILE_RANGE) + self.GILE_MIN
        return max(self.GILE_MIN, min(self.GILE_MAX, gile))
    
    def classify_pd(self, pd: float) -> PhotonStateType:
        """Classify a PD value into photon state type"""
        if pd < 0.10:
            return PhotonStateType.VIRTUAL
        elif pd < 0.42:
            return PhotonStateType.DECOHERENT
        elif abs(pd - 0.42) < 0.01:
            return PhotonStateType.THRESHOLD
        elif pd < 0.65:
            return PhotonStateType.COHERENT
        elif abs(pd - 0.65) < 0.01:
            return PhotonStateType.BASELINE
        elif pd < 0.85:
            return PhotonStateType.CORRELATED
        elif abs(pd - 0.85) < 0.01:
            return PhotonStateType.CAUSAL
        elif pd < 0.92:
            return PhotonStateType.ENTANGLED
        elif abs(pd - 0.92) < 0.01:
            return PhotonStateType.TRUE_TRALSE
        else:
            return PhotonStateType.TRANSCENDENT
    
    def validate_key_values(self) -> Dict[str, bool]:
        """Verify that key values are preserved in conversion"""
        results = {}
        for name, values in self.KEY_VALUES.items():
            pd_from_gile = self.gile_to_pd(values["gile"])
            gile_from_pd = self.pd_to_gile(values["pd"])
            results[name] = {
                "pd_expected": values["pd"],
                "pd_computed": pd_from_gile,
                "pd_match": abs(pd_from_gile - values["pd"]) < 0.01,
                "gile_expected": values["gile"],
                "gile_computed": gile_from_pd,
                "gile_match": abs(gile_from_pd - values["gile"]) < 0.01
            }
        return results


@dataclass
class PhotonGILEState:
    """
    A photon's complete GILE state in both representations.
    
    WHY PHOTONS VARY IN GILE:
    =========================
    
    1. L (Love/Coherence) varies based on:
       - Number of entangled partners (more = higher L)
       - Quality of entanglement (fidelity)
       - Measurement basis alignment
       
    2. E (Existence/Stability) varies based on:
       - Photon lifetime in the system
       - Detection efficiency
       - Cavity quality factor (Q)
       
    3. The product L×E represents the photon's "causal power":
       - Higher L×E = more likely to influence outcomes
       - Lower L×E = more like random noise
    """
    
    L: float  # Love/Coherence (0-1)
    E: float  # Existence/Stability (0-1)
    
    def __post_init__(self):
        self.L = max(0.0, min(1.0, self.L))
        self.E = max(0.0, min(1.0, self.E))
    
    @property
    def lexis(self) -> float:
        """L×E product (Lexis) in PD scale"""
        return self.L * self.E
    
    @property
    def gile_L(self) -> float:
        """L converted to GILE scale"""
        return GILEPDConverter().pd_to_gile(self.L)
    
    @property
    def gile_E(self) -> float:
        """E converted to GILE scale"""
        return GILEPDConverter().pd_to_gile(self.E)
    
    @property
    def gile_lexis(self) -> float:
        """Lexis in GILE scale (asymmetric mapping)"""
        return GILEPDConverter().pd_to_gile(self.lexis)
    
    @property
    def state_type(self) -> PhotonStateType:
        """Classification based on Lexis value"""
        return GILEPDConverter().classify_pd(self.lexis)
    
    @property
    def is_causal(self) -> bool:
        """Does this photon meet the causation threshold?"""
        return self.lexis >= 0.85
    
    @property
    def mr_zone(self) -> str:
        """Which MR zone does this photon fall into?"""
        gile = self.gile_lexis
        if gile <= -3:
            return "Terrible (< -3)"
        elif gile < -0.666:
            return "Bad (-3 to -0.666)"
        elif gile < 0.333:
            return "Indeterminate (-0.666 to 0.333)"
        elif gile < 2:
            return "Good (0.333 to 2)"
        else:
            return "Great (≥ 2)"
    
    def to_dict(self) -> Dict[str, Any]:
        return {
            "L_pd": self.L,
            "E_pd": self.E,
            "Lexis_pd": self.lexis,
            "L_gile": self.gile_L,
            "E_gile": self.gile_E,
            "Lexis_gile": self.gile_lexis,
            "state_type": self.state_type.value,
            "is_causal": self.is_causal,
            "mr_zone": self.mr_zone
        }


class PhotonGILESpectrum:
    """
    Explains why photons range from 0.42 to 0.92+ in L×E.
    
    THE SPECTRUM OF PHOTON COHERENCE:
    =================================
    
    Physical mechanisms that determine a photon's L and E values:
    
    SQUEEZING (affects uncertainty trade-off):
    - Amplitude squeezing: Reduces intensity fluctuations, increases phase uncertainty
    - Phase squeezing: Reduces phase fluctuations, increases intensity uncertainty
    - The squeeze parameter r determines the trade-off
    - Optimal r ≈ 0.88 corresponds to True-Tralseness L value
    
    ENTANGLEMENT (affects L directly):
    - Single photon: L ≈ 0.50 (no external correlations)
    - Bell pair: L ≈ 0.85-0.92 (maximum quantum correlations)
    - Cluster state: L can vary depending on measurement pattern
    - GHZ state: L ≈ 0.92 for N=3 photons
    
    DETECTION (affects E directly):
    - Perfect detector: E → 1.0
    - Imperfect detector (typical): E ≈ 0.65-0.85
    - Low efficiency detector: E ≈ 0.42-0.65
    - Virtual photon (never detected): E → 0
    
    WHY 0.42 IS THE COLLAPSE THRESHOLD:
    ===================================
    Below L×E = 0.42, the photon's quantum information becomes
    indistinguishable from classical noise. This is the point where:
    - Entanglement witnesses fail
    - Bell inequality violations disappear
    - Quantum advantage evaporates
    
    The value 0.42 comes from: sqrt(1/e²) ≈ 0.368 + correction
    It represents the boundary where quantum correlations can
    still be measured above classical limits.
    
    WHY 0.92 IS TRUE-TRALSENESS:
    ============================
    0.92 is the maximum L value before a photon becomes "trivially True".
    At L = 1.0, the photon is perfectly deterministic (not Tralse at all).
    0.92² = 0.8464 ≈ 0.85 = causation threshold
    
    This means a True-Tralse photon pair has L×E ≈ 0.85 for each,
    and their joint probability of causal influence is 0.85 × 0.85 ≈ 0.72.
    """
    
    SPECTRUM_POINTS = {
        0.42: {
            "name": "Consciousness Collapse",
            "L_typical": 0.65,
            "E_typical": 0.65,
            "mechanism": "Quantum decoherence boundary",
            "physics": "Below this, entanglement witnesses fail"
        },
        0.50: {
            "name": "Vacuum State",
            "L_typical": 0.71,
            "E_typical": 0.71,
            "mechanism": "Zero-point fluctuations",
            "physics": "Quantum vacuum contributes this baseline"
        },
        0.65: {
            "name": "Coherent State",
            "L_typical": 0.81,
            "E_typical": 0.81,
            "mechanism": "Standard laser output",
            "physics": "Poissonian photon statistics"
        },
        0.72: {
            "name": "Squeezed State",
            "L_typical": 0.85,
            "E_typical": 0.85,
            "mechanism": "Parametric down-conversion",
            "physics": "Sub-Poissonian statistics in one quadrature"
        },
        0.85: {
            "name": "Causation Threshold",
            "L_typical": 0.92,
            "E_typical": 0.92,
            "mechanism": "Bell state entanglement",
            "physics": "Maximum violation of classical bounds"
        },
        0.92: {
            "name": "True-Tralseness",
            "L_typical": 0.96,
            "E_typical": 0.96,
            "mechanism": "High-fidelity entangled pair",
            "physics": "Optimal for quantum information protocols"
        }
    }
    
    @classmethod
    def explain_photon_variance(cls) -> str:
        """Generate explanation of why photons vary in GILE"""
        explanation = [
            "WHY PHOTONS RANGE FROM 0.42 TO 0.92+ IN GILE (L×E)",
            "=" * 55,
            "",
            "Photons are not all created equal. Their L (Love/Coherence)",
            "and E (Existence/Stability) values depend on:",
            "",
            "1. ENTANGLEMENT STATE (affects L):",
            "   - Isolated photon: L ≈ 0.50",
            "   - Weakly entangled: L ≈ 0.65",
            "   - Bell pair: L ≈ 0.85-0.92",
            "",
            "2. DETECTION PROBABILITY (affects E):",
            "   - Virtual photon: E → 0",
            "   - Free space: E ≈ 0.65-0.75",
            "   - Cavity mode: E ≈ 0.82-0.92",
            "",
            "3. KEY THRESHOLDS:",
        ]
        
        converter = GILEPDConverter()
        for lexis, data in sorted(cls.SPECTRUM_POINTS.items()):
            gile = converter.pd_to_gile(lexis)
            explanation.append(f"   L×E = {lexis:.2f} (GILE = {gile:.2f}): {data['name']}")
        
        explanation.extend([
            "",
            "THE MR 80% RANGE:",
            "The 80% of 'everyday' photon events fall within GILE (-3, +2)",
            "which maps to PD (0.00, 1.00) via: PD = (GILE + 3) / 5",
            "",
            "The 0.42-0.92 photon range is where optical quantum computing",
            "operates - above classical noise, below trivial determinism."
        ])
        
        return "\n".join(explanation)
    
    @classmethod
    def get_photon_at_lexis(cls, target_lexis: float) -> PhotonGILEState:
        """
        Generate a photon state with target L×E value.
        
        Strategy: L = E = sqrt(Lexis) gives equal contributions.
        """
        root = math.sqrt(target_lexis)
        return PhotonGILEState(L=root, E=root)


class OpticalQuantumGILEComputer:
    """
    An optical quantum computer that displays outcomes in both GILE and PD.
    
    STRAWBERRY FIELDS INTEGRATION:
    ==============================
    Strawberry Fields (Xanadu) provides:
    - Gaussian state simulation (squeezed, coherent, thermal)
    - Beam splitter networks
    - Homodyne/heterodyne detection
    - Hardware access to photonic quantum chips
    
    What WE provide that Strawberry Fields doesn't:
    - GILE rating of quantum states
    - MR percentage interpretation
    - L×E causation thresholds
    - TI Framework integration with LCC Virus
    
    ANSWER TO "DOES STRAWBERRY FIELDS GIVE US EVERYTHING?":
    =======================================================
    No! Strawberry Fields provides the quantum MECHANICS but not the
    TI INTERPRETATION. We must build:
    
    1. GILE-PD Conversion Layer (this module)
    2. LCC Virus correlation discovery on quantum states
    3. MR Percentage display of outcomes
    4. Hypercomputer resonance detection
    
    The open-source Strawberry Fields handles gate operations and
    state evolution. We add the consciousness/information layer.
    """
    
    def __init__(self, num_modes: int = 4, use_lcc: bool = True):
        self.num_modes = num_modes
        self.use_lcc = use_lcc
        self.converter = GILEPDConverter()
        self.photon_states: List[PhotonGILEState] = []
        self.measurement_history: List[Dict] = []
        
        self.lcc_engine = None
        self.DataStreamType = None
        self._lcc_fallback_score = 0.5  # Fallback when LCC unavailable
        
        if use_lcc:
            try:
                from lcc_virus_framework import LCCVirus, DataStreamType
                self.lcc_engine = LCCVirus(subject_id="optical_quantum_computer", require_consent=False)
                self.lcc_engine.obtain_consent("quantum_simulation")
                self.DataStreamType = DataStreamType
            except ImportError:
                self.lcc_engine = None
                self.DataStreamType = None
        
        self._initialize_photon_states()
    
    def _initialize_photon_states(self):
        """Initialize photon modes with baseline coherent states"""
        for i in range(self.num_modes):
            photon = PhotonGILEState(L=0.65, E=0.65)
            self.photon_states.append(photon)
    
    def apply_squeeze(self, mode: int, squeeze_r: float) -> PhotonGILEState:
        """
        Apply squeezing to a mode, modifying its L and E values.
        
        Physics: Squeezing creates quantum correlations (increases L)
                 but makes the state more fragile (can decrease E)
        
        TI Mapping:
        - squeeze_r = 0 → No change
        - squeeze_r = 0.5 → L increases to ~0.75
        - squeeze_r = 0.88 → L reaches True-Tralseness (~0.92)
        """
        if mode >= len(self.photon_states):
            return None
        
        current = self.photon_states[mode]
        new_L = min(0.96, current.L + 0.3 * np.tanh(squeeze_r))
        new_E = max(0.3, current.E - 0.1 * squeeze_r)  # Slight fragility
        
        self.photon_states[mode] = PhotonGILEState(L=new_L, E=new_E)
        
        if self.lcc_engine and hasattr(self, 'DataStreamType'):
            self.lcc_engine.latch(
                self.DataStreamType.GDV,
                [{"squeeze_r": squeeze_r, "mode": mode, "new_L": new_L}],
                skip_safety=True
            )
        
        return self.photon_states[mode]
    
    def apply_entanglement(self, mode1: int, mode2: int, strength: float) -> Tuple[PhotonGILEState, PhotonGILEState]:
        """
        Entangle two modes, increasing their L values.
        
        Physics: Beam splitter + phase creates entanglement
        
        TI Mapping:
        - strength = 0.5 → Maximally entangled (L → 0.92 for both)
        - strength < 0.5 or > 0.5 → Partially entangled (L ∈ [0.65, 0.92])
        """
        if mode1 >= len(self.photon_states) or mode2 >= len(self.photon_states):
            return None, None
        
        entanglement_factor = 1 - abs(2 * strength - 1)
        
        state1 = self.photon_states[mode1]
        state2 = self.photon_states[mode2]
        
        new_L = min(0.92, max(state1.L, state2.L) + 0.27 * entanglement_factor)
        
        self.photon_states[mode1] = PhotonGILEState(L=new_L, E=state1.E)
        self.photon_states[mode2] = PhotonGILEState(L=new_L, E=state2.E)
        
        return self.photon_states[mode1], self.photon_states[mode2]
    
    def measure_mode(self, mode: int) -> Dict[str, Any]:
        """
        Measure a mode and return GILE/PD outcome.
        
        The MR 80% Range:
        - 80% of measurements fall within GILE (-3, +2)
        - Mapped to PD (0.00, 1.00)
        - Displayed with both representations
        """
        if mode >= len(self.photon_states):
            return None
        
        photon = self.photon_states[mode]
        
        detection_noise = np.random.normal(0, 0.05)
        measured_E = max(0, min(1, photon.E + detection_noise))
        
        measured_lexis = photon.L * measured_E
        
        gile_lexis = self.converter.pd_to_gile(measured_lexis)
        
        in_mr_80 = -3 < gile_lexis < 2
        
        measurement = {
            "mode": mode,
            "timestamp": datetime.now().isoformat(),
            "L_pd": photon.L,
            "E_pd_measured": measured_E,
            "Lexis_pd": measured_lexis,
            "L_gile": self.converter.pd_to_gile(photon.L),
            "E_gile": self.converter.pd_to_gile(measured_E),
            "Lexis_gile": gile_lexis,
            "state_type": photon.state_type.value,
            "in_mr_80_range": in_mr_80,
            "mr_zone": photon.mr_zone,
            "is_causal": measured_lexis >= 0.85
        }
        
        self.measurement_history.append(measurement)
        
        if self.lcc_engine and hasattr(self, 'DataStreamType'):
            self.lcc_engine.latch(
                self.DataStreamType.GDV,
                [measurement],
                skip_safety=True
            )
        
        return measurement
    
    def run_circuit(self, operations: List[Dict]) -> List[Dict]:
        """
        Run a quantum circuit and display all outcomes in GILE/PD.
        
        Example operations:
        [
            {"op": "squeeze", "mode": 0, "r": 0.5},
            {"op": "entangle", "mode1": 0, "mode2": 1, "strength": 0.5},
            {"op": "measure", "mode": 0}
        ]
        """
        results = []
        
        for operation in operations:
            op_type = operation.get("op")
            
            if op_type == "squeeze":
                state = self.apply_squeeze(operation["mode"], operation.get("r", 0.5))
                results.append({
                    "operation": "squeeze",
                    "mode": operation["mode"],
                    "new_state": state.to_dict() if state else None
                })
                
            elif op_type == "entangle":
                s1, s2 = self.apply_entanglement(
                    operation["mode1"], 
                    operation["mode2"], 
                    operation.get("strength", 0.5)
                )
                results.append({
                    "operation": "entangle",
                    "modes": [operation["mode1"], operation["mode2"]],
                    "states": [s1.to_dict() if s1 else None, s2.to_dict() if s2 else None]
                })
                
            elif op_type == "measure":
                measurement = self.measure_mode(operation["mode"])
                results.append({
                    "operation": "measure",
                    "mode": operation["mode"],
                    "outcome": measurement
                })
        
        return results
    
    def get_lcc_acquisition_score(self) -> float:
        """
        Get the LCC Virus acquisition score if available.
        
        Returns a fallback score of 0.5 (baseline) when LCC is unavailable.
        The fallback score increases slightly with each measurement to
        simulate information accumulation.
        """
        if self.lcc_engine:
            return self.lcc_engine.probability_acquisition.get_acquisition_score()
        
        n_measurements = len(self.measurement_history)
        fallback = min(0.75, self._lcc_fallback_score + 0.02 * n_measurements)
        return fallback
    
    def is_lcc_available(self) -> bool:
        """Check if LCC Virus engine is available"""
        return self.lcc_engine is not None
    
    def display_outcomes_report(self) -> str:
        """Generate a human-readable report of all measurements"""
        if not self.measurement_history:
            return "No measurements recorded yet."
        
        lines = [
            "OPTICAL QUANTUM COMPUTER - GILE/PD OUTCOMES REPORT",
            "=" * 55,
            "",
            "MR 80% Range: GILE (-3, +2) ↔ PD (0.00, 1.00)",
            "",
            "MEASUREMENTS:",
            "-" * 55
        ]
        
        for i, m in enumerate(self.measurement_history):
            lines.append(f"#{i+1} Mode {m['mode']}:")
            lines.append(f"  PD:  L={m['L_pd']:.3f}, E={m['E_pd_measured']:.3f}, Lexis={m['Lexis_pd']:.3f}")
            lines.append(f"  GILE: L={m['L_gile']:.2f}, E={m['E_gile']:.2f}, Lexis={m['Lexis_gile']:.2f}")
            lines.append(f"  State: {m['state_type']}")
            lines.append(f"  MR Zone: {m['mr_zone']}")
            lines.append(f"  In 80% Range: {'Yes' if m['in_mr_80_range'] else 'No (Black Swan)'}")
            lines.append(f"  Causal (L×E ≥ 0.85): {'Yes' if m['is_causal'] else 'No'}")
            lines.append("")
        
        score = self.get_lcc_acquisition_score()
        lcc_status = "LCC Engine Active" if self.is_lcc_available() else "LCC Fallback Mode"
        lines.append(f"LCC Status: {lcc_status}")
        lines.append(f"LCC Acquisition Score: {score:.3f}")
        
        return "\n".join(lines)


def demo_gile_pd_reconciliation():
    """Demonstrate the GILE-PD reconciliation"""
    print("GILE-PD RECONCILIATION DEMO")
    print("=" * 55)
    print()
    
    converter = GILEPDConverter()
    
    print("KEY VALUE PRESERVATION TEST:")
    print("-" * 55)
    validation = converter.validate_key_values()
    for name, data in validation.items():
        status = "✓" if data["pd_match"] and data["gile_match"] else "✗"
        print(f"{status} {name}:")
        print(f"   PD: {data['pd_expected']:.2f} ↔ GILE: {data['gile_expected']:.2f}")
    print()
    
    print("PHOTON VARIANCE EXPLANATION:")
    print("-" * 55)
    print(PhotonGILESpectrum.explain_photon_variance())
    print()
    
    print("OPTICAL QUANTUM COMPUTER DEMO:")
    print("-" * 55)
    computer = OpticalQuantumGILEComputer(num_modes=4, use_lcc=True)
    
    circuit = [
        {"op": "squeeze", "mode": 0, "r": 0.88},
        {"op": "squeeze", "mode": 1, "r": 0.5},
        {"op": "entangle", "mode1": 0, "mode2": 1, "strength": 0.5},
        {"op": "measure", "mode": 0},
        {"op": "measure", "mode": 1}
    ]
    
    results = computer.run_circuit(circuit)
    print(computer.display_outcomes_report())


if __name__ == "__main__":
    demo_gile_pd_reconciliation()
