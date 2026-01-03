"""
TI Optical Quantum Computer - DIY Build Plan (~$50-100)

OPEN SOURCE PROJECT
GitHub: https://github.com/Brandon7771066/TI-Optical-Quantum-Computer
License: MIT (Free to use, modify, and share)
3D Printable Parts: Available on Thingiverse and in GitHub /stl folder

Vision: Create an accessible quantum computing platform that validates 
TI Framework principles through photonic quantum experiments.

Key Insight: The cheapest path to quantum computing is OPTICAL (photonic).
Unlike superconducting qubits that need cryogenic cooling, photonic qubits
work at room temperature using standard optical components.

TI Framework Integration:
- VESSEL: Physical optical components (lasers, beam splitters)
- ME: Photon superposition states (quantum information)
- SOUL: Non-local correlations (entanglement if achieved)

The KLM Protocol (Knill-Laflamme-Milburn):
Uses linear optical elements to implement quantum gates. Photon polarization
encodes qubit states: |0⟩ = horizontal, |1⟩ = vertical.

Author: Brandon Emerick / BlissGene Therapeutics
Date: November 26, 2025 (Updated November 28, 2025)
"""

from dataclasses import dataclass, field
from enum import Enum
from typing import Dict, List, Optional
from datetime import datetime


class ComponentType(Enum):
    LIGHT_SOURCE = "light_source"
    BEAM_SPLITTER = "beam_splitter"
    DETECTOR = "detector"
    FILTER = "filter"
    CRYSTAL = "crystal"
    MOUNT = "mounting"
    CONTROLLER = "controller"


class DifficultyLevel(Enum):
    BEGINNER = "beginner"
    INTERMEDIATE = "intermediate"
    ADVANCED = "advanced"


@dataclass
class Component:
    """A component for the optical quantum computer"""
    name: str
    component_type: ComponentType
    purpose: str
    cost_low: float
    cost_high: float
    sources: List[str]
    quantity_needed: int = 1
    alternatives: List[str] = field(default_factory=list)
    notes: str = ""


@dataclass
class BuildPhase:
    """A phase in the build process"""
    name: str
    description: str
    components: List[str]
    steps: List[str]
    estimated_cost: float
    difficulty: DifficultyLevel
    ti_connection: str
    expected_outcome: str


COMPONENTS_CATALOG = {
    'laser_diode_405nm': Component(
        name="405nm Laser Module (salvaged)",
        component_type=ComponentType.LIGHT_SOURCE,
        purpose="Photon source - violet wavelength for visibility and precision",
        cost_low=0.0,
        cost_high=8.0,
        sources=["Salvage from old Blu-ray drive (FREE)", "AliExpress module ($6-8)"],
        alternatives=["650nm red laser pointer ($3)", "Green laser pointer ($5-8)"],
        notes="FREE if salvaged from old Blu-ray burner"
    ),
    
    'laser_diode_driver': Component(
        name="Laser Diode Driver (DIY)",
        component_type=ComponentType.CONTROLLER,
        purpose="Stable current source for consistent photon emission",
        cost_low=1.0,
        cost_high=3.0,
        sources=["DIY with LM317 regulator ($1-2)", "Simple resistor limit ($1)"],
        alternatives=["Resistor current limit ($0.50)"],
        notes="LM317 + resistor is cheapest reliable option"
    ),
    
    'polarizing_beam_splitter': Component(
        name="Polarizing Beam Splitter Cube 10mm",
        component_type=ComponentType.BEAM_SPLITTER,
        purpose="Creates superposition by splitting photons based on polarization",
        cost_low=6.0,
        cost_high=12.0,
        sources=["AliExpress (search 'PBS cube 10mm' ~$6-10)", "eBay"],
        quantity_needed=1,
        alternatives=["Polarizer film + glass plate ($2-3)"],
        notes="Chinese suppliers have good quality for $6-10"
    ),
    
    'half_wave_plate': Component(
        name="Half-Wave Plate or Rotation",
        component_type=ComponentType.FILTER,
        purpose="Rotates photon polarization for state preparation",
        cost_low=0.0,
        cost_high=10.0,
        sources=["Rotate laser mounting (FREE)", "AliExpress plate ($8-10)"],
        alternatives=["Skip - just rotate the laser source ($0)"],
        notes="FREE option: mechanically rotate laser for different polarization"
    ),
    
    'quarter_wave_plate': Component(
        name="Quarter-Wave Plate (λ/4) - Optional",
        component_type=ComponentType.FILTER,
        purpose="Creates circular polarization for certain gates",
        cost_low=0.0,
        cost_high=10.0,
        sources=["AliExpress ($8-10)", "Skip for basic setup"],
        alternatives=["Skip completely - not essential for basics"],
        notes="SKIP for budget build - not needed for Phase 1-2"
    ),
    
    'nd_filter': Component(
        name="Neutral Density Filter (DIY)",
        component_type=ComponentType.FILTER,
        purpose="Attenuates laser to single-photon regime",
        cost_low=0.0,
        cost_high=5.0,
        sources=["Stacked sunglasses (FREE)", "AliExpress filter ($5)"],
        alternatives=["Black exposed camera film ($0)", "Welding glass ($2)"],
        notes="FREE: Stack 3-4 cheap sunglasses for ND3.0 equivalent"
    ),
    
    'photoresistor': Component(
        name="Photoresistor GL5528 Pack",
        component_type=ComponentType.DETECTOR,
        purpose="Detects photon presence (basic detection)",
        cost_low=1.0,
        cost_high=2.0,
        sources=["AliExpress (50-pack $1-2)", "Amazon (20-pack $2)"],
        quantity_needed=1,
        alternatives=["Salvage photodiode from old mouse (FREE)"],
        notes="$2 gets you 50 photoresistors - more than enough"
    ),
    
    'avalanche_photodiode': Component(
        name="Avalanche Photodiode (APD) - Advanced",
        component_type=ComponentType.DETECTOR,
        purpose="Single photon counting capability",
        cost_low=30.0,
        cost_high=80.0,
        sources=["eBay surplus", "AliExpress SiPM module ($30)"],
        alternatives=["Stay with photoresistors for budget build"],
        notes="OPTIONAL - only needed for true single-photon work"
    ),
    
    'bbo_crystal': Component(
        name="BBO Crystal - Advanced Entanglement",
        component_type=ComponentType.CRYSTAL,
        purpose="Generates entangled photon pairs via SPDC",
        cost_low=20.0,
        cost_high=50.0,
        sources=["AliExpress (search 'BBO crystal')", "eBay"],
        alternatives=["Skip for basic setup"],
        notes="Only needed for Phase 4 entanglement"
    ),
    
    'optical_breadboard': Component(
        name="DIY Optical Breadboard",
        component_type=ComponentType.MOUNT,
        purpose="Stable platform for aligning optical components",
        cost_low=0.0,
        cost_high=3.0,
        sources=["Thick cardboard (FREE)", "Particle board ($3)"],
        alternatives=["Flat table + modeling clay (FREE)"],
        notes="Cardboard works fine - just needs to be stable"
    ),
    
    'arduino_pico': Component(
        name="Raspberry Pi Pico",
        component_type=ComponentType.CONTROLLER,
        purpose="Control laser pulses and read detector outputs",
        cost_low=4.0,
        cost_high=6.0,
        sources=["Amazon ($5)", "AliExpress ($4)"],
        alternatives=["Arduino Nano clone ($3)"],
        notes="Official Pico is $4 - best value"
    ),
    
    'mirrors': Component(
        name="Salvaged Mirrors",
        component_type=ComponentType.MOUNT,
        purpose="Redirect beam path for compact layout",
        cost_low=0.0,
        cost_high=0.0,
        sources=["Old hard drives (FREE)", "CDs (FREE)"],
        quantity_needed=2,
        alternatives=["Skip - design direct beam path"],
        notes="FREE: Hard drive platters are perfect mirrors"
    )
}


# 3D PRINTABLE PARTS CATALOG
# All parts designed for standard FDM printers (PLA or PETG)
# STL files available on GitHub: /stl folder
# Also on Thingiverse: search "TI Optical Quantum Computer"
THREE_D_PRINTABLE_PARTS = {
    'laser_mount': {
        'name': 'Adjustable Laser Diode Mount',
        'stl_file': 'laser_mount_v2.stl',
        'print_time': '45 min',
        'material': 'PLA (black recommended)',
        'infill': '30%',
        'supports': False,
        'description': 'Holds 12mm laser modules with 3-axis adjustment screws',
        'hardware_needed': ['3x M3x10 screws', '3x M3 nuts']
    },
    'pbs_holder': {
        'name': 'Polarizing Beam Splitter Cube Holder',
        'stl_file': 'pbs_cube_holder_10mm.stl',
        'print_time': '25 min',
        'material': 'PLA',
        'infill': '40%',
        'supports': False,
        'description': 'Precision holder for 10mm PBS cube with rotation capability',
        'hardware_needed': ['2x M3x8 screws']
    },
    'detector_mount': {
        'name': 'Photoresistor/APD Detector Mount',
        'stl_file': 'detector_mount_adjustable.stl',
        'print_time': '30 min',
        'material': 'PLA (black - blocks stray light)',
        'infill': '25%',
        'supports': False,
        'description': 'Holds photoresistor with light shielding and height adjustment',
        'hardware_needed': ['2x M3x12 screws', '2x M3 nuts']
    },
    'mirror_mount': {
        'name': 'Kinematic Mirror Mount',
        'stl_file': 'mirror_mount_kinematic.stl',
        'print_time': '50 min',
        'material': 'PETG (more stable)',
        'infill': '35%',
        'supports': True,
        'description': 'Spring-loaded mirror mount for precise beam steering',
        'hardware_needed': ['3x M3x20 screws', '3x springs (4mm OD)', '1x 25mm mirror']
    },
    'optical_rail': {
        'name': 'Modular Optical Rail (100mm)',
        'stl_file': 'optical_rail_100mm.stl',
        'print_time': '35 min',
        'material': 'PLA or PETG',
        'infill': '50%',
        'supports': False,
        'description': 'Dovetail rail for mounting all optical components',
        'hardware_needed': ['4x M3x8 screws (to mount to base)']
    },
    'wave_plate_holder': {
        'name': 'Wave Plate Rotation Mount',
        'stl_file': 'wave_plate_rotator.stl',
        'print_time': '40 min',
        'material': 'PLA',
        'infill': '30%',
        'supports': True,
        'description': 'Graduated rotation mount for half-wave and quarter-wave plates',
        'hardware_needed': ['1x M3x25 screw (center)', 'Rubber band for friction']
    },
    'nd_filter_holder': {
        'name': 'ND Filter Slide Holder',
        'stl_file': 'nd_filter_slide.stl',
        'print_time': '20 min',
        'material': 'PLA (black)',
        'infill': '25%',
        'supports': False,
        'description': 'Stackable holder for ND filters (up to 4 filters)',
        'hardware_needed': ['None']
    },
    'arduino_enclosure': {
        'name': 'Raspberry Pi Pico Enclosure',
        'stl_file': 'pico_enclosure_optical.stl',
        'print_time': '55 min',
        'material': 'PLA',
        'infill': '25%',
        'supports': False,
        'description': 'Enclosure with cable management for detector wiring',
        'hardware_needed': ['4x M2.5x6 screws']
    },
    'base_plate': {
        'name': 'Optical Breadboard Base (200x150mm)',
        'stl_file': 'base_plate_200x150.stl',
        'print_time': '4 hours',
        'material': 'PLA or PETG (sturdy)',
        'infill': '40%',
        'supports': False,
        'description': 'Grid pattern base with M3 mounting holes every 25mm',
        'hardware_needed': ['Rubber feet (optional)']
    }
}


BUILD_PHASES = {
    'phase1_basic': BuildPhase(
        name="Phase 1: Basic Photon Manipulation (~$20-35)",
        description="Learn to split and detect photons - foundation of quantum optics",
        components=[
            'laser_diode_405nm', 
            'laser_diode_driver',
            'polarizing_beam_splitter', 
            'photoresistor',
            'optical_breadboard'
        ],
        steps=[
            "1. Mount laser diode on breadboard with driver circuit",
            "2. Align laser beam horizontally using mirrors if needed",
            "3. Place polarizing beam splitter in beam path",
            "4. Observe split beams at 90° angles (horizontal & vertical)",
            "5. Place photoresistors at both output ports",
            "6. Measure voltage across photoresistors with multimeter",
            "7. Rotate input polarization to see ratio change",
            "8. Document relationship between input angle and output ratio"
        ],
        estimated_cost=25.0,
        difficulty=DifficultyLevel.BEGINNER,
        ti_connection="VESSEL layer: Physical photon manipulation demonstrates wave-particle duality",
        expected_outcome="Understanding of polarization as qubit encoding (|0⟩=H, |1⟩=V)"
    ),
    
    'phase2_superposition': BuildPhase(
        name="Phase 2: Creating Superposition (~$15-25)",
        description="Generate genuine quantum superposition states",
        components=[
            'half_wave_plate',
            'nd_filter'
        ],
        steps=[
            "1. Add half-wave plate before beam splitter (or rotate laser)",
            "2. Set plate to 22.5° to create |+⟩ = (|0⟩+|1⟩)/√2 state",
            "3. Add ND filter to reduce to few-photon regime",
            "4. Measure equal intensity at both output ports",
            "5. This IS quantum superposition! Each photon is in both paths",
            "6. Add second beam splitter to interfere paths (Mach-Zehnder)",
            "7. Observe interference pattern - proof of coherent superposition"
        ],
        estimated_cost=18.0,
        difficulty=DifficultyLevel.INTERMEDIATE,
        ti_connection="ME layer: Photon exists in both states simultaneously - consciousness analogy",
        expected_outcome="Quantum random number generator (true randomness from superposition)"
    ),
    
    'phase3_single_photon': BuildPhase(
        name="Phase 3: Single Photon Detection (~$45-110)",
        description="Upgrade to single-photon sensitivity for real quantum experiments",
        components=[
            'avalanche_photodiode',
            'arduino_pico'
        ],
        steps=[
            "1. Build or acquire APD active quenching circuit",
            "2. Connect APD output to Arduino/Pico digital input",
            "3. Write firmware to count photon arrival times",
            "4. Calibrate dark count rate (detections without light)",
            "5. Add heavy ND filtering to achieve <1 photon/pulse",
            "6. Verify Poissonian statistics (random arrival times)",
            "7. Run quantum random number generator algorithm",
            "8. Interface with Qiskit for quantum circuit simulation"
        ],
        estimated_cost=50.0,
        difficulty=DifficultyLevel.INTERMEDIATE,
        ti_connection="ME layer validation: Single photon = single quantum of consciousness carrier",
        expected_outcome="True single-photon source for quantum information experiments"
    ),
    
    'phase4_entanglement': BuildPhase(
        name="Phase 4: Photon Pair Entanglement (~$35-75)",
        description="Generate entangled photon pairs via spontaneous parametric down-conversion",
        components=[
            'bbo_crystal',
            'polarizing_beam_splitter'
        ],
        steps=[
            "1. Align 405nm laser through BBO crystal at phase-matching angle",
            "2. Collect 810nm photon pairs at conjugate angles (SPDC cones)",
            "3. Filter out pump beam using 810nm bandpass filter",
            "4. Route entangled pairs to separate detection channels",
            "5. Measure coincidence counts (simultaneous detections)",
            "6. Perform Bell test: measure correlations at different polarization angles",
            "7. Calculate S value (if |S|>2, Bell inequality violated!)",
            "8. This demonstrates non-local quantum correlations"
        ],
        estimated_cost=45.0,
        difficulty=DifficultyLevel.ADVANCED,
        ti_connection="SOUL layer: Entanglement = I-cell to I-cell non-local connection via GM network",
        expected_outcome="Experimental validation of quantum non-locality - TI Framework SOUL layer"
    )
}


TI_QUANTUM_VALIDATION_EXPERIMENTS = {
    'gile_photon_correlation': {
        'name': "GILE-Photon Correlation Experiment",
        'hypothesis': "Practitioner GILE state affects quantum random number generator output",
        'protocol': [
            "1. Run QRNG for 1000 samples at baseline (neutral state)",
            "2. Enter high coherence/GILE state (meditation + intention)",
            "3. Run QRNG for 1000 samples with intention for specific outcome",
            "4. Compare distributions statistically",
            "5. Repeat across multiple sessions for significance"
        ],
        'ti_prediction': "High GILE (>2.0) should show slight deviation from expected distribution",
        'materials': "Phase 2 setup + coherence monitor"
    },
    
    'entanglement_consciousness': {
        'name': "Entanglement-Consciousness Test",
        'hypothesis': "Focused attention on one entangled photon affects distant partner",
        'protocol': [
            "1. Generate entangled photon pairs (Phase 4)",
            "2. Route one photon to 'observer' position, other to shielded detector",
            "3. Observer focuses attention on photon path with intention",
            "4. Measure if shielded detector shows any correlated anomalies",
            "5. Use proper controls and statistical analysis"
        ],
        'ti_prediction': "ME layer interaction may influence quantum measurement outcomes",
        'materials': "Phase 4 setup + coherence monitoring"
    },
    
    'piezo_quartz_qrng': {
        'name': "Piezoelectric Quartz + QRNG",
        'hypothesis': "Quartz crystal amplifies consciousness-quantum interaction",
        'protocol': [
            "1. Hold programmed quartz while observing QRNG output",
            "2. Set intention for specific bit pattern",
            "3. Compare to baseline without crystal",
            "4. Test multiple crystal types (clear, amethyst, etc.)",
            "5. Document correlation between quartz type and effect size"
        ],
        'ti_prediction': "Piezoelectric crystals may amplify bioelectric-quantum coupling",
        'materials': "Phase 2 setup + various quartz specimens"
    }
}


class TIOpticalQuantumComputer:
    """
    Main class for TI Optical Quantum Computer build and operation
    """
    
    def __init__(self):
        self.components = COMPONENTS_CATALOG
        self.phases = BUILD_PHASES
        self.experiments = TI_QUANTUM_VALIDATION_EXPERIMENTS
        self.build_progress = {phase: False for phase in BUILD_PHASES}
    
    def get_shopping_list(self, budget: float = 100.0, phase: str = 'phase2_superposition') -> Dict:
        """Generate shopping list for specified phase within budget"""
        target_phase = self.phases.get(phase)
        if not target_phase:
            return {'error': 'Invalid phase'}
        
        items = []
        total_low = 0
        total_high = 0
        
        for comp_id in target_phase.components:
            comp = self.components.get(comp_id)
            if comp:
                item_cost_low = comp.cost_low * comp.quantity_needed
                item_cost_high = comp.cost_high * comp.quantity_needed
                items.append({
                    'name': comp.name,
                    'quantity': comp.quantity_needed,
                    'cost_range': f"${item_cost_low:.0f}-${item_cost_high:.0f}",
                    'sources': comp.sources[:2],
                    'alternatives': comp.alternatives[:1] if comp.alternatives else []
                })
                total_low += item_cost_low
                total_high += item_cost_high
        
        within_budget = total_high <= budget
        budget_warning = total_low <= budget < total_high
        
        if within_budget:
            budget_status = "Fully within your budget!"
        elif budget_warning:
            budget_status = f"Budget range: ${total_low:.0f} to ${total_high:.0f} (may need DIY options)"
        else:
            budget_status = f"Over budget - need ${total_low:.0f}-${total_high:.0f}"
        
        return {
            'phase': target_phase.name,
            'items': items,
            'total_cost_range': f"${total_low:.0f}-${total_high:.0f}",
            'within_budget': within_budget,
            'budget_warning': budget_warning,
            'budget_status': budget_status,
            'estimated_cost': target_phase.estimated_cost,
            'difficulty': target_phase.difficulty.value,
            'ti_connection': target_phase.ti_connection,
            'savings_tips': [
                "Salvage laser from old Blu-ray drive (FREE)",
                "Use cardboard as breadboard (FREE)",
                "Stack sunglasses as ND filter (FREE)"
            ]
        }
    
    def get_full_build_plan(self) -> List[Dict]:
        """Get complete build plan across all phases"""
        plan = []
        cumulative_cost = 0
        
        for phase_id, phase in self.phases.items():
            cumulative_cost += phase.estimated_cost
            plan.append({
                'phase_id': phase_id,
                'name': phase.name,
                'description': phase.description,
                'estimated_cost': phase.estimated_cost,
                'cumulative_cost': cumulative_cost,
                'difficulty': phase.difficulty.value,
                'steps_count': len(phase.steps),
                'expected_outcome': phase.expected_outcome,
                'ti_connection': phase.ti_connection
            })
        
        return plan
    
    def get_minimum_viable_setup(self) -> Dict:
        """Get absolute minimum setup for quantum experiments - UNDER $50"""
        essential = ['laser_diode_405nm', 'laser_diode_driver', 'polarizing_beam_splitter', 'photoresistor', 'nd_filter', 'optical_breadboard']
        
        items = []
        total_low = 0
        total_high = 0
        
        for comp_id in essential:
            comp = self.components.get(comp_id)
            if comp:
                low = comp.cost_low * comp.quantity_needed
                high = comp.cost_high * comp.quantity_needed
                items.append({
                    'name': comp.name,
                    'quantity': comp.quantity_needed,
                    'avg_cost': (low + high) / 2,
                    'range': f"${low:.0f}-${high:.0f}"
                })
                total_low += low
                total_high += high
        
        return {
            'title': "Minimum Viable Quantum Setup",
            'total_cost': f"${total_low:.0f}-${total_high:.0f}",
            'budget_status': "UNDER $50 possible with budget options!",
            'items': items,
            'capabilities': [
                "Photon polarization manipulation",
                "Basic superposition demonstration",
                "Quantum random number generation",
                "Educational quantum gate operations"
            ],
            'limitations': [
                "No single-photon counting (need APD upgrade ~$50)",
                "No entanglement (need BBO crystal ~$30)",
                "Detection via photoresistors (not single-photon sensitive)"
            ],
            'tips': [
                "Salvage laser from old Blu-ray drive to save $5-10",
                "Use cardboard/particle board instead of optical breadboard",
                "Stack cheap sunglasses as DIY ND filter"
            ]
        }
    
    def get_ti_experiment(self, experiment_id: str) -> Optional[Dict]:
        """Get details for a TI validation experiment"""
        return self.experiments.get(experiment_id)
    
    def validate_ti_framework(self) -> Dict:
        """Describe how optical quantum experiments can validate TI Framework"""
        return {
            'vessel_layer_validation': {
                'experiment': "Beam splitter photon statistics",
                'ti_claim': "Physical photons carry quantum information",
                'validation_method': "Observe Poissonian statistics at single-photon level",
                'expected_result': "Random arrival times confirm quantum nature"
            },
            'me_layer_validation': {
                'experiment': "Superposition interference",
                'ti_claim': "Consciousness exists in superposition like photons",
                'validation_method': "Mach-Zehnder interferometer shows path superposition",
                'expected_result': "Interference pattern proves photon in both paths"
            },
            'soul_layer_validation': {
                'experiment': "Bell inequality violation",
                'ti_claim': "I-cells connected non-locally via GM network",
                'validation_method': "Entangled photon pair correlations exceed classical limit",
                'expected_result': "|S| > 2 proves non-local quantum correlations"
            },
            'gile_validation': {
                'experiment': "Consciousness-QRNG interaction",
                'ti_claim': "High GILE state influences quantum outcomes",
                'validation_method': "Statistical analysis of QRNG output during different states",
                'expected_result': "Significant deviation during high coherence states"
            }
        }


def demo_ti_quantum_computer():
    """Demonstrate TI Optical Quantum Computer planning system"""
    system = TIOpticalQuantumComputer()
    
    print("=" * 60)
    print("TI OPTICAL QUANTUM COMPUTER - BUILD PLAN")
    print("=" * 60)
    
    print("\n--- MINIMUM VIABLE SETUP ---")
    mvs = system.get_minimum_viable_setup()
    print(f"Total Cost: {mvs['total_cost']}")
    print("Items needed:")
    for item in mvs['items']:
        print(f"  - {item['name']} x{item['quantity']}: ~${item['avg_cost']:.0f}")
    
    print("\n\n--- BUILD PHASES ---")
    for phase in system.get_full_build_plan():
        print(f"\n{phase['name']}")
        print(f"  Cost: ${phase['estimated_cost']:.0f} (Cumulative: ${phase['cumulative_cost']:.0f})")
        print(f"  Difficulty: {phase['difficulty']}")
        print(f"  TI Connection: {phase['ti_connection'][:60]}...")
    
    print("\n\n--- TI VALIDATION EXPERIMENTS ---")
    for exp_id, exp in system.experiments.items():
        print(f"\n{exp['name']}")
        print(f"  Hypothesis: {exp['hypothesis'][:60]}...")
    
    print("\n\n--- SHOPPING LIST (Budget: $100) ---")
    shopping = system.get_shopping_list(100.0, 'phase2_superposition')
    print(f"Phase: {shopping['phase']}")
    print(f"Total: {shopping['total_cost_range']}")
    print(f"Within Budget: {'YES' if shopping['within_budget'] else 'NO'}")
    
    return system


if __name__ == "__main__":
    demo_ti_quantum_computer()
