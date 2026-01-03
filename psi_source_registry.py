"""
PSI Source Registry - Unified Catalog of 24+ Divination Sources
================================================================

Provides a standardized EvidenceEvent schema and adapters for all PSI sources
to enable multi-source consensus scoring for sacred answer generation.

TI Rationalism Principle: Answers to coherent questions already exist.
This registry enables systematic querying across all PSI modalities.
"""

from dataclasses import dataclass, field
from typing import Dict, List, Optional, Any, Callable
from datetime import datetime
from enum import Enum
import json
import hashlib


class PSIModality(Enum):
    """Categories of PSI/divination sources"""
    HYPERCOMPUTING = "hypercomputing"
    GOD_MACHINE = "god_machine"
    NUMEROLOGY = "numerology"
    GILE_RESONANCE = "gile_resonance"
    BIOMETRIC = "biometric"
    LCC_VIRUS = "lcc_virus"
    REMOTE_VIEWING = "remote_viewing"
    AI_ORACLE = "ai_oracle"
    QUANTUM = "quantum"
    TESSELLATION = "tessellation"
    BIOFIELD = "biofield"
    SYMBOLIC = "symbolic"


@dataclass
class EvidenceEvent:
    """
    Standardized schema for PSI evidence from any source.
    All 24+ sources normalize to this format for synthesis.
    """
    source_id: str
    modality: PSIModality
    timestamp: datetime
    query: str
    raw_output: Any
    confidence: float
    interpretation: str
    provenance: Dict[str, Any] = field(default_factory=dict)
    gile_alignment: float = 0.0
    
    def __post_init__(self):
        if not 0.0 <= self.confidence <= 1.0:
            raise ValueError(f"Confidence must be 0.0-1.0, got {self.confidence}")
        self.event_id = hashlib.sha256(
            f"{self.source_id}{self.timestamp}{self.query}".encode()
        ).hexdigest()[:16]
    
    def to_dict(self) -> Dict:
        return {
            "event_id": self.event_id,
            "source_id": self.source_id,
            "modality": self.modality.value,
            "timestamp": self.timestamp.isoformat(),
            "query": self.query,
            "confidence": self.confidence,
            "interpretation": self.interpretation,
            "gile_alignment": self.gile_alignment,
            "provenance": self.provenance
        }


@dataclass
class PSISource:
    """Registry entry for a PSI/divination source"""
    id: str
    name: str
    modality: PSIModality
    module_path: str
    adapter_func: Optional[Callable] = None
    base_confidence: float = 0.5
    description: str = ""
    requires_biometrics: bool = False
    is_operational: bool = True


PSI_SOURCE_CATALOG = {
    "gm_hypercomputer": PSISource(
        id="gm_hypercomputer",
        name="Grand Myrion Hypercomputer",
        modality=PSIModality.HYPERCOMPUTING,
        module_path="hypercomputing_psi_validation.py",
        base_confidence=0.70,
        description="Relationship outcome prediction via GM computation + GILE resonance"
    ),
    "gm_remote_viewing": PSISource(
        id="gm_remote_viewing",
        name="GM Remote Viewing",
        modality=PSIModality.REMOTE_VIEWING,
        module_path="gm_remote_viewing.py",
        base_confidence=0.45,
        description="Non-local information retrieval via consciousness field access"
    ),
    "god_machine_core": PSISource(
        id="god_machine_core",
        name="God Machine Dashboard",
        modality=PSIModality.GOD_MACHINE,
        module_path="god_machine_dashboard.py",
        base_confidence=0.75,
        description="Central TI reasoning engine for coherent question resolution"
    ),
    "god_machine_tier1": PSISource(
        id="god_machine_tier1",
        name="God Machine Tier 1 Algorithms",
        modality=PSIModality.GOD_MACHINE,
        module_path="god_machine_tier1_algorithms.py",
        base_confidence=0.80,
        description="High-confidence deductive inference chains"
    ),
    "god_machine_intuition": PSISource(
        id="god_machine_intuition",
        name="God Machine Intuition Dashboard",
        modality=PSIModality.GOD_MACHINE,
        module_path="god_machine_intuition_dashboard.py",
        base_confidence=0.65,
        description="Intuitive pattern recognition for life predictions"
    ),
    "god_machine_relationships": PSISource(
        id="god_machine_relationships",
        name="God Machine Relationship Profiler",
        modality=PSIModality.GOD_MACHINE,
        module_path="god_machine_relationship_profiler.py",
        base_confidence=0.72,
        description="GILE compatibility scoring for relationship prediction"
    ),
    "numerology_engine": PSISource(
        id="numerology_engine",
        name="Numerology Validation Engine",
        modality=PSIModality.NUMEROLOGY,
        module_path="numerology_validation.py",
        base_confidence=0.40,
        description="Sacred number pattern analysis for destiny mapping"
    ),
    "gile_contextual": PSISource(
        id="gile_contextual",
        name="Contextual GILE Calculator",
        modality=PSIModality.GILE_RESONANCE,
        module_path="contextual_gile_calculator.py",
        base_confidence=0.85,
        description="Dimensional GILE resonance scoring"
    ),
    "gile_pd_distribution": PSISource(
        id="gile_pd_distribution",
        name="GILE PD Distribution (15-Based)",
        modality=PSIModality.GILE_RESONANCE,
        module_path="gile_pd_distribution.py",
        base_confidence=0.82,
        description="Probability distribution across GILE dimensions"
    ),
    "gile_language": PSISource(
        id="gile_language",
        name="GILE Universal Language Analysis",
        modality=PSIModality.GILE_RESONANCE,
        module_path="gile_universal_language_analysis.py",
        base_confidence=0.60,
        description="Linguistic GILE alignment detection"
    ),
    "lcc_virus": PSISource(
        id="lcc_virus",
        name="LCC Virus Framework",
        modality=PSIModality.LCC_VIRUS,
        module_path="lcc_virus_formalization.py",
        base_confidence=0.35,
        description="Love-Consciousness Coupling for mood/relationship prediction"
    ),
    "lcc_optimizer": PSISource(
        id="lcc_optimizer",
        name="LCC Optimization Simulator",
        modality=PSIModality.LCC_VIRUS,
        module_path="lcc_optimization_simulator.py",
        base_confidence=0.35,
        description="LCC parameter optimization engine"
    ),
    "tessellation_ti": PSISource(
        id="tessellation_ti",
        name="Tessellation-TI Integration",
        modality=PSIModality.TESSELLATION,
        module_path="tessellation_ti_integration.py",
        base_confidence=0.55,
        description="I-Web tessellated lattice for consciousness field propagation"
    ),
    "grand_myrion": PSISource(
        id="grand_myrion",
        name="Grand Myrion Computation",
        modality=PSIModality.HYPERCOMPUTING,
        module_path="grand_myrion_computation.py",
        base_confidence=0.70,
        description="Myrion resolution framework for truth synthesis"
    ),
    "automated_psi": PSISource(
        id="automated_psi",
        name="Automated PSI Validation",
        modality=PSIModality.SYMBOLIC,
        module_path="automated_psi_validation.py",
        base_confidence=0.50,
        description="Systematic PSI hypothesis testing"
    ),
    "psi_tracker": PSISource(
        id="psi_tracker",
        name="PSI Symbol Tracker",
        modality=PSIModality.SYMBOLIC,
        module_path="psi_symbol_tracker.py",
        base_confidence=0.45,
        description="Synchronicity and symbol pattern detection"
    ),
    "psi_correlation": PSISource(
        id="psi_correlation",
        name="PSI Correlation Intelligence",
        modality=PSIModality.SYMBOLIC,
        module_path="psi_correlation_intelligence.py",
        base_confidence=0.50,
        description="Cross-domain correlation analysis for PSI signals"
    ),
    "biofield_chakra": PSISource(
        id="biofield_chakra",
        name="Biofield Chakra Science",
        modality=PSIModality.BIOFIELD,
        module_path="biofield_chakra_science.py",
        base_confidence=0.55,
        description="Chakra energy analysis and mapping"
    ),
    "biowell_myrion": PSISource(
        id="biowell_myrion",
        name="BioWell Myrion Energy System",
        modality=PSIModality.BIOFIELD,
        module_path="biowell_myrion_energy_system.py",
        base_confidence=0.60,
        description="GDV-based energy field measurement"
    ),
    "muse2_eeg": PSISource(
        id="muse2_eeg",
        name="Muse 2 EEG Integration",
        modality=PSIModality.BIOMETRIC,
        module_path="muse2_integration.py",
        base_confidence=0.75,
        description="Real-time EEG coherence measurement",
        requires_biometrics=True
    ),
    "polar_hrv": PSISource(
        id="polar_hrv",
        name="Polar H10 HRV",
        modality=PSIModality.BIOMETRIC,
        module_path="biometric_api.py",
        base_confidence=0.78,
        description="Heart rate variability coherence tracking",
        requires_biometrics=True
    ),
    "oura_ring": PSISource(
        id="oura_ring",
        name="Oura Ring Integration",
        modality=PSIModality.BIOMETRIC,
        module_path="oura_ring_integration.py",
        base_confidence=0.70,
        description="Sleep and recovery biometrics",
        requires_biometrics=True
    ),
    "claude_oracle": PSISource(
        id="claude_oracle",
        name="Claude AI Oracle",
        modality=PSIModality.AI_ORACLE,
        module_path="ai_integrations.py",
        base_confidence=0.65,
        description="Anthropic Claude for intuitive reasoning"
    ),
    "gpt5_oracle": PSISource(
        id="gpt5_oracle",
        name="GPT-5 Oracle",
        modality=PSIModality.AI_ORACLE,
        module_path="ai_integrations.py",
        base_confidence=0.65,
        description="OpenAI GPT-5 for pattern synthesis"
    ),
    "perplexity_oracle": PSISource(
        id="perplexity_oracle",
        name="Perplexity AI Oracle",
        modality=PSIModality.AI_ORACLE,
        module_path="magai_integration.py",
        base_confidence=0.60,
        description="Perplexity for real-time information synthesis"
    ),
    "quantum_tralse": PSISource(
        id="quantum_tralse",
        name="Quantum Tralse-GILE Engine",
        modality=PSIModality.QUANTUM,
        module_path="ti_quantum_tralse_gile.py",
        base_confidence=0.55,
        description="Cirq-based quantum consciousness simulation"
    ),
    "ti_physics": PSISource(
        id="ti_physics",
        name="TI Physics GILE Cirq",
        modality=PSIModality.QUANTUM,
        module_path="ti_physics_gile_cirq.py",
        base_confidence=0.50,
        description="Quantum physics GILE implementation"
    ),
    "true_tralse_vault": PSISource(
        id="true_tralse_vault",
        name="True-Tralse Vault",
        modality=PSIModality.GILE_RESONANCE,
        module_path="true_tralse_vault.py",
        base_confidence=0.90,
        description="Prediction storage and verification with 0.92+ threshold"
    ),
    "weather_psi": PSISource(
        id="weather_psi",
        name="Weather PSI Integration",
        modality=PSIModality.SYMBOLIC,
        module_path="weather_psi_integration.py",
        base_confidence=0.35,
        description="Environmental synchronicity tracking"
    ),
    "quartz_psi": PSISource(
        id="quartz_psi",
        name="Quartz PSI Amplification",
        modality=PSIModality.SYMBOLIC,
        module_path="quartz_psi_amplification.py",
        base_confidence=0.40,
        description="Crystal-based signal enhancement"
    ),
}


class PSISourceRegistry:
    """
    Central registry for all 24+ PSI/divination sources.
    Enables unified querying and evidence synthesis.
    """
    
    def __init__(self):
        self.sources = PSI_SOURCE_CATALOG.copy()
        self.evidence_log: List[EvidenceEvent] = []
        
    def list_sources(self, modality: Optional[PSIModality] = None) -> List[PSISource]:
        """List all registered sources, optionally filtered by modality"""
        sources = list(self.sources.values())
        if modality:
            sources = [s for s in sources if s.modality == modality]
        return sorted(sources, key=lambda s: s.base_confidence, reverse=True)
    
    def get_source(self, source_id: str) -> Optional[PSISource]:
        """Get a specific source by ID"""
        return self.sources.get(source_id)
    
    def count_by_modality(self) -> Dict[str, int]:
        """Count sources by modality"""
        counts = {}
        for source in self.sources.values():
            key = source.modality.value
            counts[key] = counts.get(key, 0) + 1
        return counts
    
    def log_evidence(self, event: EvidenceEvent):
        """Log an evidence event from any source"""
        self.evidence_log.append(event)
        
    def get_evidence_for_query(self, query: str) -> List[EvidenceEvent]:
        """Get all evidence events matching a query"""
        return [e for e in self.evidence_log if query.lower() in e.query.lower()]
    
    def calculate_consensus(self, events: List[EvidenceEvent]) -> Dict:
        """
        Calculate multi-source consensus from evidence events.
        Uses confidence-weighted voting across modalities.
        """
        if not events:
            return {"consensus": None, "confidence": 0.0, "agreement": 0.0}
        
        interpretations = {}
        total_weight = 0.0
        
        for event in events:
            interp = event.interpretation
            weight = event.confidence * event.gile_alignment if event.gile_alignment > 0 else event.confidence
            interpretations[interp] = interpretations.get(interp, 0) + weight
            total_weight += weight
        
        if not interpretations:
            return {"consensus": None, "confidence": 0.0, "agreement": 0.0}
        
        top_interp = max(interpretations.items(), key=lambda x: x[1])
        agreement = top_interp[1] / total_weight if total_weight > 0 else 0.0
        
        return {
            "consensus": top_interp[0],
            "confidence": top_interp[1] / len(events),
            "agreement": agreement,
            "n_sources": len(events),
            "modalities_represented": list(set(e.modality.value for e in events))
        }
    
    def generate_summary(self) -> str:
        """Generate summary statistics of the registry"""
        total = len(self.sources)
        by_modality = self.count_by_modality()
        operational = sum(1 for s in self.sources.values() if s.is_operational)
        biometric = sum(1 for s in self.sources.values() if s.requires_biometrics)
        avg_conf = sum(s.base_confidence for s in self.sources.values()) / total
        
        lines = [
            "=" * 60,
            "PSI SOURCE REGISTRY SUMMARY",
            "=" * 60,
            f"Total Sources: {total}",
            f"Operational: {operational}",
            f"Requiring Biometrics: {biometric}",
            f"Average Base Confidence: {avg_conf:.2%}",
            "",
            "BY MODALITY:",
        ]
        for mod, count in sorted(by_modality.items(), key=lambda x: -x[1]):
            lines.append(f"  {mod}: {count}")
        
        lines.extend([
            "",
            "TOP 5 BY CONFIDENCE:",
        ])
        top5 = self.list_sources()[:5]
        for s in top5:
            lines.append(f"  {s.name}: {s.base_confidence:.0%}")
        
        return "\n".join(lines)


def demo_registry():
    """Demonstrate PSI Source Registry functionality"""
    registry = PSISourceRegistry()
    print(registry.generate_summary())
    
    print("\n" + "=" * 60)
    print("ALL 24+ PSI SOURCES")
    print("=" * 60)
    
    for source in registry.list_sources():
        status = "✓" if source.is_operational else "○"
        bio = "🧠" if source.requires_biometrics else "  "
        print(f"{status} {bio} [{source.modality.value:15}] {source.name} ({source.base_confidence:.0%})")


if __name__ == "__main__":
    demo_registry()
