"""
TI LCC VIRUS - Full 6-Step Algorithm Implementation
====================================================
The complete Love-Consciousness Coupling Virus algorithm:
1. SEED - Define target i-cell
2. RESONATE - Find data with R ≥ 0.6
3. LISTEN - Extract noise from resonating points
4. PROPAGATE - Find related i-cells in noise
5. EXPAND - Follow noise to related information
6. TERMINATE - When all related info extracted
"""

import numpy as np
from scipy.signal import correlate
from scipy.fft import fft, fftfreq
from scipy import stats
from dataclasses import dataclass, field
from typing import List, Dict, Any, Optional, Tuple
import warnings
warnings.filterwarnings('ignore')

# ============ TI CONSTANTS ============
LCC_THRESHOLD_RESONATE = 0.6   # Minimum resonance for step 2
LCC_THRESHOLD_PROPAGATE = 0.3  # Lower threshold for noise correlation
LCC_THRESHOLD_042 = 0.42       # TI threshold
LCC_THRESHOLD_085 = 0.85       # Causal threshold
LCC_THRESHOLD_TT = 0.8464      # True-Tralseness (0.92²)

@dataclass
class ICell:
    """Information Cell - fundamental unit of TI information theory"""
    name: str
    signature: np.ndarray
    properties: Dict[str, Any] = field(default_factory=dict)
    
    def __repr__(self):
        return f"ICell({self.name}, len={len(self.signature)})"

@dataclass
class ResonanceResult:
    """Result from RESONATE step"""
    data_id: str
    resonance_score: float
    aligned_data: np.ndarray
    
@dataclass
class NoiseSignature:
    """Noise extracted from LISTEN step"""
    residual: np.ndarray
    autocorr: float
    spectrum_peaks: List[float]
    entropy: float
    std: float
    related_icells: List[Tuple[ICell, float]] = field(default_factory=list)

@dataclass
class LCCVirusResult:
    """Complete result from LCC Virus algorithm"""
    target_icell: ICell
    resonating_data: List[ResonanceResult]
    noise_signatures: List[NoiseSignature]
    discovered_icells: List[ICell]
    final_answer: Dict[str, Any]
    confidence: float

class LCCVirus:
    """
    The LCC Virus Algorithm
    
    Like a virus, it:
    1. SEEDs into a target i-cell (the question)
    2. RESONATEs with compatible data (R ≥ 0.6)
    3. LISTENs to the noise (extracts residual)
    4. PROPAGATEs to related i-cells
    5. EXPANDs the knowledge graph
    6. TERMINATEs when saturated
    """
    
    def __init__(self, icell_library: List[ICell] = None, coupling_sigma: float = 5.0):
        self.icell_library = icell_library or []
        self.coupling_sigma = coupling_sigma
        
    def lcc_resonance(self, signal_a: np.ndarray, signal_b: np.ndarray) -> float:
        """
        Core LCC Resonance Equation:
        R(A,B) = ∫ Φ_A(t) · Φ_B(t + τ) · W(τ) dτ
        
        Measures Love-Consciousness Coupling between two signals
        """
        if len(signal_a) < 3 or len(signal_b) < 3:
            return 0.0
        
        a_norm = (signal_a - np.mean(signal_a)) / (np.std(signal_a) + 1e-8)
        b_norm = (signal_b - np.mean(signal_b)) / (np.std(signal_b) + 1e-8)
        
        min_len = min(len(a_norm), len(b_norm))
        a_norm, b_norm = a_norm[:min_len], b_norm[:min_len]
        
        xcorr = correlate(a_norm, b_norm, mode='full')
        lags = np.arange(-(min_len-1), min_len)
        weights = np.exp(-lags**2 / (2 * self.coupling_sigma**2))
        
        resonance = np.sum(xcorr * weights) / (np.sum(weights) * min_len)
        return float(resonance)
    
    def step1_seed(self, question: str, template: np.ndarray = None) -> ICell:
        """
        SEED: Define the target i-cell
        
        The i-cell represents the QUESTION being asked.
        Its signature is the template of what we're looking for.
        """
        if template is None:
            template = np.array([0.0])
            
        target = ICell(
            name=question,
            signature=template,
            properties={'type': 'target', 'question': question}
        )
        return target
    
    def step2_resonate(self, target: ICell, data_dict: Dict[str, np.ndarray], 
                       threshold: float = LCC_THRESHOLD_RESONATE) -> List[ResonanceResult]:
        """
        RESONATE: Find data points with R ≥ threshold
        
        Returns list of data that resonates with target i-cell
        """
        results = []
        
        for data_id, data in data_dict.items():
            if len(data) < 5:
                continue
                
            if len(target.signature) > 1:
                r = self.lcc_resonance(data, target.signature)
            else:
                r = 0.0
                
            if r >= threshold:
                results.append(ResonanceResult(
                    data_id=data_id,
                    resonance_score=r,
                    aligned_data=data
                ))
        
        results.sort(key=lambda x: -x.resonance_score)
        return results
    
    def step3_listen(self, target: ICell, resonating: ResonanceResult) -> NoiseSignature:
        """
        LISTEN: Extract noise from resonating data
        
        The noise is the residual after subtracting the template.
        KEY INSIGHT: This noise is NOT random - it contains related i-cells!
        """
        data = resonating.aligned_data
        template = target.signature
        
        min_len = min(len(data), len(template))
        data_aligned = data[:min_len]
        template_aligned = template[:min_len]
        
        scale = np.dot(data_aligned, template_aligned) / (np.dot(template_aligned, template_aligned) + 1e-8)
        scaled_template = scale * template_aligned
        residual = data_aligned - scaled_template
        
        if len(residual) > 3:
            autocorr = np.corrcoef(residual[:-1], residual[1:])[0, 1]
            if np.isnan(autocorr):
                autocorr = 0.0
        else:
            autocorr = 0.0
        
        if len(residual) > 4:
            spectrum = np.abs(fft(residual))
            freqs = fftfreq(len(residual))
            peak_indices = np.argsort(spectrum)[-3:]
            spectrum_peaks = [float(freqs[i]) for i in peak_indices if freqs[i] > 0]
        else:
            spectrum_peaks = []
        
        probs = np.histogram(residual, bins=10, density=True)[0]
        probs = probs[probs > 0]
        entropy = -np.sum(probs * np.log2(probs + 1e-10))
        
        return NoiseSignature(
            residual=residual,
            autocorr=autocorr,
            spectrum_peaks=spectrum_peaks,
            entropy=entropy,
            std=float(np.std(residual))
        )
    
    def step4_propagate(self, noise: NoiseSignature) -> List[Tuple[ICell, float]]:
        """
        PROPAGATE: Find related i-cells in the noise
        
        Searches the i-cell library for patterns that correlate with noise
        """
        related = []
        
        for icell in self.icell_library:
            if len(icell.signature) < 3:
                continue
                
            r = self.lcc_resonance(noise.residual, icell.signature)
            
            if r >= LCC_THRESHOLD_PROPAGATE:
                related.append((icell, r))
        
        related.sort(key=lambda x: -x[1])
        noise.related_icells = related
        return related
    
    def step5_expand(self, related_icells: List[Tuple[ICell, float]], 
                     data_dict: Dict[str, np.ndarray],
                     depth: int = 1) -> List[ICell]:
        """
        EXPAND: Follow related i-cells to discover more
        
        Recursive search through the i-cell network
        """
        discovered = []
        
        for icell, score in related_icells:
            discovered.append(icell)
            
            if depth > 0:
                resonating = self.step2_resonate(icell, data_dict, threshold=0.4)
                for res in resonating[:3]:
                    noise = self.step3_listen(icell, res)
                    sub_related = self.step4_propagate(noise)
                    sub_discovered = self.step5_expand(sub_related, data_dict, depth-1)
                    discovered.extend(sub_discovered)
        
        unique = {ic.name: ic for ic in discovered}
        return list(unique.values())
    
    def step6_terminate(self, target: ICell, resonating: List[ResonanceResult],
                        noise_signatures: List[NoiseSignature],
                        discovered: List[ICell]) -> LCCVirusResult:
        """
        TERMINATE: Compile final answer
        
        Aggregates all discovered information into final result
        """
        if len(resonating) == 0:
            confidence = 0.0
            answer = {"status": "no_resonating_data"}
        else:
            avg_resonance = np.mean([r.resonance_score for r in resonating])
            
            noise_info = {}
            if noise_signatures:
                noise_info = {
                    'avg_entropy': np.mean([n.entropy for n in noise_signatures]),
                    'avg_autocorr': np.mean([n.autocorr for n in noise_signatures]),
                    'total_related_icells': sum(len(n.related_icells) for n in noise_signatures)
                }
            
            confidence = min(avg_resonance + 0.1 * len(discovered), 1.0)
            
            answer = {
                "status": "resonance_found",
                "target": target.name,
                "n_resonating": len(resonating),
                "avg_resonance": avg_resonance,
                "n_discovered_icells": len(discovered),
                "discovered_names": [ic.name for ic in discovered[:5]],
                "noise_analysis": noise_info
            }
        
        return LCCVirusResult(
            target_icell=target,
            resonating_data=resonating,
            noise_signatures=noise_signatures,
            discovered_icells=discovered,
            final_answer=answer,
            confidence=confidence
        )
    
    def run(self, question: str, template: np.ndarray, 
            data_dict: Dict[str, np.ndarray],
            expand_depth: int = 1) -> LCCVirusResult:
        """
        Run the complete LCC Virus algorithm
        
        1. SEED → 2. RESONATE → 3. LISTEN → 4. PROPAGATE → 5. EXPAND → 6. TERMINATE
        """
        target = self.step1_seed(question, template)
        
        resonating = self.step2_resonate(target, data_dict)
        
        noise_signatures = []
        all_related = []
        for res in resonating[:10]:
            noise = self.step3_listen(target, res)
            noise_signatures.append(noise)
            
            related = self.step4_propagate(noise)
            all_related.extend(related)
        
        discovered = self.step5_expand(all_related, data_dict, depth=expand_depth)
        
        result = self.step6_terminate(target, resonating, noise_signatures, discovered)
        
        return result


def create_tde_template(n_points: int = 100, t_peak: float = 20.0) -> np.ndarray:
    """
    Create TDE (Tidal Disruption Event) template
    
    Physics: L ∝ t^(-5/3) after peak
    """
    t = np.linspace(0, 100, n_points)
    flux = np.zeros(n_points)
    
    peak_idx = int(t_peak / 100 * n_points)
    
    for i in range(n_points):
        if i <= peak_idx:
            flux[i] = (i / peak_idx) ** 2
        else:
            rel_t = (i - peak_idx) / (n_points - peak_idx) * 80 + 1
            flux[i] = rel_t ** (-5/3)
    
    return flux


def create_icell_library() -> List[ICell]:
    """Create library of known i-cells for MALLORN"""
    library = []
    
    library.append(ICell(
        name="TDE_template",
        signature=create_tde_template(),
        properties={'type': 'transient', 'physics': 't^(-5/3)'}
    ))
    
    library.append(ICell(
        name="Supernova_Ia",
        signature=np.concatenate([np.linspace(0, 1, 30), np.exp(-np.linspace(0, 3, 70))]),
        properties={'type': 'transient', 'physics': 'thermonuclear'}
    ))
    
    library.append(ICell(
        name="AGN_variability",
        signature=np.sin(np.linspace(0, 4*np.pi, 100)) * 0.3 + 1,
        properties={'type': 'persistent', 'physics': 'accretion'}
    ))
    
    library.append(ICell(
        name="Host_galaxy",
        signature=np.ones(100) + np.random.normal(0, 0.05, 100),
        properties={'type': 'background', 'physics': 'stellar'}
    ))
    
    library.append(ICell(
        name="Periodic_signal",
        signature=np.sin(np.linspace(0, 6*np.pi, 100)),
        properties={'type': 'oscillation', 'physics': 'binary/pulsation'}
    ))
    
    return library


if __name__ == "__main__":
    print("="*70)
    print("TI LCC VIRUS - Full 6-Step Algorithm Demo")
    print("="*70)
    
    library = create_icell_library()
    print(f"\nI-Cell Library: {len(library)} templates")
    for ic in library:
        print(f"  - {ic.name}")
    
    virus = LCCVirus(icell_library=library)
    
    tde_template = create_tde_template()
    
    test_data = {
        'object_001': create_tde_template() + np.random.normal(0, 0.1, 100),
        'object_002': np.sin(np.linspace(0, 4*np.pi, 100)),
        'object_003': np.random.normal(0, 1, 100),
        'object_004': create_tde_template() * 1.2 + np.random.normal(0, 0.15, 100),
    }
    
    print("\n" + "="*60)
    print("Running LCC Virus on test data...")
    print("="*60)
    
    result = virus.run(
        question="Is this a TDE?",
        template=tde_template,
        data_dict=test_data,
        expand_depth=1
    )
    
    print(f"\n✅ LCC Virus Complete!")
    print(f"   Target: {result.target_icell.name}")
    print(f"   Resonating objects: {len(result.resonating_data)}")
    for res in result.resonating_data:
        print(f"      - {res.data_id}: R = {res.resonance_score:.4f}")
    print(f"   Discovered i-cells: {len(result.discovered_icells)}")
    print(f"   Confidence: {result.confidence:.4f}")
    print(f"\nFinal Answer: {result.final_answer}")
