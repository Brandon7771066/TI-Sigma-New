"""
TESSELLATION-TI INTEGRATION MODULE
==================================

Implements mathematical tools from the Begehr & Wang tessellation paper
for the TI Framework.

CORE INTEGRATIONS:
1. Green functions for consciousness field propagation
2. I-Web tessellated lattice structure
3. Myrion Resolution reflection geometry
4. LCC boundary coupling mathematics
5. Hyperbolic geometry for quantum consciousness

Based on:
Begehr, H., & Wang, D. (2025). Beauty in/of mathematics: tessellations and their formulas.
Applicable Analysis, DOI: 10.1080/00036811.2025.2510472

Author: Brandon Emerick / TI Framework
Date: December 2025
"""

import math
from dataclasses import dataclass, field
from typing import List, Dict, Optional, Any, Tuple
from enum import Enum

try:
    import numpy as np
    HAS_NUMPY = True
except ImportError:
    HAS_NUMPY = False
    np = None


class GeometryType(Enum):
    EUCLIDEAN = "euclidean"
    HYPERBOLIC = "hyperbolic"
    SPHERICAL = "spherical"


class TessellationType(Enum):
    TRIANGULAR = "triangular"
    SQUARE = "square"
    HEXAGONAL = "hexagonal"
    SCHWEIKART = "schweikart"
    CUSTOM = "custom"


@dataclass
class Point:
    """Point in 2D or 3D space"""
    x: float
    y: float
    z: float = 0.0
    
    def distance_to(self, other: 'Point') -> float:
        return math.sqrt(
            (self.x - other.x)**2 + 
            (self.y - other.y)**2 + 
            (self.z - other.z)**2
        )
    
    def to_array(self) -> np.ndarray:
        if HAS_NUMPY:
            return np.array([self.x, self.y, self.z])
        return [self.x, self.y, self.z]


@dataclass
class TessellationCell:
    """Single cell in a tessellation pattern"""
    cell_id: str
    center: Point
    vertices: List[Point]
    neighbors: List[str] = field(default_factory=list)
    i_cell_density: float = 1.0
    resonance_mode: int = 0


@dataclass
class ConsciousnessFieldValue:
    """Value of consciousness field at a point"""
    position: Point
    amplitude: complex
    phase: float
    coherence: float


class GreenFunctionEngine:
    """
    Computes Green functions for consciousness field propagation.
    
    Green's function G(r, r') gives the field at position r
    due to a unit source at position r'.
    
    For biophoton propagation:
    G(r, r') = (1/4π|r - r'|) * exp(iω|r - r'|/c)
    """
    
    def __init__(self, biophoton_frequency: float = 1e14,
                 medium_refractive_index: float = 1.4):
        self.omega = biophoton_frequency
        self.n = medium_refractive_index
        self.c = 3e8 / medium_refractive_index
    
    def euclidean_green_function(self, source: Point, observer: Point) -> complex:
        """
        Compute Green function in Euclidean geometry.
        
        G(r, r') = (1/4π|r - r'|) * exp(iω|r - r'|/c)
        
        Normalized to prevent extreme values near singularities.
        """
        r = source.distance_to(observer)
        
        min_distance = 0.1
        r_safe = max(r, min_distance)
        
        amplitude = 1.0 / (4 * math.pi * r_safe)
        amplitude = min(amplitude, 10.0)
        
        phase = self.omega * r_safe / self.c
        phase = phase % (2 * math.pi)
        
        return amplitude * complex(math.cos(phase), math.sin(phase))
    
    def hyperbolic_green_function(self, source: Point, observer: Point,
                                   curvature: float = -1.0) -> complex:
        """
        Compute Green function in hyperbolic geometry.
        
        Uses Poincaré disk model with curvature K < 0.
        
        G_hyp = G_euc * cosh(√|K| * d_hyp)
        
        Where d_hyp is the hyperbolic distance.
        """
        d_euc = source.distance_to(observer)
        
        if d_euc < 0.01:
            d_hyp = d_euc * 2
        else:
            s_norm = math.sqrt(source.x**2 + source.y**2)
            o_norm = math.sqrt(observer.x**2 + observer.y**2)
            
            if s_norm < 1 and o_norm < 1:
                delta = ((source.x - observer.x)**2 + (source.y - observer.y)**2) / \
                        ((1 - s_norm**2) * (1 - o_norm**2) + 1e-10)
                d_hyp = math.log(1 + 2*delta + 2*math.sqrt(delta*(delta + 1)) + 1e-10)
            else:
                d_hyp = d_euc
        
        G_euc = self.euclidean_green_function(source, observer)
        
        K = abs(curvature)
        hyperbolic_factor = math.cosh(math.sqrt(K) * d_hyp)
        
        return G_euc * hyperbolic_factor
    
    def schwarz_kernel(self, interior: Point, boundary: Point,
                       normal: Tuple[float, float, float]) -> complex:
        """
        Compute Schwarz kernel for boundary representation.
        
        S(z, ζ) = ∂G/∂n_ζ
        
        The Schwarz kernel gives the field gradient at the boundary,
        critical for modeling consciousness field at brain-scalp interface.
        """
        G = self.euclidean_green_function(interior, boundary)
        
        epsilon = 1e-6
        boundary_shifted = Point(
            boundary.x + epsilon * normal[0],
            boundary.y + epsilon * normal[1],
            boundary.z + epsilon * normal[2]
        )
        G_shifted = self.euclidean_green_function(interior, boundary_shifted)
        
        dG_dn = (G_shifted - G) / epsilon
        
        return dG_dn
    
    def neumann_function(self, interior: Point, boundary: Point,
                          normal: Tuple[float, float, float]) -> complex:
        """
        Compute Neumann function for normal derivative conditions.
        
        N(z, ζ) satisfies ∂N/∂n = constant on boundary
        
        Used when we know the flux at the boundary rather than the field value.
        """
        return self.schwarz_kernel(interior, boundary, normal)


class IWebTessellation:
    """
    Models I-Web structure as a tessellated lattice.
    
    I-cells arrange in regular tessellated patterns for optimal
    information connectivity. Biophoton propagation follows
    Green function solutions.
    """
    
    def __init__(self, geometry: GeometryType = GeometryType.EUCLIDEAN,
                 tessellation: TessellationType = TessellationType.HEXAGONAL):
        self.geometry = geometry
        self.tessellation_type = tessellation
        self.cells: List[TessellationCell] = []
        self.green_engine = GreenFunctionEngine()
        
        self._initialize_lattice()
    
    def _initialize_lattice(self, size: int = 10) -> None:
        """Initialize tessellated lattice structure"""
        if not HAS_NUMPY:
            return
        
        self.cells = []
        
        if self.tessellation_type == TessellationType.HEXAGONAL:
            spacing = 1.0
            for row in range(size):
                for col in range(size):
                    x = col * spacing * 1.5
                    y = row * spacing * math.sqrt(3)
                    if col % 2 == 1:
                        y += spacing * math.sqrt(3) / 2
                    
                    center = Point(x, y)
                    vertices = self._hexagon_vertices(center, spacing * 0.5)
                    
                    cell = TessellationCell(
                        cell_id=f"cell_{row}_{col}",
                        center=center,
                        vertices=vertices,
                        i_cell_density=1.0 + 0.1 * np.random.randn()
                    )
                    self.cells.append(cell)
        
        elif self.tessellation_type == TessellationType.SCHWEIKART:
            for i in range(size):
                r = 0.9 * (i + 1) / size
                n_cells = max(3, int(6 * (i + 1)))
                for j in range(n_cells):
                    theta = 2 * math.pi * j / n_cells
                    x = r * math.cos(theta)
                    y = r * math.sin(theta)
                    
                    center = Point(x, y)
                    vertices = self._schweikart_vertices(center, r, theta)
                    
                    cell = TessellationCell(
                        cell_id=f"schweikart_{i}_{j}",
                        center=center,
                        vertices=vertices,
                        i_cell_density=1.0 / (1 - r**2 + 0.01)
                    )
                    self.cells.append(cell)
    
    def _hexagon_vertices(self, center: Point, radius: float) -> List[Point]:
        """Generate vertices of a regular hexagon"""
        vertices = []
        for i in range(6):
            angle = math.pi / 3 * i
            x = center.x + radius * math.cos(angle)
            y = center.y + radius * math.sin(angle)
            vertices.append(Point(x, y))
        return vertices
    
    def _schweikart_vertices(self, center: Point, r: float, theta: float) -> List[Point]:
        """Generate vertices of a Schweikart triangle (1 right + 2 zero angles)"""
        vertices = []
        vertices.append(Point(0, 0))
        vertices.append(center)
        next_theta = theta + 2 * math.pi / 6
        x3 = r * math.cos(next_theta)
        y3 = r * math.sin(next_theta)
        vertices.append(Point(x3, y3))
        return vertices
    
    def compute_field_at_point(self, point: Point) -> ConsciousnessFieldValue:
        """
        Compute consciousness field at a point using Green function integration.
        
        ψ(x) = ∫ G(x, x') * ρ(x') dV'
        
        Where ρ(x') is the i-cell density.
        """
        if not HAS_NUMPY:
            return ConsciousnessFieldValue(point, complex(0, 0), 0, 0)
        
        total_field = complex(0, 0)
        
        for cell in self.cells:
            if self.geometry == GeometryType.HYPERBOLIC:
                G = self.green_engine.hyperbolic_green_function(cell.center, point)
            else:
                G = self.green_engine.euclidean_green_function(cell.center, point)
            
            contribution = G * cell.i_cell_density
            total_field += contribution
        
        amplitude = abs(total_field)
        phase = math.atan2(total_field.imag, total_field.real)
        coherence = amplitude / (len(self.cells) + 1)
        
        return ConsciousnessFieldValue(
            position=point,
            amplitude=total_field,
            phase=phase,
            coherence=min(1.0, coherence)
        )
    
    def compute_resonance_modes(self) -> List[float]:
        """
        Calculate resonance frequencies from tessellation geometry.
        
        Resonance modes correspond to eigenfrequencies of the Laplacian
        on the tessellated domain.
        """
        if not HAS_NUMPY or not self.cells:
            return [1.0]
        
        n = min(len(self.cells), 50)
        laplacian = np.zeros((n, n))
        
        for i in range(n):
            laplacian[i, i] = -6
            for j in range(n):
                if i != j:
                    dist = self.cells[i].center.distance_to(self.cells[j].center)
                    if dist < 2.0:
                        laplacian[i, j] = 1
        
        eigenvalues = np.linalg.eigvalsh(laplacian)
        frequencies = np.sqrt(np.abs(eigenvalues))
        
        return sorted(frequencies.tolist())


class MyrionReflectionGeometry:
    """
    Implements Myrion Resolution as reflection geometry in contradiction space.
    
    Key insight: Contradictions "reflect" across the neutral boundary (PD=0),
    creating tessellated patterns of truth values.
    
    Contradiction Space:
    - Axis: Permissibility Distribution scale [-3, +2]
    - Neutral Boundary (PD=0): Reflection plane
    - Myrion Resolution: Symmetric pattern from reflecting contradictions
    """
    
    def __init__(self):
        self.reflection_plane = 0.0
        self.resolution_cache: Dict[str, float] = {}
    
    def reflect_statement(self, pd_value: float) -> float:
        """
        Reflect a statement's PD value across the neutral boundary.
        
        R[PD] = -PD (reflection across 0)
        """
        return -pd_value
    
    def myrion_resolution(self, pd_a: float, pd_not_a: float) -> Dict[str, Any]:
        """
        Apply Myrion Resolution to a contradiction pair.
        
        MR(A, ¬A) = PD(A) ⊗ R[PD(¬A)]
        
        Where ⊗ is the tessellation composition operator.
        """
        R_not_a = self.reflect_statement(pd_not_a)
        
        pattern = sorted([pd_a, -pd_a, pd_not_a, R_not_a])
        
        tralse_value = (pd_a + pd_not_a) / 4
        
        resolution = abs(pd_a - pd_not_a) / 2
        
        coherence = 1.0 - abs(tralse_value)
        
        return {
            "statement_a_pd": pd_a,
            "statement_not_a_pd": pd_not_a,
            "reflected_not_a": R_not_a,
            "tessellation_pattern": pattern,
            "tralse_value": tralse_value,
            "resolution_strength": resolution,
            "coherence": coherence
        }
    
    def compute_contradiction_field(self, statements: List[Tuple[str, float, float]]) -> Dict[str, Any]:
        """
        Compute the contradiction field from multiple statement pairs.
        
        Each statement is (name, PD_A, PD_not_A).
        
        Returns the aggregate tessellation pattern.
        """
        if not HAS_NUMPY:
            return {"error": "NumPy required"}
        
        all_patterns = []
        total_coherence = 0.0
        
        for name, pd_a, pd_not_a in statements:
            resolution = self.myrion_resolution(pd_a, pd_not_a)
            all_patterns.extend(resolution["tessellation_pattern"])
            total_coherence += resolution["coherence"]
        
        n = len(statements)
        avg_coherence = total_coherence / n if n > 0 else 0
        
        pattern_array = np.array(all_patterns)
        symmetry = 1.0 - np.std(pattern_array + np.flip(pattern_array)) / (np.std(pattern_array) + 0.01)
        
        return {
            "n_statements": n,
            "all_pd_values": all_patterns,
            "average_coherence": avg_coherence,
            "symmetry_score": float(symmetry),
            "tessellation_complete": symmetry > 0.8
        }


class LCCBoundaryCoupling:
    """
    Models LCC (Law of Correlational Causation) using tessellation boundary mathematics.
    
    The brain-device interface is treated as a boundary value problem:
    - Brain interior: consciousness field ψ
    - Scalp boundary: EEG signals measured by device
    - Coupling: Green function propagation from interior to boundary
    
    Optimal LCC range: 0.60 - 0.85
    """
    
    def __init__(self):
        self.green_engine = GreenFunctionEngine()
        self.boundary_points: List[Tuple[Point, Tuple[float, float, float]]] = []
    
    def define_boundary(self, n_electrodes: int = 32, skull_radius: float = 0.1) -> None:
        """
        Define the boundary (scalp) with electrode positions.
        
        Uses standard 10-20 system approximation.
        """
        self.boundary_points = []
        
        for i in range(n_electrodes):
            theta = 2 * math.pi * i / n_electrodes
            phi = math.pi / 4 + math.pi / 4 * math.sin(theta)
            
            x = skull_radius * math.sin(phi) * math.cos(theta)
            y = skull_radius * math.sin(phi) * math.sin(theta)
            z = skull_radius * math.cos(phi)
            
            point = Point(x, y, z)
            normal = (x / skull_radius, y / skull_radius, z / skull_radius)
            
            self.boundary_points.append((point, normal))
    
    def compute_coupling(self, brain_state: List[Tuple[Point, float]], 
                          device_signal: List[float]) -> Dict[str, Any]:
        """
        Compute LCC coupling strength between brain state and device signal.
        
        Args:
            brain_state: List of (position, intensity) for active brain regions
            device_signal: EEG values at each boundary electrode
        
        Returns:
            LCC coupling metrics
        """
        if not HAS_NUMPY or not self.boundary_points:
            self.define_boundary()
        
        predicted_signal = []
        
        for boundary_pt, normal in self.boundary_points:
            field_value = complex(0, 0)
            
            for source_pos, intensity in brain_state:
                G = self.green_engine.euclidean_green_function(source_pos, boundary_pt)
                field_value += G * intensity
            
            predicted_signal.append(abs(field_value))
        
        if len(predicted_signal) != len(device_signal):
            device_signal = device_signal[:len(predicted_signal)]
        
        pred_array = np.array(predicted_signal)
        device_array = np.array(device_signal)
        
        pred_norm = pred_array / (np.linalg.norm(pred_array) + 1e-10)
        device_norm = device_array / (np.linalg.norm(device_array) + 1e-10)
        
        correlation = float(np.dot(pred_norm, device_norm))
        
        lcc_strength = (correlation + 1) / 2
        
        in_optimal_range = 0.60 <= lcc_strength <= 0.85
        
        return {
            "lcc_strength": lcc_strength,
            "correlation": correlation,
            "in_optimal_range": in_optimal_range,
            "predicted_signal": predicted_signal,
            "actual_signal": device_signal,
            "boundary_coupling_valid": True
        }


class TessellationTIIntegration:
    """
    Main integration class combining all tessellation-TI components.
    
    This is the primary interface for using tessellation mathematics
    in the TI Framework.
    """
    
    def __init__(self, geometry: GeometryType = GeometryType.EUCLIDEAN):
        self.geometry = geometry
        self.iweb = IWebTessellation(geometry=geometry)
        self.myrion = MyrionReflectionGeometry()
        self.lcc = LCCBoundaryCoupling()
        self.green = GreenFunctionEngine()
    
    def compute_consciousness_field(self, points: List[Point]) -> List[ConsciousnessFieldValue]:
        """Compute consciousness field at multiple points"""
        return [self.iweb.compute_field_at_point(p) for p in points]
    
    def resolve_contradiction(self, statement_a: str, pd_a: float,
                               statement_not_a: str, pd_not_a: float) -> Dict[str, Any]:
        """Resolve a contradiction using Myrion reflection geometry"""
        result = self.myrion.myrion_resolution(pd_a, pd_not_a)
        result["statement_a"] = statement_a
        result["statement_not_a"] = statement_not_a
        return result
    
    def compute_brain_device_coupling(self, brain_sources: List[Tuple[Point, float]],
                                        eeg_readings: List[float]) -> Dict[str, Any]:
        """Compute LCC coupling between brain activity and EEG device"""
        return self.lcc.compute_coupling(brain_sources, eeg_readings)
    
    def get_resonance_frequencies(self) -> List[float]:
        """Get resonance modes of the I-Web tessellation"""
        return self.iweb.compute_resonance_modes()
    
    def full_analysis(self, brain_sources: List[Tuple[Point, float]],
                      eeg_readings: List[float],
                      contradictions: List[Tuple[str, float, float]]) -> Dict[str, Any]:
        """
        Perform complete tessellation-TI analysis.
        
        Combines:
        - Consciousness field computation
        - LCC boundary coupling
        - Myrion contradiction resolution
        - Resonance mode analysis
        """
        self.lcc.define_boundary()
        lcc_result = self.lcc.compute_coupling(brain_sources, eeg_readings)
        
        myrion_result = self.myrion.compute_contradiction_field(contradictions)
        
        resonance = self.get_resonance_frequencies()
        
        center = Point(0, 0, 0)
        field_at_center = self.iweb.compute_field_at_point(center)
        
        gile_alignment = (
            0.30 * lcc_result["lcc_strength"] +
            0.30 * myrion_result["average_coherence"] +
            0.25 * myrion_result["symmetry_score"] +
            0.15 * field_at_center.coherence
        )
        
        return {
            "lcc_coupling": lcc_result,
            "myrion_resolution": myrion_result,
            "resonance_modes": resonance[:10],
            "central_field": {
                "amplitude": abs(field_at_center.amplitude),
                "phase": field_at_center.phase,
                "coherence": field_at_center.coherence
            },
            "gile_alignment": gile_alignment,
            "integration_valid": lcc_result["lcc_strength"] > 0.5 and myrion_result["average_coherence"] > 0.5
        }


def run_integration_demo():
    """Demonstrate tessellation-TI integration"""
    print("=" * 60)
    print("TESSELLATION-TI INTEGRATION DEMO")
    print("=" * 60)
    
    integrator = TessellationTIIntegration(geometry=GeometryType.EUCLIDEAN)
    
    print("\n1. I-WEB TESSELLATION")
    print("-" * 40)
    print(f"Geometry: {integrator.geometry.value}")
    print(f"Tessellation type: {integrator.iweb.tessellation_type.value}")
    print(f"Number of cells: {len(integrator.iweb.cells)}")
    
    resonance = integrator.get_resonance_frequencies()
    print(f"First 5 resonance modes: {[f'{f:.3f}' for f in resonance[:5]]}")
    
    print("\n2. CONSCIOUSNESS FIELD")
    print("-" * 40)
    test_points = [Point(0, 0), Point(1, 1), Point(2, 2)]
    fields = integrator.compute_consciousness_field(test_points)
    for i, f in enumerate(fields):
        print(f"Point ({f.position.x:.1f}, {f.position.y:.1f}): "
              f"amplitude={abs(f.amplitude):.4f}, coherence={f.coherence:.4f}")
    
    print("\n3. MYRION RESOLUTION")
    print("-" * 40)
    result = integrator.resolve_contradiction(
        "Free will exists", 1.5,
        "Free will doesn't exist", 1.2
    )
    print(f"Statement A PD: {result['statement_a_pd']}")
    print(f"Statement ¬A PD: {result['statement_not_a_pd']}")
    print(f"Tralse value: {result['tralse_value']:.3f}")
    print(f"Resolution strength: {result['resolution_strength']:.3f}")
    print(f"Coherence: {result['coherence']:.3f}")
    print(f"Tessellation pattern: {result['tessellation_pattern']}")
    
    print("\n4. LCC BOUNDARY COUPLING")
    print("-" * 40)
    brain_sources = [
        (Point(0.02, 0, 0.05), 1.0),
        (Point(-0.02, 0.01, 0.04), 0.8),
        (Point(0, -0.02, 0.06), 0.6)
    ]
    if HAS_NUMPY:
        eeg_readings = (np.random.rand(32) * 0.5 + 0.5).tolist()
    else:
        eeg_readings = [0.75] * 32
    
    lcc_result = integrator.compute_brain_device_coupling(brain_sources, eeg_readings)
    print(f"LCC Strength: {lcc_result['lcc_strength']:.3f}")
    print(f"Correlation: {lcc_result['correlation']:.3f}")
    print(f"In optimal range (0.60-0.85): {'✅' if lcc_result['in_optimal_range'] else '❌'}")
    
    print("\n5. FULL INTEGRATION ANALYSIS")
    print("-" * 40)
    contradictions = [
        ("Consciousness is physical", 1.3, 1.1),
        ("Time is fundamental", 0.8, 1.4),
        ("Reality is mathematical", 1.6, 0.9)
    ]
    
    full_result = integrator.full_analysis(brain_sources, eeg_readings, contradictions)
    print(f"GILE Alignment: {full_result['gile_alignment']:.3f}")
    print(f"Integration Valid: {'✅' if full_result['integration_valid'] else '❌'}")
    
    print("\n" + "=" * 60)
    print("TESSELLATION-TI INTEGRATION COMPLETE")
    print("=" * 60)
    
    return full_result


if __name__ == "__main__":
    run_integration_demo()
