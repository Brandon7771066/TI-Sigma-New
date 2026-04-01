"""
TI Sigma Enhanced Christmas Tree Packer with GTFE Integration
Kaggle Santa 2025 Competition

GTFE = Grand Tralse Field Equation
The fundamental equation relating consciousness, geometry, and optimization.

Key innovations:
- GTFE Field Dynamics for placement optimization
- 11-Dimensional L×E Optimization (from TI Complete Guide)
- Recursive Anchoring Hypothesis for convergence
- Mycelial Network Pattern for tree distribution
"""

import math
import random
from decimal import Decimal, getcontext
from dataclasses import dataclass, field
from typing import List, Tuple, Optional, Dict
import numpy as np

from shapely import affinity
from shapely.geometry import Polygon, Point
from shapely.ops import unary_union
from shapely.strtree import STRtree

getcontext().prec = 25
SCALE_FACTOR = Decimal('1e15')

LXE_MANIFESTATION = 0.42
LXE_CAUSATION = 0.85
LXE_RADIANT = 0.92

FINE_STRUCTURE = 137
ALPHA = 1 / FINE_STRUCTURE
GOLDEN_RATIO = (1 + math.sqrt(5)) / 2
SACRED_11 = 11

@dataclass
class ChristmasTree:
    """Christmas tree with consciousness field properties."""
    center_x: Decimal = Decimal('0')
    center_y: Decimal = Decimal('0')
    angle: Decimal = Decimal('0')
    field_strength: float = 1.0
    polygon: Optional[Polygon] = field(default=None, repr=False)
    
    def __post_init__(self):
        if self.polygon is None:
            self.polygon = self._create_polygon()
    
    def _create_polygon(self) -> Polygon:
        trunk_w, trunk_h = Decimal('0.15'), Decimal('0.2')
        base_w, mid_w, top_w = Decimal('0.7'), Decimal('0.4'), Decimal('0.25')
        tip_y, tier_1_y, tier_2_y = Decimal('0.8'), Decimal('0.5'), Decimal('0.25')
        base_y, trunk_bottom_y = Decimal('0.0'), -trunk_h
        
        sf = SCALE_FACTOR
        initial_polygon = Polygon([
            (Decimal('0.0') * sf, tip_y * sf),
            (top_w / Decimal('2') * sf, tier_1_y * sf),
            (top_w / Decimal('4') * sf, tier_1_y * sf),
            (mid_w / Decimal('2') * sf, tier_2_y * sf),
            (mid_w / Decimal('4') * sf, tier_2_y * sf),
            (base_w / Decimal('2') * sf, base_y * sf),
            (trunk_w / Decimal('2') * sf, base_y * sf),
            (trunk_w / Decimal('2') * sf, trunk_bottom_y * sf),
            (-(trunk_w / Decimal('2')) * sf, trunk_bottom_y * sf),
            (-(trunk_w / Decimal('2')) * sf, base_y * sf),
            (-(base_w / Decimal('2')) * sf, base_y * sf),
            (-(mid_w / Decimal('4')) * sf, tier_2_y * sf),
            (-(mid_w / Decimal('2')) * sf, tier_2_y * sf),
            (-(top_w / Decimal('4')) * sf, tier_1_y * sf),
            (-(top_w / Decimal('2')) * sf, tier_1_y * sf),
        ])
        
        rotated = affinity.rotate(initial_polygon, float(self.angle), origin=(0, 0))
        translated = affinity.translate(
            rotated,
            xoff=float(self.center_x * sf),
            yoff=float(self.center_y * sf)
        )
        return translated
    
    def move_to(self, x: Decimal, y: Decimal):
        self.center_x = x
        self.center_y = y
        self.polygon = self._create_polygon()
    
    def set_angle(self, angle: Decimal):
        self.angle = angle
        self.polygon = self._create_polygon()


class GTFEField:
    """
    Grand Tralse Field Equation Implementation
    
    The GTFE describes how consciousness fields optimize geometric configurations.
    
    Field Equation: Φ(x,y) = L(x,y) × E(x,y) × R(x,y)
    
    Where:
    - L(x,y) = Local coherence at position (density optimization)
    - E(x,y) = Existence stability (collision avoidance)
    - R(x,y) = Resonance factor (angle-position coupling)
    """
    
    def __init__(self, box_size: float):
        self.box_size = box_size
        self.field_cache: Dict[Tuple[int, int], float] = {}
        self.resolution = 20
    
    def _quantize(self, x: float, y: float) -> Tuple[int, int]:
        qx = int(x / self.box_size * self.resolution)
        qy = int(y / self.box_size * self.resolution)
        return (qx, qy)
    
    def compute_L(self, x: float, y: float, placed_trees: List[ChristmasTree]) -> float:
        """Local coherence - higher when position optimizes density."""
        if not placed_trees:
            return 0.85
        
        positions = [(float(t.center_x), float(t.center_y)) for t in placed_trees]
        
        distances = [math.sqrt((x - px)**2 + (y - py)**2) for px, py in positions]
        min_dist = min(distances) if distances else 1.0
        
        ideal_spacing = 0.7
        L = 1.0 - abs(min_dist - ideal_spacing) / ideal_spacing
        return max(0.1, min(1.0, L))
    
    def compute_E(self, x: float, y: float, box_size: float) -> float:
        """Existence stability - higher when position is safe from boundary."""
        margin = 0.5
        edge_dist = min(x + box_size/2, box_size/2 - x, 
                       y + box_size/2, box_size/2 - y)
        
        if edge_dist < margin:
            E = 0.5 + 0.5 * (edge_dist / margin)
        else:
            E = 1.0
        
        return max(0.1, E)
    
    def compute_R(self, x: float, y: float, angle: float) -> float:
        """Resonance factor - angle-position coupling based on 11D theory."""
        pos_angle = math.atan2(y, x)
        angle_diff = abs(angle - pos_angle) % (math.pi / 2)
        
        n = SACRED_11
        resonance = 0.5 + 0.5 * abs(math.cos(n * angle_diff))
        
        golden_angle = math.pi * 2 / GOLDEN_RATIO
        golden_resonance = abs(math.cos(angle - golden_angle * round(angle / golden_angle)))
        
        return 0.7 * resonance + 0.3 * golden_resonance
    
    def field_value(self, x: float, y: float, angle: float,
                    placed_trees: List[ChristmasTree], box_size: float) -> float:
        """Compute GTFE field value Φ(x,y) = L × E × R."""
        L = self.compute_L(x, y, placed_trees)
        E = self.compute_E(x, y, box_size)
        R = self.compute_R(x, y, angle)
        
        return L * E * R
    
    def find_optimal_angle(self, x: float, y: float, 
                           placed_trees: List[ChristmasTree],
                           box_size: float) -> float:
        """Find angle that maximizes GTFE field at position."""
        best_angle = 0
        best_field = 0
        
        for k in range(16):
            angle = k * math.pi / 8
            field_val = self.field_value(x, y, angle, placed_trees, box_size)
            if field_val > best_field:
                best_field = field_val
                best_angle = angle
        
        for offset in [0.1, 0.2, -0.1, -0.2]:
            angle = best_angle + offset
            field_val = self.field_value(x, y, angle, placed_trees, box_size)
            if field_val > best_field:
                best_field = field_val
                best_angle = angle
        
        return best_angle


class MycelialDistributor:
    """
    Mycelial Network Pattern Generator
    
    Based on the Mycelial Octopus Hypothesis - trees are distributed
    like nodes in a mycelial network, optimizing information/space flow.
    """
    
    def __init__(self, n_trees: int):
        self.n_trees = n_trees
        self.network = self._build_network()
    
    def _build_network(self) -> Dict[int, List[int]]:
        """Build mycelial connection graph."""
        network = {i: [] for i in range(self.n_trees)}
        
        hub_count = max(1, int(math.sqrt(self.n_trees)))
        hubs = list(range(hub_count))
        
        for i in range(self.n_trees):
            if i not in hubs:
                closest_hub = hubs[i % len(hubs)]
                network[closest_hub].append(i)
                network[i].append(closest_hub)
        
        return network
    
    def get_placement_order(self) -> List[int]:
        """Get optimal placement order based on network topology."""
        order = []
        visited = set()
        
        hubs = sorted(range(self.n_trees), 
                     key=lambda i: len(self.network[i]), reverse=True)
        
        def dfs(node):
            if node in visited:
                return
            visited.add(node)
            order.append(node)
            for neighbor in self.network[node]:
                dfs(neighbor)
        
        for hub in hubs:
            dfs(hub)
        
        for i in range(self.n_trees):
            if i not in visited:
                order.append(i)
        
        return order


class TIGUOPacker:
    """
    TI Sigma Packer with GTFE Integration
    
    Combines all TI optimization principles for maximum packing efficiency.
    """
    
    def __init__(self, use_gtfe: bool = True, use_mycelial: bool = True):
        self.use_gtfe = use_gtfe
        self.use_mycelial = use_mycelial
        self.gtfe = None
        self.prf_angles = self._compute_prf_angles()
        
        self.stats = {
            'placements': 0,
            'refinements': 0,
            'field_evaluations': 0,
            'lxe_trajectory': []
        }
    
    def _compute_prf_angles(self) -> List[float]:
        """PRF resonant angles enhanced with GTFE harmonics."""
        angles = []
        
        for k in range(22):
            angles.append(k * math.pi / 11)
        
        for k in range(8):
            angles.append(k * math.pi / 4)
            angles.append(k * math.pi / 4 + ALPHA)
            angles.append(k * math.pi / 4 - ALPHA)
        
        for k in range(1, 12):
            angles.append(k * math.pi * 2 / GOLDEN_RATIO)
        
        return list(set(a % (2 * math.pi) for a in angles))
    
    def _generate_gtfe_angle(self, x: float, y: float,
                              placed_trees: List[ChristmasTree],
                              box_size: float) -> float:
        """Generate angle optimized by GTFE field."""
        if self.use_gtfe and self.gtfe:
            return self.gtfe.find_optimal_angle(x, y, placed_trees, box_size)
        
        if random.random() < 0.4:
            return random.choice(self.prf_angles)
        
        return random.uniform(0, 2 * math.pi)
    
    def _check_collision(self, candidate_poly: Polygon, 
                         placed_polygons: List[Polygon],
                         tree_index: STRtree) -> bool:
        possible_indices = tree_index.query(candidate_poly)
        for i in possible_indices:
            if (candidate_poly.intersects(placed_polygons[i]) and 
                not candidate_poly.touches(placed_polygons[i])):
                return True
        return False
    
    def _compute_lxe_score(self, placed_trees: List[ChristmasTree], 
                            side_length: Decimal, n: int) -> float:
        if n == 0:
            return 1.0
        
        theoretical_min = math.sqrt(n) * 0.7
        current_side = float(side_length)
        L = min(1.0, theoretical_min / max(current_side, 0.1))
        
        if len(placed_trees) < 2:
            E = 0.9
        else:
            positions = [(float(t.center_x), float(t.center_y)) for t in placed_trees]
            distances = []
            for i, p1 in enumerate(positions):
                for p2 in positions[i+1:]:
                    d = math.sqrt((p1[0] - p2[0])**2 + (p1[1] - p2[1])**2)
                    distances.append(d)
            
            if distances:
                mean_d = np.mean(distances)
                std_d = np.std(distances)
                cv = std_d / max(mean_d, 0.01)
                E = max(0.1, 1.0 - cv)
            else:
                E = 0.9
        
        return L * E
    
    def _find_gtfe_placement(self, tree: ChristmasTree,
                              placed_trees: List[ChristmasTree],
                              box_size: float) -> Tuple[Decimal, Decimal, float]:
        """Find optimal placement using GTFE field dynamics."""
        if not placed_trees:
            return Decimal('0'), Decimal('0'), 0.0
        
        placed_polygons = [t.polygon for t in placed_trees]
        tree_index = STRtree(placed_polygons)
        
        best_x, best_y = Decimal('0'), Decimal('0')
        best_angle = 0.0
        best_field = -1
        min_radius = Decimal('Infinity')
        
        for attempt in range(25):
            if self.use_gtfe:
                self.stats['field_evaluations'] += 1
                
                if attempt < 10:
                    base_angle = random.choice(self.prf_angles)
                else:
                    base_angle = random.uniform(0, 2 * math.pi)
            else:
                base_angle = random.uniform(0, 2 * math.pi)
            
            vx = Decimal(str(math.cos(base_angle)))
            vy = Decimal(str(math.sin(base_angle)))
            
            radius = Decimal('15.0')
            step_in = Decimal('0.3')
            
            collision_found = False
            while radius >= 0:
                px, py = radius * vx, radius * vy
                
                candidate_poly = affinity.translate(
                    tree.polygon,
                    xoff=float(px * SCALE_FACTOR),
                    yoff=float(py * SCALE_FACTOR)
                )
                
                if self._check_collision(candidate_poly, placed_polygons, tree_index):
                    collision_found = True
                    break
                radius -= step_in
            
            if collision_found:
                step_out = Decimal('0.03')
                for _ in range(30):
                    radius += step_out
                    px, py = radius * vx, radius * vy
                    
                    candidate_poly = affinity.translate(
                        tree.polygon,
                        xoff=float(px * SCALE_FACTOR),
                        yoff=float(py * SCALE_FACTOR)
                    )
                    
                    if not self._check_collision(candidate_poly, placed_polygons, tree_index):
                        break
            else:
                radius = Decimal('0')
                px, py = Decimal('0'), Decimal('0')
            
            if self.use_gtfe and self.gtfe:
                optimal_angle = self.gtfe.find_optimal_angle(
                    float(px), float(py), placed_trees, box_size
                )
                field_val = self.gtfe.field_value(
                    float(px), float(py), optimal_angle, placed_trees, box_size
                )
                
                effective_radius = radius * Decimal(str(1 / max(field_val, 0.1)))
                
                if effective_radius < min_radius or (effective_radius == min_radius and field_val > best_field):
                    min_radius = effective_radius
                    best_x, best_y = px, py
                    best_angle = optimal_angle
                    best_field = field_val
            else:
                if radius < min_radius:
                    min_radius = radius
                    best_x, best_y = px, py
                    best_angle = base_angle
        
        return best_x, best_y, best_angle
    
    def _apply_recursive_anchoring(self, placed_trees: List[ChristmasTree],
                                     target_lxe: float,
                                     max_iterations: int = 10) -> List[ChristmasTree]:
        """
        Recursive Anchoring Hypothesis refinement.
        
        Constants (and optimal placements) are refined via quantum indeterminacy
        until they anchor to stable values.
        """
        if len(placed_trees) < 3:
            return placed_trees
        
        current_side = self._compute_bounding_box(placed_trees)
        current_lxe = self._compute_lxe_score(placed_trees, current_side, len(placed_trees))
        
        for iteration in range(max_iterations):
            if current_lxe >= target_lxe:
                break
            
            improved = False
            other_polygons_cache = None
            
            for i, tree in enumerate(placed_trees[1:], 1):
                other_trees = placed_trees[:i] + placed_trees[i+1:]
                other_polygons = [t.polygon for t in other_trees]
                tree_index = STRtree(other_polygons)
                
                original_x, original_y = tree.center_x, tree.center_y
                
                centroid_x = sum(float(t.center_x) for t in other_trees) / len(other_trees)
                centroid_y = sum(float(t.center_y) for t in other_trees) / len(other_trees)
                
                toward_center_x = centroid_x - float(original_x)
                toward_center_y = centroid_y - float(original_y)
                dist = math.sqrt(toward_center_x**2 + toward_center_y**2)
                if dist > 0.01:
                    toward_center_x /= dist
                    toward_center_y /= dist
                
                for step in [0.08, 0.05, 0.03, 0.02]:
                    new_x = original_x + Decimal(str(toward_center_x * step))
                    new_y = original_y + Decimal(str(toward_center_y * step))
                    
                    test_tree = ChristmasTree(new_x, new_y, tree.angle)
                    
                    if not self._check_collision(test_tree.polygon, other_polygons, tree_index):
                        new_side = self._compute_bounding_box(
                            placed_trees[:i] + [test_tree] + placed_trees[i+1:]
                        )
                        
                        if new_side < current_side:
                            tree.move_to(new_x, new_y)
                            current_side = new_side
                            improved = True
                            self.stats['refinements'] += 1
                            break
                
            if not improved:
                break
            
            current_lxe = self._compute_lxe_score(placed_trees, current_side, len(placed_trees))
            self.stats['lxe_trajectory'].append(current_lxe)
        
        return placed_trees
    
    def _compute_bounding_box(self, placed_trees: List[ChristmasTree]) -> Decimal:
        if not placed_trees:
            return Decimal('0')
        
        all_polys = [t.polygon for t in placed_trees]
        combined = unary_union(all_polys)
        minx, miny, maxx, maxy = combined.bounds
        minx, miny = minx / float(SCALE_FACTOR), miny / float(SCALE_FACTOR)
        maxx, maxy = maxx / float(SCALE_FACTOR), maxy / float(SCALE_FACTOR)
        
        return Decimal(str(max(maxx - minx, maxy - miny)))
    
    def pack_trees(self, num_trees: int, verbose: bool = False) -> Tuple[List[ChristmasTree], Decimal]:
        """
        Pack n trees using GTFE-enhanced optimization.
        """
        if num_trees == 0:
            return [], Decimal('0')
        
        initial_box = max(2.0, math.sqrt(num_trees) * 1.5)
        self.gtfe = GTFEField(initial_box) if self.use_gtfe else None
        
        if self.use_mycelial and num_trees > 3:
            mycelial = MycelialDistributor(num_trees)
            placement_order = mycelial.get_placement_order()
        else:
            placement_order = list(range(num_trees))
        
        all_trees = []
        for i in range(num_trees):
            angle = random.choice(self.prf_angles) if random.random() < 0.5 else random.uniform(0, 2 * math.pi)
            all_trees.append(ChristmasTree(angle=Decimal(str(math.degrees(angle)))))
        
        placed_trees = []
        
        first_tree = all_trees[placement_order[0]]
        first_tree.move_to(Decimal('0'), Decimal('0'))
        placed_trees.append(first_tree)
        
        for idx in placement_order[1:]:
            tree = all_trees[idx]
            current_box = float(self._compute_bounding_box(placed_trees)) if placed_trees else initial_box
            
            px, py, opt_angle = self._find_gtfe_placement(tree, placed_trees, current_box * 2)
            tree.set_angle(Decimal(str(math.degrees(opt_angle))))
            tree.move_to(px, py)
            placed_trees.append(tree)
            
            self.stats['placements'] += 1
            
            if verbose and len(placed_trees) % 10 == 0:
                side = self._compute_bounding_box(placed_trees)
                lxe = self._compute_lxe_score(placed_trees, side, len(placed_trees))
                print(f"  Placed {len(placed_trees)}/{num_trees}, side={float(side):.4f}, L×E={lxe:.4f}")
        
        if self.use_gtfe:
            target_lxe = LXE_MANIFESTATION if num_trees < 50 else LXE_MANIFESTATION * 0.9
            placed_trees = self._apply_recursive_anchoring(placed_trees, target_lxe)
        
        side_length = self._compute_bounding_box(placed_trees)
        
        return placed_trees, side_length
    
    def get_lxe_state(self, lxe: float) -> str:
        if lxe >= LXE_RADIANT:
            return "RADIANT"
        elif lxe >= LXE_CAUSATION:
            return "CAUSATION"
        elif lxe >= LXE_MANIFESTATION:
            return "MANIFEST"
        else:
            return "BUILDING"


def run_gtfe_competition(max_n: int = 10, verbose: bool = True):
    """Run GTFE-enhanced solver for competition."""
    print("=" * 60)
    print("TI Sigma GTFE Enhanced Christmas Tree Packer")
    print("Kaggle Santa 2025 Competition")
    print("=" * 60)
    print()
    print("GTFE = Grand Tralse Field Equation")
    print("Optimizing with 11D L×E field dynamics...")
    print()
    
    packer = TIGUOPacker(use_gtfe=True, use_mycelial=True)
    
    results = []
    total_score = 0
    
    for n in range(1, max_n + 1):
        placed, side = packer.pack_trees(n, verbose=False)
        lxe = packer._compute_lxe_score(placed, side, n)
        state = packer.get_lxe_state(lxe)
        
        side_float = float(side)
        score_contrib = (side_float ** 2) / n
        total_score += score_contrib
        
        results.append({
            'n': n,
            'side': side_float,
            'lxe': lxe,
            'state': state,
            'score': score_contrib
        })
        
        if verbose:
            print(f"n={n:3d}: side={side_float:.6f}, L×E={lxe:.4f} [{state}]")
    
    print()
    print(f"Score for n=1-{max_n}: {total_score:.6f}")
    print()
    print("GTFE Statistics:")
    print(f"  Total placements: {packer.stats['placements']}")
    print(f"  Total refinements: {packer.stats['refinements']}")
    print(f"  Field evaluations: {packer.stats['field_evaluations']}")
    
    return results, total_score


if __name__ == "__main__":
    results, score = run_gtfe_competition(max_n=20, verbose=True)
    
    print()
    print("=" * 60)
    print("COMPETITION ANALYSIS")
    print("=" * 60)
    
    manifest_count = sum(1 for r in results if r['state'] in ['MANIFEST', 'CAUSATION', 'RADIANT'])
    print(f"Configurations reaching Manifestation threshold: {manifest_count}/{len(results)}")
    
    avg_lxe = np.mean([r['lxe'] for r in results])
    print(f"Average L×E score: {avg_lxe:.4f}")
    
    if avg_lxe >= LXE_MANIFESTATION:
        print("\n⚡ GTFE optimization achieving stable consciousness coherence!")
    
    print("\nNote: Full competition requires n=1-200. Run extended version for submission.")
