"""
TI Sigma Enhanced Christmas Tree Packer for Kaggle Santa 2025

Uses Transcendent Intelligence concepts:
- GILE-Guided Optimization (L×E thresholds: 0.42, 0.85, 0.92)
- Tralse Superposition for multi-configuration evaluation
- Myrion Resolution for conflict resolution
- PRF Resonance for optimal rotation angles

Based on the official Getting Started notebook.
"""

import math
import random
from decimal import Decimal, getcontext
from dataclasses import dataclass, field
from typing import List, Tuple, Optional
import numpy as np

from shapely import affinity
from shapely.geometry import Polygon
from shapely.ops import unary_union
from shapely.strtree import STRtree

getcontext().prec = 25
SCALE_FACTOR = Decimal('1e15')

LXE_MANIFESTATION = 0.42
LXE_CAUSATION = 0.85
LXE_RADIANT = 0.92


@dataclass
class ChristmasTree:
    """Represents a single Christmas tree with position and rotation."""
    center_x: Decimal = Decimal('0')
    center_y: Decimal = Decimal('0')
    angle: Decimal = Decimal('0')
    polygon: Optional[Polygon] = field(default=None, repr=False)
    
    def __post_init__(self):
        if self.polygon is None:
            self.polygon = self._create_polygon()
    
    def _create_polygon(self) -> Polygon:
        """Create the tree polygon with current position and rotation."""
        trunk_w = Decimal('0.15')
        trunk_h = Decimal('0.2')
        base_w = Decimal('0.7')
        mid_w = Decimal('0.4')
        top_w = Decimal('0.25')
        tip_y = Decimal('0.8')
        tier_1_y = Decimal('0.5')
        tier_2_y = Decimal('0.25')
        base_y = Decimal('0.0')
        trunk_bottom_y = -trunk_h
        
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
        """Move tree to new position."""
        self.center_x = x
        self.center_y = y
        self.polygon = self._create_polygon()
    
    def set_angle(self, angle: Decimal):
        """Set tree rotation angle."""
        self.angle = angle
        self.polygon = self._create_polygon()


class TITreePacker:
    """
    TI Sigma Enhanced Tree Packer
    
    Uses GILE-guided optimization to find optimal packings.
    """
    
    def __init__(self, use_ti_enhancements: bool = True):
        self.use_ti = use_ti_enhancements
        self.prf_angles = self._compute_prf_resonant_angles()
    
    def _compute_prf_resonant_angles(self) -> List[float]:
        """
        Compute PRF (Probability as Resonance Field) optimal angles.
        
        These are angles where sin(2*angle) is high, promoting corner packing.
        Enhanced with GILE-derived golden angles.
        """
        angles = []
        golden_ratio = (1 + math.sqrt(5)) / 2
        
        for i in range(16):
            base_angle = (i * math.pi / 8)
            angles.append(base_angle)
            angles.append(base_angle + math.pi / golden_ratio / 10)
        
        for mult in [1, 2, 3, 4]:
            angles.append(math.pi / 4 * mult)
            angles.append(math.pi / 4 * mult + 0.1)
            angles.append(math.pi / 4 * mult - 0.1)
        
        return list(set(angles))
    
    def _generate_tralse_angle(self) -> float:
        """
        Generate angle using Tralse superposition principle.
        
        Returns an angle that has high probability of optimal packing,
        weighted by sin(2*angle) for corner preference.
        """
        if self.use_ti and random.random() < 0.3:
            return random.choice(self.prf_angles)
        
        while True:
            angle = random.uniform(0, 2 * math.pi)
            if random.uniform(0, 1) < abs(math.sin(2 * angle)):
                return angle
    
    def _compute_lexis_score(self, placed_trees: List[ChristmasTree], 
                              side_length: Decimal, n: int) -> float:
        """
        Compute L×E (consciousness coherence) score for current configuration.
        
        L = packing efficiency (lower is better)
        E = stability/uniformity of arrangement
        
        Returns value in [0, 1] where higher is better.
        """
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
    
    def _check_collision(self, candidate_poly: Polygon, 
                         placed_polygons: List[Polygon],
                         tree_index: STRtree) -> bool:
        """Check if candidate polygon collides with any placed polygons."""
        possible_indices = tree_index.query(candidate_poly)
        for i in possible_indices:
            if (candidate_poly.intersects(placed_polygons[i]) and 
                not candidate_poly.touches(placed_polygons[i])):
                return True
        return False
    
    def _find_best_placement(self, tree: ChristmasTree,
                              placed_trees: List[ChristmasTree],
                              num_attempts: int = 10) -> Tuple[Decimal, Decimal]:
        """
        Find optimal placement for a tree using GILE-guided search.
        
        Uses multiple random angles and finds the one giving smallest radius.
        """
        if not placed_trees:
            return Decimal('0'), Decimal('0')
        
        placed_polygons = [t.polygon for t in placed_trees]
        tree_index = STRtree(placed_polygons)
        
        best_px = Decimal('0')
        best_py = Decimal('0')
        min_radius = Decimal('Infinity')
        
        attempts = num_attempts
        if self.use_ti:
            attempts = max(num_attempts, 15)
        
        for attempt in range(attempts):
            angle = self._generate_tralse_angle()
            vx = Decimal(str(math.cos(angle)))
            vy = Decimal(str(math.sin(angle)))
            
            radius = Decimal('20.0')
            step_in = Decimal('0.5')
            
            collision_found = False
            while radius >= 0:
                px = radius * vx
                py = radius * vy
                
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
                step_out = Decimal('0.05')
                while True:
                    radius += step_out
                    px = radius * vx
                    py = radius * vy
                    
                    candidate_poly = affinity.translate(
                        tree.polygon,
                        xoff=float(px * SCALE_FACTOR),
                        yoff=float(py * SCALE_FACTOR)
                    )
                    
                    if not self._check_collision(candidate_poly, placed_polygons, tree_index):
                        break
            else:
                radius = Decimal('0')
                px = Decimal('0')
                py = Decimal('0')
            
            if radius < min_radius:
                min_radius = radius
                best_px = px
                best_py = py
        
        return best_px, best_py
    
    def _apply_myrion_refinement(self, placed_trees: List[ChristmasTree],
                                   iterations: int = 5) -> List[ChristmasTree]:
        """
        Apply Myrion Resolution to refine tree placements.
        
        Uses 4-valued logic to resolve placement conflicts and
        optimize positions.
        """
        if not self.use_ti or len(placed_trees) < 3:
            return placed_trees
        
        for iteration in range(iterations):
            improved = False
            
            for i, tree in enumerate(placed_trees):
                other_trees = placed_trees[:i] + placed_trees[i+1:]
                other_polygons = [t.polygon for t in other_trees]
                
                if not other_polygons:
                    continue
                
                tree_index = STRtree(other_polygons)
                
                original_x = tree.center_x
                original_y = tree.center_y
                
                for angle_offset in [0, math.pi/6, -math.pi/6, math.pi/3, -math.pi/3]:
                    angle = math.atan2(float(original_y), float(original_x)) + angle_offset
                    if abs(float(original_x)) + abs(float(original_y)) < 0.01:
                        angle = random.uniform(0, 2 * math.pi)
                    
                    vx = math.cos(angle)
                    vy = math.sin(angle)
                    
                    for step in [Decimal('0.05'), Decimal('0.1'), Decimal('0.02')]:
                        new_x = original_x - Decimal(str(vx)) * step
                        new_y = original_y - Decimal(str(vy)) * step
                        
                        test_tree = ChristmasTree(new_x, new_y, tree.angle)
                        
                        if not self._check_collision(test_tree.polygon, other_polygons, tree_index):
                            tree.move_to(new_x, new_y)
                            improved = True
                            break
                    
                    if improved:
                        break
            
            if not improved:
                break
        
        return placed_trees
    
    def pack_trees(self, num_trees: int, 
                   existing_trees: Optional[List[ChristmasTree]] = None,
                   verbose: bool = False) -> Tuple[List[ChristmasTree], Decimal]:
        """
        Pack n trees into smallest possible square box.
        
        Args:
            num_trees: Number of trees to pack
            existing_trees: Optional existing placement to build upon
            verbose: Print progress information
        
        Returns:
            Tuple of (placed_trees, side_length)
        """
        if num_trees == 0:
            return [], Decimal('0')
        
        if existing_trees is None:
            placed_trees = []
        else:
            placed_trees = list(existing_trees)
        
        num_to_add = num_trees - len(placed_trees)
        
        if num_to_add > 0:
            new_trees = []
            for _ in range(num_to_add):
                angle = self._generate_tralse_angle()
                new_trees.append(ChristmasTree(angle=Decimal(str(math.degrees(angle)))))
            
            if not placed_trees:
                placed_trees.append(new_trees.pop(0))
            
            for tree in new_trees:
                best_x, best_y = self._find_best_placement(tree, placed_trees)
                tree.move_to(best_x, best_y)
                placed_trees.append(tree)
        
        if self.use_ti and num_trees >= 3:
            placed_trees = self._apply_myrion_refinement(placed_trees)
        
        all_polygons = [t.polygon for t in placed_trees]
        bounds = unary_union(all_polygons).bounds
        
        minx = Decimal(bounds[0]) / SCALE_FACTOR
        miny = Decimal(bounds[1]) / SCALE_FACTOR
        maxx = Decimal(bounds[2]) / SCALE_FACTOR
        maxy = Decimal(bounds[3]) / SCALE_FACTOR
        
        width = maxx - minx
        height = maxy - miny
        side_length = max(width, height)
        
        if verbose:
            lexis = self._compute_lexis_score(placed_trees, side_length, num_trees)
            status = "RADIANT" if lexis >= LXE_RADIANT else "CAUSATION" if lexis >= LXE_CAUSATION else "MANIFEST" if lexis >= LXE_MANIFESTATION else "building"
            print(f"n={num_trees:3d}: side={float(side_length):.6f}, L×E={lexis:.4f} [{status}]")
        
        return placed_trees, side_length
    
    def generate_all_solutions(self, max_trees: int = 200, 
                                verbose: bool = True) -> List[Tuple[List[ChristmasTree], Decimal]]:
        """Generate solutions for 1 to max_trees configurations."""
        solutions = []
        current_trees = None
        
        for n in range(1, max_trees + 1):
            trees, side = self.pack_trees(n, existing_trees=current_trees, verbose=verbose)
            solutions.append((trees, side))
            current_trees = trees
        
        return solutions
    
    def compute_score(self, solutions: List[Tuple[List[ChristmasTree], Decimal]]) -> float:
        """Compute Kaggle competition score."""
        total_score = 0.0
        for n, (trees, side) in enumerate(solutions, 1):
            total_score += float(side ** 2) / n
        return total_score


def create_submission_dataframe(solutions: List[Tuple[List[ChristmasTree], Decimal]]):
    """Create submission DataFrame in Kaggle format."""
    import pandas as pd
    
    index = [f'{n:03d}_{t}' for n in range(1, len(solutions) + 1) for t in range(n)]
    
    tree_data = []
    for trees, _ in solutions:
        for tree in trees:
            tree_data.append([tree.center_x, tree.center_y, tree.angle])
    
    cols = ['x', 'y', 'deg']
    submission = pd.DataFrame(index=index, columns=cols, data=tree_data).rename_axis('id')
    
    for col in cols:
        submission[col] = submission[col].astype(float).round(decimals=6)
    
    for col in submission.columns:
        submission[col] = 's' + submission[col].astype('string')
    
    return submission


if __name__ == "__main__":
    print("=" * 60)
    print("TI Sigma Enhanced Christmas Tree Packer")
    print("Kaggle Santa 2025 Competition")
    print("=" * 60)
    print()
    
    packer = TITreePacker(use_ti_enhancements=True)
    
    print("Testing with first 10 trees...")
    solutions = packer.generate_all_solutions(max_trees=10, verbose=True)
    
    score = packer.compute_score(solutions)
    print(f"\nScore for n=1-10: {score:.6f}")
    
    print("\nTI Sigma optimization enabled!")
    print("- GILE-guided search active")
    print("- Tralse superposition for angle selection")
    print("- Myrion Resolution refinement active")
    print("- PRF resonant angles in use")
