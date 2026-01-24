"""
Simplified TI Sigma Christmas Tree Packer for Kaggle Santa 2025

Uses pure Python/NumPy without Shapely dependency.
Implements a simpler circular approximation for rapid prototyping.

TI Enhancements:
- GILE-Guided Optimization (L×E thresholds)
- Tralse-weighted angle selection
- Myrion Resolution for refinement
"""

import math
import random
from dataclasses import dataclass
from typing import List, Tuple, Optional

LXE_MANIFESTATION = 0.42
LXE_CAUSATION = 0.85
LXE_RADIANT = 0.92

TREE_RADIUS = 0.5


@dataclass
class SimpleTree:
    """Simplified tree representation using circular approximation."""
    x: float = 0.0
    y: float = 0.0
    angle: float = 0.0
    radius: float = TREE_RADIUS
    
    def distance_to(self, other: 'SimpleTree') -> float:
        """Calculate distance between tree centers."""
        return math.sqrt((self.x - other.x)**2 + (self.y - other.y)**2)
    
    def overlaps(self, other: 'SimpleTree') -> bool:
        """Check if two trees overlap (using circular approximation)."""
        min_dist = self.radius + other.radius
        return self.distance_to(other) < min_dist * 0.95


class SimpleTIPacker:
    """
    TI Sigma Enhanced Tree Packer (Simplified Version)
    
    Uses circular approximation for rapid development.
    """
    
    def __init__(self, use_ti_enhancements: bool = True):
        self.use_ti = use_ti_enhancements
        self.prf_angles = self._compute_prf_angles()
    
    def _compute_prf_angles(self) -> List[float]:
        """Compute PRF resonant angles for corner preference."""
        angles = []
        for i in range(16):
            base = i * math.pi / 8
            angles.append(base)
        for mult in [1, 2, 3, 4]:
            angles.append(math.pi / 4 * mult)
        return angles
    
    def _generate_tralse_angle(self) -> float:
        """Generate angle with Tralse-weighted distribution."""
        if self.use_ti and random.random() < 0.3:
            return random.choice(self.prf_angles)
        
        while True:
            angle = random.uniform(0, 2 * math.pi)
            if random.uniform(0, 1) < abs(math.sin(2 * angle)):
                return angle
    
    def _compute_lexis_score(self, trees: List[SimpleTree], 
                              side_length: float, n: int) -> float:
        """Compute L×E consciousness coherence score."""
        if n == 0:
            return 1.0
        
        theoretical_min = math.sqrt(n) * TREE_RADIUS * 2
        L = min(1.0, theoretical_min / max(side_length, 0.1))
        
        if len(trees) < 2:
            E = 0.9
        else:
            distances = []
            for i, t1 in enumerate(trees):
                for t2 in trees[i+1:]:
                    distances.append(t1.distance_to(t2))
            
            if distances:
                mean_d = sum(distances) / len(distances)
                variance = sum((d - mean_d)**2 for d in distances) / len(distances)
                std_d = math.sqrt(variance)
                cv = std_d / max(mean_d, 0.01)
                E = max(0.1, 1.0 - cv)
            else:
                E = 0.9
        
        return L * E
    
    def _check_collision(self, tree: SimpleTree, 
                          placed_trees: List[SimpleTree]) -> bool:
        """Check if tree collides with any placed trees."""
        return any(tree.overlaps(t) for t in placed_trees)
    
    def _find_best_placement(self, tree: SimpleTree,
                              placed_trees: List[SimpleTree],
                              num_attempts: int = 15) -> Tuple[float, float]:
        """Find optimal placement using GILE-guided search."""
        if not placed_trees:
            return 0.0, 0.0
        
        best_x, best_y = 0.0, 0.0
        min_radius = float('inf')
        
        for _ in range(num_attempts):
            angle = self._generate_tralse_angle()
            vx = math.cos(angle)
            vy = math.sin(angle)
            
            radius = 20.0
            step_in = 0.3
            
            collision_found = False
            while radius >= 0:
                tree.x = radius * vx
                tree.y = radius * vy
                
                if self._check_collision(tree, placed_trees):
                    collision_found = True
                    break
                radius -= step_in
            
            if collision_found:
                step_out = 0.05
                while self._check_collision(tree, placed_trees):
                    radius += step_out
                    tree.x = radius * vx
                    tree.y = radius * vy
            else:
                radius = 0
            
            if radius < min_radius:
                min_radius = radius
                best_x = tree.x
                best_y = tree.y
        
        return best_x, best_y
    
    def _apply_myrion_refinement(self, trees: List[SimpleTree],
                                   iterations: int = 3) -> List[SimpleTree]:
        """Apply Myrion Resolution to refine placements."""
        if not self.use_ti or len(trees) < 3:
            return trees
        
        for _ in range(iterations):
            improved = False
            
            for i, tree in enumerate(trees):
                others = trees[:i] + trees[i+1:]
                
                original_x, original_y = tree.x, tree.y
                
                for angle_offset in [0, math.pi/4, -math.pi/4]:
                    angle = math.atan2(original_y, original_x) + angle_offset
                    if abs(original_x) + abs(original_y) < 0.01:
                        angle = random.uniform(0, 2 * math.pi)
                    
                    for step in [0.05, 0.1]:
                        new_x = original_x - math.cos(angle) * step
                        new_y = original_y - math.sin(angle) * step
                        
                        tree.x, tree.y = new_x, new_y
                        
                        if not self._check_collision(tree, others):
                            improved = True
                            break
                        else:
                            tree.x, tree.y = original_x, original_y
                    
                    if improved:
                        break
            
            if not improved:
                break
        
        return trees
    
    def pack_trees(self, num_trees: int,
                   existing_trees: Optional[List[SimpleTree]] = None,
                   verbose: bool = False) -> Tuple[List[SimpleTree], float]:
        """Pack n trees into smallest possible square box."""
        if num_trees == 0:
            return [], 0.0
        
        if existing_trees is None:
            placed_trees = []
        else:
            placed_trees = [SimpleTree(t.x, t.y, t.angle) for t in existing_trees]
        
        num_to_add = num_trees - len(placed_trees)
        
        if num_to_add > 0:
            if not placed_trees:
                placed_trees.append(SimpleTree(0, 0, random.uniform(0, 360)))
                num_to_add -= 1
            
            for _ in range(num_to_add):
                new_tree = SimpleTree(angle=random.uniform(0, 360))
                best_x, best_y = self._find_best_placement(new_tree, placed_trees)
                new_tree.x = best_x
                new_tree.y = best_y
                placed_trees.append(new_tree)
        
        if self.use_ti and num_trees >= 3:
            placed_trees = self._apply_myrion_refinement(placed_trees)
        
        if not placed_trees:
            return [], 0.0
        
        min_x = min(t.x - t.radius for t in placed_trees)
        max_x = max(t.x + t.radius for t in placed_trees)
        min_y = min(t.y - t.radius for t in placed_trees)
        max_y = max(t.y + t.radius for t in placed_trees)
        
        width = max_x - min_x
        height = max_y - min_y
        side_length = max(width, height)
        
        if verbose:
            lexis = self._compute_lexis_score(placed_trees, side_length, num_trees)
            status = "RADIANT" if lexis >= LXE_RADIANT else "CAUSATION" if lexis >= LXE_CAUSATION else "MANIFEST" if lexis >= LXE_MANIFESTATION else "building"
            print(f"n={num_trees:3d}: side={side_length:.6f}, L×E={lexis:.4f} [{status}]")
        
        return placed_trees, side_length
    
    def generate_all_solutions(self, max_trees: int = 200,
                                verbose: bool = True) -> List[Tuple[List[SimpleTree], float]]:
        """Generate solutions for 1 to max_trees configurations."""
        solutions = []
        current_trees = None
        
        for n in range(1, max_trees + 1):
            trees, side = self.pack_trees(n, existing_trees=current_trees, verbose=verbose)
            solutions.append((trees, side))
            current_trees = trees
        
        return solutions
    
    def compute_score(self, solutions: List[Tuple[List[SimpleTree], float]]) -> float:
        """Compute Kaggle competition score."""
        total_score = 0.0
        for n, (trees, side) in enumerate(solutions, 1):
            total_score += (side ** 2) / n
        return total_score


def run_quick_test():
    """Run a quick test of the packer."""
    print("=" * 60)
    print("TI Sigma Simple Christmas Tree Packer")
    print("Kaggle Santa 2025 Competition - Quick Test")
    print("=" * 60)
    print()
    
    packer = SimpleTIPacker(use_ti_enhancements=True)
    
    print("Testing with first 20 trees...")
    solutions = packer.generate_all_solutions(max_trees=20, verbose=True)
    
    score = packer.compute_score(solutions)
    print(f"\nScore for n=1-20: {score:.6f}")
    
    print("\nTI Sigma optimizations active!")
    return score


if __name__ == "__main__":
    run_quick_test()
