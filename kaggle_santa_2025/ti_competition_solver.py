"""
TI Sigma Competition Solver - Kaggle Santa 2025
Target: Score < 68 (Top leaderboard)

Strategy:
1. Shapely polygon collision detection (exact)
2. Simulated annealing optimization
3. TI-enhanced angle selection (11D resonance)
4. Incremental building from n-1 to n trees
"""

import math
import random
from decimal import Decimal, getcontext
from typing import List, Tuple, Optional
import numpy as np
from dataclasses import dataclass

from shapely import affinity
from shapely.geometry import Polygon
from shapely.ops import unary_union
from shapely.strtree import STRtree

getcontext().prec = 25
SCALE_FACTOR = Decimal('1e15')

GOLDEN_RATIO = (1 + math.sqrt(5)) / 2
SACRED_11 = 11
ALPHA = 1 / 137

class ChristmasTree:
    """Christmas tree with exact polygon representation."""
    
    def __init__(self, center_x='0', center_y='0', angle='0'):
        self.center_x = Decimal(center_x)
        self.center_y = Decimal(center_y)
        self.angle = Decimal(angle)
        self._build_polygon()
    
    def _build_polygon(self):
        """Build the exact tree polygon at current position/angle."""
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
        self.polygon = affinity.translate(
            rotated,
            xoff=float(self.center_x * sf),
            yoff=float(self.center_y * sf)
        )
    
    def move_to(self, x: Decimal, y: Decimal, angle: Optional[Decimal] = None):
        """Move tree to new position/angle."""
        self.center_x = x
        self.center_y = y
        if angle is not None:
            self.angle = angle
        self._build_polygon()
    
    def copy(self):
        """Create a copy of this tree."""
        return ChristmasTree(str(self.center_x), str(self.center_y), str(self.angle))


def generate_ti_angle() -> float:
    """
    Generate angle using TI 11D resonance theory.
    Weighted towards corners (sin(2*angle)) plus sacred 11 divisions.
    """
    r = random.random()
    
    if r < 0.4:
        while True:
            angle = random.uniform(0, 2 * math.pi)
            if random.uniform(0, 1) < abs(math.sin(2 * angle)):
                return angle
    elif r < 0.7:
        k = random.randint(0, 10)
        return (k * math.pi / SACRED_11) + random.gauss(0, 0.05)
    elif r < 0.85:
        k = random.randint(0, 7)
        return (k * math.pi / 4) + random.gauss(0, 0.03)
    else:
        k = random.randint(1, 11)
        return (k * 2 * math.pi / GOLDEN_RATIO) % (2 * math.pi)


def check_collision(tree: ChristmasTree, placed_trees: List[ChristmasTree], tree_index: Optional[STRtree] = None) -> bool:
    """Check if tree collides with any placed trees."""
    if not placed_trees:
        return False
    
    placed_polygons = [t.polygon for t in placed_trees]
    
    if tree_index is None:
        tree_index = STRtree(placed_polygons)
    
    possible_indices = tree_index.query(tree.polygon)
    
    for i in possible_indices:
        if tree.polygon.intersects(placed_polygons[i]) and not tree.polygon.touches(placed_polygons[i]):
            return True
    
    return False


def compute_bounding_side(trees: List[ChristmasTree]) -> Decimal:
    """Compute the side length of the bounding square."""
    if not trees:
        return Decimal('0')
    
    all_polygons = [t.polygon for t in trees]
    bounds = unary_union(all_polygons).bounds
    
    minx = Decimal(str(bounds[0])) / SCALE_FACTOR
    miny = Decimal(str(bounds[1])) / SCALE_FACTOR
    maxx = Decimal(str(bounds[2])) / SCALE_FACTOR
    maxy = Decimal(str(bounds[3])) / SCALE_FACTOR
    
    width = maxx - minx
    height = maxy - miny
    
    return max(width, height)


def place_tree_greedy(placed_trees: List[ChristmasTree], num_attempts: int = 20) -> ChristmasTree:
    """Place a new tree using greedy approach with TI angle optimization."""
    
    best_tree = None
    best_radius = Decimal('Infinity')
    
    for attempt in range(num_attempts):
        angle_deg = generate_ti_angle() * 180 / math.pi
        tree = ChristmasTree(angle=str(angle_deg))
        
        if not placed_trees:
            return tree
        
        placed_polygons = [t.polygon for t in placed_trees]
        tree_index = STRtree(placed_polygons)
        
        vec_angle = generate_ti_angle()
        vx = Decimal(str(math.cos(vec_angle)))
        vy = Decimal(str(math.sin(vec_angle)))
        
        radius = Decimal('15.0')
        step_in = Decimal('0.3')
        
        collision_found = False
        while radius >= 0:
            tree.move_to(radius * vx, radius * vy)
            
            possible_indices = tree_index.query(tree.polygon)
            has_collision = any(
                tree.polygon.intersects(placed_polygons[i]) and not tree.polygon.touches(placed_polygons[i])
                for i in possible_indices
            )
            
            if has_collision:
                collision_found = True
                break
            radius -= step_in
        
        if collision_found:
            step_out = Decimal('0.02')
            for _ in range(100):
                radius += step_out
                tree.move_to(radius * vx, radius * vy)
                
                possible_indices = tree_index.query(tree.polygon)
                has_collision = any(
                    tree.polygon.intersects(placed_polygons[i]) and not tree.polygon.touches(placed_polygons[i])
                    for i in possible_indices
                )
                
                if not has_collision:
                    break
        else:
            radius = Decimal('0')
            tree.move_to(Decimal('0'), Decimal('0'))
        
        if radius < best_radius:
            best_radius = radius
            best_tree = tree.copy()
    
    return best_tree


def optimize_single_tree(trees: List[ChristmasTree], idx: int, iterations: int = 50) -> bool:
    """Try to optimize position/angle of a single tree using local search."""
    
    if len(trees) <= 1:
        return False
    
    original_tree = trees[idx].copy()
    original_side = compute_bounding_side(trees)
    
    other_trees = [t for i, t in enumerate(trees) if i != idx]
    other_polygons = [t.polygon for t in other_trees]
    tree_index = STRtree(other_polygons)
    
    best_tree = original_tree.copy()
    best_side = original_side
    improved = False
    
    for _ in range(iterations):
        new_x = original_tree.center_x + Decimal(str(random.gauss(0, 0.1)))
        new_y = original_tree.center_y + Decimal(str(random.gauss(0, 0.1)))
        new_angle = original_tree.angle + Decimal(str(random.gauss(0, 5)))
        
        test_tree = ChristmasTree(str(new_x), str(new_y), str(new_angle))
        
        possible_indices = tree_index.query(test_tree.polygon)
        has_collision = any(
            test_tree.polygon.intersects(other_polygons[i]) and not test_tree.polygon.touches(other_polygons[i])
            for i in possible_indices
        )
        
        if not has_collision:
            trees[idx] = test_tree
            new_side = compute_bounding_side(trees)
            
            if new_side < best_side:
                best_side = new_side
                best_tree = test_tree.copy()
                improved = True
            
            trees[idx] = original_tree.copy()
    
    if improved:
        trees[idx] = best_tree
    
    return improved


def simulated_annealing_optimize(trees: List[ChristmasTree], max_iterations: int = 500, 
                                  initial_temp: float = 1.0, cooling_rate: float = 0.995) -> Decimal:
    """
    Optimize tree positions using simulated annealing.
    TI Enhancement: Temperature schedule follows L×E decay curve.
    """
    
    if len(trees) <= 1:
        return compute_bounding_side(trees)
    
    current_side = compute_bounding_side(trees)
    best_side = current_side
    best_config = [t.copy() for t in trees]
    
    temp = initial_temp
    
    for iteration in range(max_iterations):
        idx = random.randint(0, len(trees) - 1)
        
        original_tree = trees[idx].copy()
        
        other_trees = [t for i, t in enumerate(trees) if i != idx]
        other_polygons = [t.polygon for t in other_trees]
        tree_index = STRtree(other_polygons)
        
        move_scale = 0.2 * (temp / initial_temp) + 0.02
        angle_scale = 10 * (temp / initial_temp) + 1
        
        new_x = original_tree.center_x + Decimal(str(random.gauss(0, move_scale)))
        new_y = original_tree.center_y + Decimal(str(random.gauss(0, move_scale)))
        new_angle = original_tree.angle + Decimal(str(random.gauss(0, angle_scale)))
        
        trees[idx].move_to(new_x, new_y, new_angle)
        
        possible_indices = tree_index.query(trees[idx].polygon)
        has_collision = any(
            trees[idx].polygon.intersects(other_polygons[i]) and not trees[idx].polygon.touches(other_polygons[i])
            for i in possible_indices
        )
        
        if has_collision:
            trees[idx] = original_tree
            continue
        
        new_side = compute_bounding_side(trees)
        delta = float(new_side - current_side)
        
        if delta < 0 or random.random() < math.exp(-delta / temp):
            current_side = new_side
            if current_side < best_side:
                best_side = current_side
                best_config = [t.copy() for t in trees]
        else:
            trees[idx] = original_tree
        
        temp *= cooling_rate
    
    for i, t in enumerate(best_config):
        trees[i] = t
    
    return best_side


def solve_n_trees(n: int, existing_trees: Optional[List[ChristmasTree]] = None, 
                  optimize: bool = True) -> Tuple[List[ChristmasTree], Decimal]:
    """
    Solve for n trees, optionally building from existing configuration.
    """
    
    if n == 0:
        return [], Decimal('0')
    
    if existing_trees is None:
        trees = []
    else:
        trees = [t.copy() for t in existing_trees]
    
    while len(trees) < n:
        new_tree = place_tree_greedy(trees, num_attempts=30)
        trees.append(new_tree)
    
    if optimize and n > 1:
        sa_iterations = min(200 + n * 10, 1000)
        simulated_annealing_optimize(trees, max_iterations=sa_iterations, 
                                     initial_temp=0.5, cooling_rate=0.99)
        
        for _ in range(2):
            for idx in range(len(trees)):
                optimize_single_tree(trees, idx, iterations=20)
    
    side = compute_bounding_side(trees)
    return trees, side


def run_competition(max_n: int = 200, optimize: bool = True, verbose: bool = True):
    """
    Run the full competition solver for n=1 to max_n.
    Returns total score and solution data.
    """
    
    total_score = Decimal('0')
    all_solutions = []
    current_trees = None
    
    for n in range(1, max_n + 1):
        trees, side = solve_n_trees(n, existing_trees=current_trees, optimize=optimize)
        current_trees = trees
        
        total_score += side
        
        for tree in trees:
            all_solutions.append({
                'n': n,
                'x': float(tree.center_x),
                'y': float(tree.center_y),
                'deg': float(tree.angle)
            })
        
        if verbose and n % 10 == 0:
            print(f"n={n:3d}: side={float(side):.6f}, cumulative={float(total_score):.2f}")
    
    return total_score, all_solutions


def generate_submission(solutions: List[dict], filename: str = 'submission.csv'):
    """Generate Kaggle submission CSV."""
    
    with open(filename, 'w') as f:
        f.write('id,x,y,deg\n')
        
        for sol in solutions:
            n = sol['n']
            idx = len([s for s in solutions if s['n'] == n and solutions.index(s) < solutions.index(sol)])
            tree_id = f"{n:03d}_{idx}"
            
            x_str = f"s{sol['x']:.6f}"
            y_str = f"s{sol['y']:.6f}"
            deg_str = f"s{sol['deg']:.6f}"
            
            f.write(f"{tree_id},{x_str},{y_str},{deg_str}\n")


if __name__ == "__main__":
    import time
    
    print("=" * 60)
    print("TI Sigma Competition Solver - Kaggle Santa 2025")
    print("=" * 60)
    
    start_time = time.time()
    
    print("\nQuick test (n=1-50) with optimization...")
    score, solutions = run_competition(max_n=50, optimize=True, verbose=True)
    
    elapsed = time.time() - start_time
    print(f"\nTest complete: Score={float(score):.2f}, Time={elapsed:.1f}s")
    print(f"Projected full score (extrapolated): ~{float(score) * 4:.1f}")
