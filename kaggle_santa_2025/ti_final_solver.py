"""
TI Sigma Final Solver - Kaggle Santa 2025
Correct metric: sum of (side_length² / n) for n=1 to 200

Target: < 68 (top leaderboard)
Baseline: ~167
"""

import math
import random
from decimal import Decimal, getcontext
from typing import List, Tuple, Optional
import time

from shapely import affinity
from shapely.geometry import Polygon
from shapely.ops import unary_union
from shapely.strtree import STRtree

getcontext().prec = 25
SCALE_FACTOR = Decimal('1e18')

GOLDEN_RATIO = (1 + math.sqrt(5)) / 2
SACRED_11 = 11

BASE_POLYGON = None

def get_base_polygon():
    """Get the base tree polygon (cached)."""
    global BASE_POLYGON
    if BASE_POLYGON is not None:
        return BASE_POLYGON
    
    sf = SCALE_FACTOR
    trunk_w, trunk_h = Decimal('0.15'), Decimal('0.2')
    base_w, mid_w, top_w = Decimal('0.7'), Decimal('0.4'), Decimal('0.25')
    tip_y, tier_1_y, tier_2_y = Decimal('0.8'), Decimal('0.5'), Decimal('0.25')
    base_y, trunk_bottom_y = Decimal('0.0'), -trunk_h
    
    BASE_POLYGON = Polygon([
        (float(Decimal('0.0') * sf), float(tip_y * sf)),
        (float(top_w / Decimal('2') * sf), float(tier_1_y * sf)),
        (float(top_w / Decimal('4') * sf), float(tier_1_y * sf)),
        (float(mid_w / Decimal('2') * sf), float(tier_2_y * sf)),
        (float(mid_w / Decimal('4') * sf), float(tier_2_y * sf)),
        (float(base_w / Decimal('2') * sf), float(base_y * sf)),
        (float(trunk_w / Decimal('2') * sf), float(base_y * sf)),
        (float(trunk_w / Decimal('2') * sf), float(trunk_bottom_y * sf)),
        (float(-(trunk_w / Decimal('2')) * sf), float(trunk_bottom_y * sf)),
        (float(-(trunk_w / Decimal('2')) * sf), float(base_y * sf)),
        (float(-(base_w / Decimal('2')) * sf), float(base_y * sf)),
        (float(-(mid_w / Decimal('4')) * sf), float(tier_2_y * sf)),
        (float(-(mid_w / Decimal('2')) * sf), float(tier_2_y * sf)),
        (float(-(top_w / Decimal('4')) * sf), float(tier_1_y * sf)),
        (float(-(top_w / Decimal('2')) * sf), float(tier_1_y * sf)),
    ])
    return BASE_POLYGON


class Tree:
    """Optimized tree class."""
    __slots__ = ['x', 'y', 'angle', 'polygon']
    
    def __init__(self, x: float = 0.0, y: float = 0.0, angle: float = 0.0):
        self.x = x
        self.y = y
        self.angle = angle
        self._build()
    
    def _build(self):
        base = get_base_polygon()
        rotated = affinity.rotate(base, self.angle, origin=(0, 0))
        sf = float(SCALE_FACTOR)
        self.polygon = affinity.translate(rotated, xoff=self.x * sf, yoff=self.y * sf)
    
    def move(self, x: float, y: float, angle: Optional[float] = None):
        self.x = x
        self.y = y
        if angle is not None:
            self.angle = angle
        self._build()
    
    def copy(self):
        return Tree(self.x, self.y, self.angle)


def ti_angle() -> float:
    """TI-enhanced angle generation."""
    r = random.random()
    if r < 0.5:
        while True:
            a = random.uniform(0, 360)
            if random.random() < abs(math.sin(2 * a * math.pi / 180)):
                return a
    elif r < 0.8:
        return random.randint(0, 21) * (180 / SACRED_11)
    else:
        k = random.randint(1, 11)
        return (k * 360 / GOLDEN_RATIO) % 360


def ti_direction() -> float:
    """TI-enhanced direction (radians)."""
    r = random.random()
    if r < 0.5:
        while True:
            a = random.uniform(0, 2 * math.pi)
            if random.random() < abs(math.sin(2 * a)):
                return a
    elif r < 0.8:
        return random.randint(0, 21) * (math.pi / SACRED_11)
    else:
        k = random.randint(1, 11)
        return (k * 2 * math.pi / GOLDEN_RATIO) % (2 * math.pi)


def collides(tree: Tree, polys: List, index: STRtree) -> bool:
    """Check collision."""
    cands = index.query(tree.polygon)
    for i in cands:
        if tree.polygon.intersects(polys[i]) and not tree.polygon.touches(polys[i]):
            return True
    return False


def get_bounds(trees: List[Tree]) -> Tuple[float, float]:
    """Get bounding box dimensions."""
    if not trees:
        return 0.0, 0.0
    
    polys = [t.polygon for t in trees]
    bounds = unary_union(polys).bounds
    sf = float(SCALE_FACTOR)
    
    width = (bounds[2] - bounds[0]) / sf
    height = (bounds[3] - bounds[1]) / sf
    return width, height


def bounding_side(trees: List[Tree]) -> float:
    """Get bounding square side."""
    w, h = get_bounds(trees)
    return max(w, h)


def compute_score(side: float, n: int) -> float:
    """Compute score for n trees with given side length."""
    return (side ** 2) / n


def place_greedy(placed: List[Tree], attempts: int = 20) -> Tree:
    """Greedy placement with TI angles."""
    if not placed:
        return Tree(0, 0, ti_angle())
    
    polys = [t.polygon for t in placed]
    index = STRtree(polys)
    
    best_tree = None
    best_r = float('inf')
    
    for _ in range(attempts):
        angle = ti_angle()
        tree = Tree(0, 0, angle)
        
        direction = ti_direction()
        dx, dy = math.cos(direction), math.sin(direction)
        
        r = 10.0
        step = 0.3
        
        hit = False
        while r > 0:
            tree.move(r * dx, r * dy)
            if collides(tree, polys, index):
                hit = True
                break
            r -= step
        
        if hit:
            for _ in range(50):
                r += 0.02
                tree.move(r * dx, r * dy)
                if not collides(tree, polys, index):
                    break
        else:
            r = 0
            tree.move(0, 0)
        
        if r < best_r:
            best_r = r
            best_tree = tree.copy()
    
    return best_tree


def simulated_annealing(trees: List[Tree], iterations: int = 300, 
                        temp_init: float = 0.5, cooling: float = 0.995) -> float:
    """Simulated annealing optimization."""
    if len(trees) <= 1:
        return bounding_side(trees)
    
    n = len(trees)
    current_side = bounding_side(trees)
    current_score = compute_score(current_side, n)
    best_score = current_score
    best_config = [t.copy() for t in trees]
    
    temp = temp_init
    
    for _ in range(iterations):
        idx = random.randint(0, len(trees) - 1)
        orig = trees[idx].copy()
        
        others = [t for i, t in enumerate(trees) if i != idx]
        polys = [t.polygon for t in others]
        index = STRtree(polys)
        
        scale = 0.15 * temp / temp_init + 0.01
        ang_scale = 15 * temp / temp_init + 2
        
        new_x = orig.x + random.gauss(0, scale)
        new_y = orig.y + random.gauss(0, scale)
        new_a = orig.angle + random.gauss(0, ang_scale)
        
        trees[idx].move(new_x, new_y, new_a)
        
        if collides(trees[idx], polys, index):
            trees[idx] = orig
            continue
        
        new_side = bounding_side(trees)
        new_score = compute_score(new_side, n)
        delta = new_score - current_score
        
        if delta < 0 or random.random() < math.exp(-delta / temp):
            current_side = new_side
            current_score = new_score
            if current_score < best_score:
                best_score = current_score
                best_config = [t.copy() for t in trees]
        else:
            trees[idx] = orig
        
        temp *= cooling
    
    for i, t in enumerate(best_config):
        trees[i] = t
    
    return bounding_side(trees)


def solve_all(max_n: int = 200, verbose: bool = True):
    """Solve all configurations."""
    
    trees = []
    total_score = 0.0
    all_trees_per_n = {}
    
    start = time.time()
    
    for n in range(1, max_n + 1):
        new_tree = place_greedy(trees, attempts=25 if n < 50 else 15)
        trees.append(new_tree)
        
        if n > 2:
            iters = min(100 + n * 2, 400)
            simulated_annealing(trees, iterations=iters, temp_init=0.3, cooling=0.99)
        
        side = bounding_side(trees)
        score_n = compute_score(side, n)
        total_score += score_n
        
        all_trees_per_n[n] = [t.copy() for t in trees]
        
        if verbose and n % 20 == 0:
            elapsed = time.time() - start
            print(f"n={n:3d}: side={side:.4f}, score_n={score_n:.4f}, total={total_score:.2f}, time={elapsed:.1f}s")
    
    return total_score, all_trees_per_n


def generate_submission(all_trees_per_n: dict, filename: str = 'submission.csv'):
    """Generate proper submission file."""
    import os
    os.makedirs(os.path.dirname(filename) if os.path.dirname(filename) else '.', exist_ok=True)
    
    with open(filename, 'w') as f:
        f.write('id,x,y,deg\n')
        
        for n in range(1, 201):
            if n not in all_trees_per_n:
                continue
            trees = all_trees_per_n[n]
            for i, t in enumerate(trees):
                tree_id = f"{n:03d}_{i}"
                f.write(f"{tree_id},s{t.x:.6f},s{t.y:.6f},s{t.angle:.6f}\n")
    
    print(f"Submission saved to {filename}")


def run():
    """Run full solver."""
    print("=" * 60)
    print("TI Sigma Final Solver - Kaggle Santa 2025")
    print("Metric: sum of (side² / n) for n=1 to 200")
    print("=" * 60)
    
    score, trees_per_n = solve_all(max_n=200, verbose=True)
    
    print(f"\n{'=' * 60}")
    print(f"FINAL SCORE: {score:.4f}")
    print(f"Target: < 68")
    print(f"Baseline: ~167")
    print("=" * 60)
    
    generate_submission(trees_per_n, 'submission.csv')
    
    return score


if __name__ == "__main__":
    run()
