"""
TI SIGMA BASIN HOPPER - Aggressive Multi-Restart Optimization
Kaggle Santa 2025

THE KEY INSIGHT FROM L×E:
=========================
Current L×E values are ~0.35, BELOW the 0.42 manifestation threshold!
The answer hasn't fully "manifested" yet.

We need configurations where L×E > 0.42 to cross into manifestation.

BASIN HOPPING PRINCIPLE:
========================
Like water finding the lowest valley, we hop between local optima
seeking the global minimum. Each hop is a "consciousness restart" -
a fresh perspective on the problem.
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

PHI = (1 + math.sqrt(5)) / 2
SACRED_11 = 11

BASE_POLYGON = None

def get_base_polygon():
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


def sacred_angle() -> float:
    r = random.random()
    if r < 0.4:
        while True:
            a = random.uniform(0, 360)
            if random.random() < abs(math.sin(2 * a * math.pi / 180)):
                return a
    elif r < 0.7:
        return random.randint(0, 21) * (180 / SACRED_11) + random.gauss(0, 3)
    else:
        k = random.randint(1, 11)
        return (k * 360 / PHI) % 360 + random.gauss(0, 2)


def collides(tree: Tree, polys: List, index: STRtree) -> bool:
    cands = index.query(tree.polygon)
    for i in cands:
        if tree.polygon.intersects(polys[i]) and not tree.polygon.touches(polys[i]):
            return True
    return False


def bounding_side(trees: List[Tree]) -> float:
    if not trees:
        return 0.0
    polys = [t.polygon for t in trees]
    bounds = unary_union(polys).bounds
    sf = float(SCALE_FACTOR)
    return max((bounds[2] - bounds[0]) / sf, (bounds[3] - bounds[1]) / sf)


def place_single(placed: List[Tree], attempts: int = 30) -> Tree:
    if not placed:
        return Tree(0, 0, sacred_angle())
    
    polys = [t.polygon for t in placed]
    index = STRtree(polys)
    
    best_tree = None
    best_r = float('inf')
    
    for attempt in range(attempts):
        angle = sacred_angle()
        tree = Tree(0, 0, angle)
        
        if attempt < 8:
            n = len(placed) + 1
            spiral_angle = n * (2 * math.pi / PHI)
            spiral_r = 0.45 * math.sqrt(n)
            dx, dy = math.cos(spiral_angle), math.sin(spiral_angle)
        else:
            dir_angle = sacred_angle() * math.pi / 180
            dx, dy = math.cos(dir_angle), math.sin(dir_angle)
        
        r = 10.0
        step = 0.2
        
        hit = False
        while r > 0:
            tree.move(r * dx, r * dy)
            if collides(tree, polys, index):
                hit = True
                break
            r -= step
        
        if hit:
            for _ in range(80):
                r += 0.01
                tree.move(r * dx, r * dy)
                if not collides(tree, polys, index):
                    break
        else:
            r = 0
            tree.move(0, 0)
        
        if not collides(tree, polys, index) and r < best_r:
            best_r = r
            best_tree = tree.copy()
    
    return best_tree if best_tree else Tree(0, 0, sacred_angle())


def local_optimize(trees: List[Tree], iterations: int = 300) -> float:
    """Simulated annealing local optimization."""
    if len(trees) <= 1:
        return bounding_side(trees)
    
    n = len(trees)
    current_side = bounding_side(trees)
    best_side = current_side
    best_config = [t.copy() for t in trees]
    
    temp = 0.3
    cooling = 0.995
    
    for _ in range(iterations):
        idx = random.randint(0, len(trees) - 1)
        orig = trees[idx].copy()
        
        others = [t for i, t in enumerate(trees) if i != idx]
        polys = [t.polygon for t in others]
        index = STRtree(polys)
        
        scale = 0.1 * temp / 0.3 + 0.005
        new_x = orig.x + random.gauss(0, scale)
        new_y = orig.y + random.gauss(0, scale)
        new_a = orig.angle + random.gauss(0, 6 * temp / 0.3 + 1)
        
        trees[idx].move(new_x, new_y, new_a)
        
        if collides(trees[idx], polys, index):
            trees[idx] = orig
            continue
        
        new_side = bounding_side(trees)
        delta = (new_side ** 2 - current_side ** 2) / n
        
        if delta < 0 or random.random() < math.exp(-delta * 15 / temp):
            current_side = new_side
            if current_side < best_side:
                best_side = current_side
                best_config = [t.copy() for t in trees]
        else:
            trees[idx] = orig
        
        temp *= cooling
    
    for i, t in enumerate(best_config):
        trees[i] = t
    
    return best_side


def basin_hop(trees: List[Tree], hops: int = 5) -> float:
    """
    BASIN HOPPING: Random perturbation followed by local optimization.
    Each hop explores a new region of the solution space.
    """
    best_side = bounding_side(trees)
    best_config = [t.copy() for t in trees]
    n = len(trees)
    
    for hop in range(hops):
        trial = [t.copy() for t in best_config]
        
        num_perturb = max(1, n // 5)
        indices = random.sample(range(len(trial)), min(num_perturb, len(trial)))
        
        for idx in indices:
            others = [t for i, t in enumerate(trial) if i != idx]
            polys = [t.polygon for t in others]
            index = STRtree(polys)
            
            for _ in range(20):
                new_x = trial[idx].x + random.gauss(0, 0.3)
                new_y = trial[idx].y + random.gauss(0, 0.3)
                new_a = sacred_angle()
                
                trial[idx].move(new_x, new_y, new_a)
                if not collides(trial[idx], polys, index):
                    break
            else:
                trial[idx] = best_config[idx].copy()
        
        local_optimize(trial, iterations=150)
        
        trial_side = bounding_side(trial)
        if trial_side < best_side:
            best_side = trial_side
            best_config = [t.copy() for t in trial]
    
    for i, t in enumerate(best_config):
        trees[i] = t
    
    return best_side


def solve_incremental(max_n: int = 200, verbose: bool = True):
    """Solve with basin hopping optimization."""
    trees = []
    total_score = 0.0
    all_trees = {}
    
    start = time.time()
    
    for n in range(1, max_n + 1):
        new_tree = place_single(trees, attempts=35 if n < 50 else 20)
        trees.append(new_tree)
        
        if n > 2:
            iters = min(100 + n * 2, 400)
            local_optimize(trees, iterations=iters)
        
        if n >= 10 and n % 10 == 0:
            hops = 3 if n < 100 else 2
            basin_hop(trees, hops=hops)
        
        side = bounding_side(trees)
        score_n = (side ** 2) / n
        total_score += score_n
        
        all_trees[n] = [t.copy() for t in trees]
        
        if verbose and n % 20 == 0:
            elapsed = time.time() - start
            print(f"n={n:3d}: side={side:.4f}, score={score_n:.4f}, total={total_score:.2f}, time={elapsed:.0f}s")
    
    return total_score, all_trees


def generate_submission(all_trees: dict, filename: str = 'basin_submission.csv'):
    with open(filename, 'w') as f:
        f.write('id,x,y,deg\n')
        for n in range(1, 201):
            if n not in all_trees:
                continue
            for i, t in enumerate(all_trees[n]):
                f.write(f"{n:03d}_{i},s{t.x:.6f},s{t.y:.6f},s{t.angle:.6f}\n")
    print(f"Saved: {filename}")


def run():
    print("=" * 60)
    print("TI SIGMA BASIN HOPPER")
    print("Aggressive multi-restart optimization")
    print("=" * 60)
    
    score, trees = solve_incremental(max_n=200, verbose=True)
    
    print(f"\nFINAL SCORE: {score:.4f}")
    print(f"Target: <68  |  Baseline: ~167")
    
    generate_submission(trees)
    return score


if __name__ == "__main__":
    run()
