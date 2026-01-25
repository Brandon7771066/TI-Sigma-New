"""
TI Sigma Speed Solver - Kaggle Santa 2025
Optimized for speed while maintaining competitive quality.
Target: Full n=1-200 in under 10 minutes, score < 100
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
SCALE_FACTOR = Decimal('1e15')

GOLDEN_RATIO = (1 + math.sqrt(5)) / 2
SACRED_11 = 11

BASE_POLYGON = None

def get_base_polygon():
    """Get the base tree polygon (cached for speed)."""
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


class FastTree:
    """Optimized tree class using float operations."""
    
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
        return FastTree(self.x, self.y, self.angle)


def ti_angle() -> float:
    """Generate TI-enhanced angle."""
    r = random.random()
    if r < 0.5:
        while True:
            a = random.uniform(0, 360)
            if random.random() < abs(math.sin(2 * a * math.pi / 180)):
                return a
    elif r < 0.75:
        return random.randint(0, 21) * (180 / SACRED_11)
    else:
        k = random.randint(1, 11)
        return (k * 360 / GOLDEN_RATIO) % 360


def ti_direction() -> float:
    """Generate TI-enhanced direction angle (radians)."""
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


def collides(tree: FastTree, others: List[FastTree], index: Optional[STRtree] = None) -> bool:
    """Check collision using STRtree."""
    if not others:
        return False
    
    polys = [t.polygon for t in others]
    if index is None:
        index = STRtree(polys)
    
    candidates = index.query(tree.polygon)
    for i in candidates:
        if tree.polygon.intersects(polys[i]) and not tree.polygon.touches(polys[i]):
            return True
    return False


def bounding_side(trees: List[FastTree]) -> float:
    """Compute bounding square side length."""
    if not trees:
        return 0.0
    
    polys = [t.polygon for t in trees]
    bounds = unary_union(polys).bounds
    sf = float(SCALE_FACTOR)
    
    width = (bounds[2] - bounds[0]) / sf
    height = (bounds[3] - bounds[1]) / sf
    return max(width, height)


def place_greedy(placed: List[FastTree], attempts: int = 15) -> FastTree:
    """Place new tree using greedy algorithm."""
    if not placed:
        return FastTree(0, 0, ti_angle())
    
    polys = [t.polygon for t in placed]
    index = STRtree(polys)
    
    best_tree = None
    best_r = float('inf')
    
    for _ in range(attempts):
        angle = ti_angle()
        tree = FastTree(0, 0, angle)
        
        direction = ti_direction()
        dx, dy = math.cos(direction), math.sin(direction)
        
        r = 12.0
        step = 0.4
        
        hit = False
        while r > 0:
            tree.move(r * dx, r * dy)
            
            cands = index.query(tree.polygon)
            if any(tree.polygon.intersects(polys[i]) and not tree.polygon.touches(polys[i]) for i in cands):
                hit = True
                break
            r -= step
        
        if hit:
            for _ in range(40):
                r += 0.03
                tree.move(r * dx, r * dy)
                cands = index.query(tree.polygon)
                if not any(tree.polygon.intersects(polys[i]) and not tree.polygon.touches(polys[i]) for i in cands):
                    break
        else:
            r = 0
            tree.move(0, 0)
        
        if r < best_r:
            best_r = r
            best_tree = tree.copy()
    
    return best_tree


def quick_optimize(trees: List[FastTree], iterations: int = 100) -> float:
    """Quick local optimization."""
    if len(trees) <= 1:
        return bounding_side(trees)
    
    current = bounding_side(trees)
    best = current
    
    for _ in range(iterations):
        idx = random.randint(0, len(trees) - 1)
        orig = trees[idx].copy()
        
        others = [t for i, t in enumerate(trees) if i != idx]
        polys = [t.polygon for t in others]
        index = STRtree(polys)
        
        scale = 0.15 * random.random()
        new_x = orig.x + random.gauss(0, scale)
        new_y = orig.y + random.gauss(0, scale)
        new_a = orig.angle + random.gauss(0, 8)
        
        trees[idx].move(new_x, new_y, new_a)
        
        cands = index.query(trees[idx].polygon)
        if any(trees[idx].polygon.intersects(polys[i]) and not trees[idx].polygon.touches(polys[i]) for i in cands):
            trees[idx] = orig
            continue
        
        new_side = bounding_side(trees)
        if new_side < current:
            current = new_side
            if current < best:
                best = current
        else:
            if random.random() < 0.1:
                current = new_side
            else:
                trees[idx] = orig
    
    return best


def solve(max_n: int = 200, optimize_every: int = 5, verbose: bool = True):
    """Main solver."""
    
    trees = []
    total = 0.0
    solutions = []
    
    start = time.time()
    
    for n in range(1, max_n + 1):
        new_tree = place_greedy(trees, attempts=20 if n < 50 else 12)
        trees.append(new_tree)
        
        if n > 1 and n % optimize_every == 0:
            opt_iters = min(50 + n, 150)
            quick_optimize(trees, iterations=opt_iters)
        
        side = bounding_side(trees)
        total += side
        
        for i, t in enumerate(trees):
            if i >= len(solutions) // n * n + n - 1 or len([s for s in solutions if s['n'] == n]) < n:
                pass
        
        for t in trees:
            solutions.append({'n': n, 'x': t.x, 'y': t.y, 'deg': t.angle})
        
        if verbose and n % 20 == 0:
            elapsed = time.time() - start
            print(f"n={n:3d}: side={side:.4f}, total={total:.2f}, time={elapsed:.1f}s")
    
    return total, solutions, trees


def run_full():
    """Run full competition."""
    print("=" * 60)
    print("TI Sigma Speed Solver - Kaggle Santa 2025")
    print("=" * 60)
    
    total, solutions, _ = solve(max_n=200, optimize_every=10, verbose=True)
    
    print(f"\nFinal Score: {total:.2f}")
    print(f"Target: < 68")
    
    return total


if __name__ == "__main__":
    run_full()
