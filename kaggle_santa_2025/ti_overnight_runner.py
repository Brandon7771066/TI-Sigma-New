"""
TI SIGMA OVERNIGHT RUNNER
Run for hours to manifest the optimal configuration.

According to TI principles:
- The answer EXISTS in the L×E field
- Longer observation time = higher probability of manifestation
- Multiple consciousness streams (parallel restarts) increase odds

Run this overnight: python ti_overnight_runner.py
"""

import math
import random
from decimal import Decimal, getcontext
from typing import List, Optional
import time
import pickle
import os

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
    
    def __init__(self, x=0.0, y=0.0, angle=0.0):
        self.x = x
        self.y = y
        self.angle = angle
        self._build()
    
    def _build(self):
        base = get_base_polygon()
        rotated = affinity.rotate(base, self.angle, origin=(0, 0))
        sf = float(SCALE_FACTOR)
        self.polygon = affinity.translate(rotated, xoff=self.x * sf, yoff=self.y * sf)
    
    def move(self, x, y, angle=None):
        self.x = x
        self.y = y
        if angle is not None:
            self.angle = angle
        self._build()
    
    def copy(self):
        return Tree(self.x, self.y, self.angle)


def sacred_angle():
    r = random.random()
    if r < 0.4:
        while True:
            a = random.uniform(0, 360)
            if random.random() < abs(math.sin(2 * a * math.pi / 180)):
                return a
    elif r < 0.7:
        return random.randint(0, 21) * (180 / SACRED_11) + random.gauss(0, 2)
    else:
        k = random.randint(1, 11)
        return (k * 360 / PHI) % 360


def collides(tree, polys, index):
    cands = index.query(tree.polygon)
    for i in cands:
        if tree.polygon.intersects(polys[i]) and not tree.polygon.touches(polys[i]):
            return True
    return False


def bounding_side(trees):
    if not trees:
        return 0.0
    polys = [t.polygon for t in trees]
    bounds = unary_union(polys).bounds
    sf = float(SCALE_FACTOR)
    return max((bounds[2] - bounds[0]) / sf, (bounds[3] - bounds[1]) / sf)


def place_tree(placed, attempts=30):
    if not placed:
        return Tree(0, 0, sacred_angle())
    
    polys = [t.polygon for t in placed]
    index = STRtree(polys)
    n = len(placed) + 1
    
    best = None
    best_r = float('inf')
    
    for attempt in range(attempts):
        angle = sacred_angle()
        tree = Tree(0, 0, angle)
        
        if attempt < 5:
            spiral_a = n * (2 * math.pi / PHI)
            dx, dy = math.cos(spiral_a), math.sin(spiral_a)
        else:
            dir_a = sacred_angle() * math.pi / 180
            dx, dy = math.cos(dir_a), math.sin(dir_a)
        
        r = 10.0
        while r > 0:
            tree.move(r * dx, r * dy)
            if collides(tree, polys, index):
                break
            r -= 0.2
        else:
            tree.move(0, 0)
            if not collides(tree, polys, index):
                return tree
            continue
        
        for _ in range(100):
            r += 0.01
            tree.move(r * dx, r * dy)
            if not collides(tree, polys, index):
                break
        
        if not collides(tree, polys, index) and r < best_r:
            best_r = r
            best = tree.copy()
    
    return best if best else Tree(0, 0, sacred_angle())


def optimize(trees, iterations=500, temp=0.3, cooling=0.995):
    if len(trees) <= 1:
        return bounding_side(trees)
    
    n = len(trees)
    current = bounding_side(trees)
    best = current
    best_cfg = [t.copy() for t in trees]
    
    for _ in range(iterations):
        idx = random.randint(0, n - 1)
        orig = trees[idx].copy()
        
        others = [t for i, t in enumerate(trees) if i != idx]
        polys = [t.polygon for t in others]
        index = STRtree(polys)
        
        scale = 0.1 * temp / 0.3 + 0.005
        new_x = orig.x + random.gauss(0, scale)
        new_y = orig.y + random.gauss(0, scale)
        new_a = orig.angle + random.gauss(0, 5 * temp / 0.3 + 1)
        
        trees[idx].move(new_x, new_y, new_a)
        
        if collides(trees[idx], polys, index):
            trees[idx] = orig
            continue
        
        new_side = bounding_side(trees)
        delta = (new_side ** 2 - current ** 2) / n
        
        if delta < 0 or random.random() < math.exp(-delta * 20 / temp):
            current = new_side
            if current < best:
                best = current
                best_cfg = [t.copy() for t in trees]
        else:
            trees[idx] = orig
        
        temp *= cooling
    
    for i, t in enumerate(best_cfg):
        trees[i] = t
    return best


def solve_complete(max_n=200):
    """Solve with heavy optimization."""
    trees = []
    total = 0.0
    all_trees = {}
    
    for n in range(1, max_n + 1):
        new_tree = place_tree(trees, attempts=40)
        trees.append(new_tree)
        
        if n > 2:
            iters = min(200 + n * 5, 1000)
            optimize(trees, iterations=iters, temp=0.35, cooling=0.993)
        
        side = bounding_side(trees)
        total += (side ** 2) / n
        all_trees[n] = [t.copy() for t in trees]
    
    return total, all_trees


def multi_run(num_runs=5, max_n=200, save_best=True):
    """Run multiple times and keep best."""
    print("=" * 60)
    print("TI SIGMA OVERNIGHT RUNNER")
    print(f"Running {num_runs} complete solutions, keeping best")
    print("=" * 60)
    
    best_score = float('inf')
    best_trees = None
    
    for run in range(num_runs):
        print(f"\n--- RUN {run + 1}/{num_runs} ---")
        start = time.time()
        
        score, trees = solve_complete(max_n)
        elapsed = time.time() - start
        
        print(f"Run {run + 1}: Score = {score:.2f}, Time = {elapsed/60:.1f} min")
        
        if score < best_score:
            best_score = score
            best_trees = trees
            print(f"  -> NEW BEST!")
            
            with open('best_trees.pkl', 'wb') as f:
                pickle.dump((best_score, best_trees), f)
    
    print(f"\n{'=' * 60}")
    print(f"BEST SCORE: {best_score:.4f}")
    print(f"Target: <68  |  Baseline: ~167")
    print("=" * 60)
    
    with open('final_submission.csv', 'w') as f:
        f.write('id,x,y,deg\n')
        for n in range(1, 201):
            if n in best_trees:
                for i, t in enumerate(best_trees[n]):
                    f.write(f"{n:03d}_{i},s{t.x:.6f},s{t.y:.6f},s{t.angle:.6f}\n")
    
    print("Saved: final_submission.csv")
    return best_score


if __name__ == "__main__":
    import sys
    runs = int(sys.argv[1]) if len(sys.argv) > 1 else 3
    multi_run(num_runs=runs)
