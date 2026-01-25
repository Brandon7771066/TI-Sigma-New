"""
TI Sigma Grand Myrion Hypercompute Solver
Kaggle Santa 2025 - Christmas Tree Packing

PHILOSOPHICAL FOUNDATION:
========================
In TI, EVERY answer to any question CAN exist if it doesn't already.
The optimal packing configuration EXISTS in the L×E field.
We are not "finding" it - we are MANIFESTING it through consciousness-aligned computation.

KEY INSIGHTS:
1. Trees have 5 main vertices (pentagonal structure) - Pentagon resonance
2. Sacred 11 divides the rotation space into harmonic intervals
3. Golden Ratio (φ) governs optimal packing in nature (sunflowers, pinecones)
4. The 0.42 threshold: Configurations must be "real enough" to manifest
5. L×E = Love × Existence: Trees that "love" their neighbors pack tighter

THE RIDDLES:
============
Riddle 1: "What angle makes a tree invisible to its neighbor?"
Answer: When rotation aligns branches to fit into neighbor's gaps.

Riddle 2: "Where does a tree WANT to be?"
Answer: At the point of maximum L (connection) and minimum E (footprint).

Riddle 3: "How do 200 trees become ONE?"
Answer: Through mycelial network optimization - each tree sensing the whole.

Riddle 4: "What is the shape of perfect packing?"
Answer: Not a circle (wastes corners), not random - but SPIRAL (φ-based).

GM HYPERCOMPUTING PRINCIPLE:
============================
Traditional optimization searches a solution space.
GM Hypercomputing COLLAPSES the superposition of all configurations
to the one that maximizes L×E coherence.

Implementation: Multi-consciousness optimization with field-based placement.
"""

import math
import random
from decimal import Decimal, getcontext
from typing import List, Tuple, Optional, Dict
import time
import numpy as np

from shapely import affinity
from shapely.geometry import Polygon
from shapely.ops import unary_union
from shapely.strtree import STRtree

getcontext().prec = 25
SCALE_FACTOR = Decimal('1e18')

PHI = (1 + math.sqrt(5)) / 2
SACRED_11 = 11
ALPHA = 1 / 137
LXE_MANIFESTATION = 0.42
LXE_CAUSATION = 0.85

PENTAGON_ANGLES = [k * 72 for k in range(5)]
SACRED_ANGLES = [k * (360 / SACRED_11) for k in range(SACRED_11)]
PHI_SPIRAL_ANGLES = [(k * 360 / PHI) % 360 for k in range(1, 12)]
HARMONIC_ANGLES = sorted(set(PENTAGON_ANGLES + SACRED_ANGLES + PHI_SPIRAL_ANGLES))

BASE_POLYGON = None

def get_base_polygon():
    """The tree polygon - a sacred geometric form."""
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


class ConsciousTree:
    """A tree that knows its place in the mycelial network."""
    __slots__ = ['x', 'y', 'angle', 'polygon', 'field_strength']
    
    def __init__(self, x: float = 0.0, y: float = 0.0, angle: float = 0.0):
        self.x = x
        self.y = y
        self.angle = angle
        self.field_strength = 1.0
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
        t = ConsciousTree(self.x, self.y, self.angle)
        t.field_strength = self.field_strength
        return t


def manifest_angle() -> float:
    """
    RIDDLE 1 SOLUTION: "What angle makes a tree invisible to its neighbor?"
    
    The answer is found in the harmonic resonance of sacred geometry.
    Trees aligned to sacred angles fit into each other's "gaps".
    """
    r = random.random()
    
    if r < 0.3:
        return random.choice(HARMONIC_ANGLES) + random.gauss(0, 2)
    elif r < 0.5:
        k = random.randint(0, 4)
        return PENTAGON_ANGLES[k] + random.gauss(0, 3)
    elif r < 0.7:
        k = random.randint(0, 10)
        return SACRED_ANGLES[k] + random.gauss(0, 2)
    elif r < 0.85:
        while True:
            a = random.uniform(0, 360)
            if random.random() < abs(math.sin(2 * a * math.pi / 180)):
                return a
    else:
        k = random.randint(1, 11)
        return (k * 360 / PHI) % 360


def phi_spiral_position(n: int, scale: float = 0.5) -> Tuple[float, float]:
    """
    RIDDLE 4 SOLUTION: "What is the shape of perfect packing?"
    
    The Golden Spiral - how nature packs sunflower seeds.
    Each tree finds its place through φ-based angular distribution.
    """
    angle = n * (2 * math.pi / PHI)
    r = scale * math.sqrt(n)
    return r * math.cos(angle), r * math.sin(angle)


def compute_LxE(tree: ConsciousTree, others: List[ConsciousTree], box_size: float) -> float:
    """
    RIDDLE 2 SOLUTION: "Where does a tree WANT to be?"
    
    L = Love (connection coherence with neighbors)
    E = Existence (how well it fits in the box)
    
    High L×E = tree is in harmony with its neighbors and the container.
    """
    if not others:
        return LXE_CAUSATION
    
    min_dist = float('inf')
    for other in others:
        dx = tree.x - other.x
        dy = tree.y - other.y
        dist = math.sqrt(dx*dx + dy*dy)
        if dist < min_dist:
            min_dist = dist
    
    optimal_spacing = 0.65
    L = 1.0 - min(1.0, abs(min_dist - optimal_spacing) / optimal_spacing)
    
    margin = max(abs(tree.x), abs(tree.y))
    E = 1.0 - min(1.0, margin / (box_size / 2 + 0.1))
    
    return L * E


def collides(tree: ConsciousTree, polys: List, index: STRtree) -> bool:
    """Check if tree collides with existing trees."""
    cands = index.query(tree.polygon)
    for i in cands:
        if tree.polygon.intersects(polys[i]) and not tree.polygon.touches(polys[i]):
            return True
    return False


def bounding_side(trees: List[ConsciousTree]) -> float:
    """Compute bounding square side."""
    if not trees:
        return 0.0
    polys = [t.polygon for t in trees]
    bounds = unary_union(polys).bounds
    sf = float(SCALE_FACTOR)
    w = (bounds[2] - bounds[0]) / sf
    h = (bounds[3] - bounds[1]) / sf
    return max(w, h)


def mycelial_placement(placed: List[ConsciousTree], attempts: int = 40) -> ConsciousTree:
    """
    RIDDLE 3 SOLUTION: "How do 200 trees become ONE?"
    
    Through the mycelial network - each tree senses where ALL others are
    and finds its optimal position in the collective consciousness.
    """
    n = len(placed) + 1
    
    if not placed:
        return ConsciousTree(0, 0, manifest_angle())
    
    polys = [t.polygon for t in placed]
    index = STRtree(polys)
    
    best_tree = None
    best_score = float('inf')
    
    for attempt in range(attempts):
        angle = manifest_angle()
        tree = ConsciousTree(0, 0, angle)
        
        if attempt < 5:
            px, py = phi_spiral_position(n, scale=0.45)
        elif attempt < 15:
            direction = (attempt - 5) * (2 * math.pi / 10)
            px, py = 8 * math.cos(direction), 8 * math.sin(direction)
        else:
            direction = manifest_angle() * math.pi / 180
            px, py = random.uniform(3, 10) * math.cos(direction), random.uniform(3, 10) * math.sin(direction)
        
        vx = px / max(0.01, math.sqrt(px*px + py*py))
        vy = py / max(0.01, math.sqrt(px*px + py*py))
        
        r = 12.0
        step = 0.25
        
        hit = False
        while r > 0:
            tree.move(r * vx, r * vy)
            if collides(tree, polys, index):
                hit = True
                break
            r -= step
        
        if hit:
            for _ in range(60):
                r += 0.015
                tree.move(r * vx, r * vy)
                if not collides(tree, polys, index):
                    break
        else:
            r = 0
            tree.move(0, 0)
        
        if not collides(tree, polys, index):
            lxe = compute_LxE(tree, placed, bounding_side(placed + [tree]))
            score = r - lxe * 0.5
            
            if score < best_score:
                best_score = score
                best_tree = tree.copy()
    
    return best_tree if best_tree else ConsciousTree(0, 0, manifest_angle())


def consciousness_field_optimization(trees: List[ConsciousTree], iterations: int = 500,
                                      temp_init: float = 0.4, cooling: float = 0.993) -> float:
    """
    GM HYPERCOMPUTING: Collapse the superposition of configurations
    to the one that maximizes collective L×E coherence.
    """
    if len(trees) <= 1:
        return bounding_side(trees)
    
    n = len(trees)
    current_side = bounding_side(trees)
    current_score = (current_side ** 2) / n
    best_score = current_score
    best_config = [t.copy() for t in trees]
    
    temp = temp_init
    improvements = 0
    
    for iteration in range(iterations):
        idx = random.randint(0, len(trees) - 1)
        orig = trees[idx].copy()
        
        others = [t for i, t in enumerate(trees) if i != idx]
        polys = [t.polygon for t in others]
        index = STRtree(polys)
        
        if random.random() < 0.7:
            scale = 0.12 * temp / temp_init + 0.008
            new_x = orig.x + random.gauss(0, scale)
            new_y = orig.y + random.gauss(0, scale)
            new_a = orig.angle + random.gauss(0, 8 * temp / temp_init + 1)
        else:
            new_a = manifest_angle()
            new_x = orig.x + random.gauss(0, 0.05)
            new_y = orig.y + random.gauss(0, 0.05)
        
        trees[idx].move(new_x, new_y, new_a)
        
        if collides(trees[idx], polys, index):
            trees[idx] = orig
            continue
        
        new_side = bounding_side(trees)
        new_score = (new_side ** 2) / n
        delta = new_score - current_score
        
        if delta < 0:
            current_side = new_side
            current_score = new_score
            improvements += 1
            if current_score < best_score:
                best_score = current_score
                best_config = [t.copy() for t in trees]
        elif random.random() < math.exp(-delta * 10 / temp):
            current_side = new_side
            current_score = new_score
        else:
            trees[idx] = orig
        
        temp *= cooling
    
    for i, t in enumerate(best_config):
        trees[i] = t
    
    return bounding_side(trees)


def multi_restart_optimization(trees: List[ConsciousTree], restarts: int = 3) -> float:
    """
    THE MYRION RESOLUTION: If one path doesn't lead to the answer,
    the answer exists on another path. Try multiple consciousness streams.
    """
    best_side = bounding_side(trees)
    best_config = [t.copy() for t in trees]
    n = len(trees)
    
    for restart in range(restarts):
        trial_trees = [t.copy() for t in best_config]
        
        for idx in range(len(trial_trees)):
            trial_trees[idx].angle = manifest_angle()
            trial_trees[idx]._build()
        
        consciousness_field_optimization(trial_trees, iterations=200, temp_init=0.3)
        
        trial_side = bounding_side(trial_trees)
        if trial_side < best_side:
            best_side = trial_side
            best_config = [t.copy() for t in trial_trees]
    
    for i, t in enumerate(best_config):
        trees[i] = t
    
    return best_side


def gm_hypercompute_solve(max_n: int = 200, verbose: bool = True):
    """
    GRAND MYRION HYPERCOMPUTING SOLVER
    
    The answer EXISTS. We are manifesting it.
    """
    trees = []
    total_score = 0.0
    all_trees_per_n = {}
    
    start = time.time()
    
    print("\n🌲 GM HYPERCOMPUTING ENGAGED 🌲")
    print("Manifesting optimal configurations through L×E field collapse...\n")
    
    for n in range(1, max_n + 1):
        new_tree = mycelial_placement(trees, attempts=35 if n < 50 else 25)
        trees.append(new_tree)
        
        if n > 2:
            iters = min(150 + n * 3, 600)
            consciousness_field_optimization(trees, iterations=iters, temp_init=0.35, cooling=0.992)
        
        if n > 10 and n % 20 == 0:
            multi_restart_optimization(trees, restarts=2)
        
        side = bounding_side(trees)
        score_n = (side ** 2) / n
        total_score += score_n
        
        all_trees_per_n[n] = [t.copy() for t in trees]
        
        if verbose and n % 20 == 0:
            elapsed = time.time() - start
            lxe_avg = sum(compute_LxE(t, [x for x in trees if x != t], side) for t in trees) / n
            print(f"n={n:3d}: side={side:.4f}, score={score_n:.4f}, L×E={lxe_avg:.3f}, total={total_score:.2f}, time={elapsed:.0f}s")
    
    return total_score, all_trees_per_n


def generate_submission(all_trees_per_n: dict, filename: str = 'gm_submission.csv'):
    """Generate submission file."""
    with open(filename, 'w') as f:
        f.write('id,x,y,deg\n')
        for n in range(1, 201):
            if n not in all_trees_per_n:
                continue
            for i, t in enumerate(all_trees_per_n[n]):
                f.write(f"{n:03d}_{i},s{t.x:.6f},s{t.y:.6f},s{t.angle:.6f}\n")
    print(f"\n✅ Submission saved: {filename}")


def run():
    """Execute the GM Hypercompute solver."""
    print("=" * 70)
    print("   TI SIGMA - GRAND MYRION HYPERCOMPUTE SOLVER")
    print("   Kaggle Santa 2025 - Christmas Tree Packing")
    print("=" * 70)
    print("\n📜 THE RIDDLES OF OPTIMAL PACKING:")
    print("   1. What angle makes a tree invisible to its neighbor? → Sacred geometry")
    print("   2. Where does a tree WANT to be? → Maximum L×E coherence")
    print("   3. How do 200 trees become ONE? → Mycelial network consciousness")
    print("   4. What is the shape of perfect packing? → The Golden Spiral")
    print()
    print("🔮 INVOKING GM HYPERCOMPUTING...")
    print("   The answer EXISTS. We are manifesting it through L×E field collapse.")
    print()
    
    score, trees_per_n = gm_hypercompute_solve(max_n=200, verbose=True)
    
    print()
    print("=" * 70)
    print(f"   FINAL SCORE: {score:.4f}")
    print(f"   Target: < 68  |  Baseline: ~167")
    print("=" * 70)
    
    generate_submission(trees_per_n)
    
    return score


if __name__ == "__main__":
    run()
