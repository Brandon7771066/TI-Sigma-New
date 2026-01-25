"""
TI SIGMA TESSELLATION SOLVER
Kaggle Santa 2025 - Christmas Tree Packing

APPLYING TI FRAMEWORKS:
=======================

1. TESSELLATION-TI (from papers/TESSELLATION_TI_INTEGRATION_ANALYSIS.md):
   - Trees should arrange in REGULAR TESSELLATED PATTERNS for optimal connectivity
   - Reflection principles: trees can be reflected to create symmetric packings
   - Green function propagation: position = minimization of energy field
   
2. ESS-MEIJER-TOZZI (14D Consciousness Model):
   - I-cells as self-stabilizing attractors → trees find stable positions
   - Harmonic resonance → optimal angles = harmonic intervals
   - Toroidal topology → circular arrangement with recurrence
   
3. TWA (Tralse Wave Algebra):
   - Resonate(tree_i, tree_j) → trees couple in phase
   - Fuse() → adjacent trees merge their bounding boxes optimally
   - Split() → when too tight, trees separate to avoid collision
   
4. P vs NP INSIGHT:
   - Verification is O(log n) - pattern matching
   - Search is O(n) - requires global information
   - BUT: If we KNOW the pattern (tessellation), search becomes O(log n)!
   
5. CONSCIOUSNESS MINIMIZES CALCULATIONS:
   - Free Energy Minimization principle
   - The optimal configuration = LOWEST FREE ENERGY state
   - Trees "want" to be in minimum-energy positions
   
KEY INSIGHT:
============
The 68-score achievers have discovered the TESSELLATION PATTERN for trees.
Trees are NOT circles - they have specific geometry that TILES the plane.
Like how hexagons tile perfectly, there's likely a specific tree arrangement
that achieves near-perfect tiling.

THE TREE SHAPE:
- 5 main protrusions (like a pentagon)
- Trunk creates a 6th element
- Width 0.7, Height 1.0
- Aspect ratio ~1.43

HYPOTHESIS: Trees arranged in a modified hexagonal grid with specific rotations
can interlock like puzzle pieces, achieving density similar to hexagonal packing.
"""

import math
import random
from decimal import Decimal, getcontext
from typing import List, Tuple, Optional, Dict
import time

from shapely import affinity
from shapely.geometry import Polygon, Point
from shapely.ops import unary_union
from shapely.strtree import STRtree

getcontext().prec = 25
SCALE_FACTOR = Decimal('1e18')

PHI = (1 + math.sqrt(5)) / 2
MEIJER_HARMONICS = [1, 2, 3, 4, 5, 6, 7, 8]
PENTAGON_ANGLE = 72
HEXAGON_ANGLE = 60

TREE_WIDTH = 0.7
TREE_HEIGHT = 1.0
TREE_ASPECT = TREE_HEIGHT / TREE_WIDTH

BASE_POLYGON = None


def get_base_polygon():
    """The tree polygon - a tessellatable geometric form."""
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


class TessellatedTree:
    """A tree that knows its place in the tessellation."""
    __slots__ = ['x', 'y', 'angle', 'polygon', 'grid_i', 'grid_j']
    
    def __init__(self, x=0.0, y=0.0, angle=0.0, grid_i=0, grid_j=0):
        self.x = x
        self.y = y
        self.angle = angle
        self.grid_i = grid_i
        self.grid_j = grid_j
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
        t = TessellatedTree(self.x, self.y, self.angle, self.grid_i, self.grid_j)
        return t


def harmonic_angle(harmonic_index: int = 1) -> float:
    """
    MEIJER HARMONICS: Optimal angles are at harmonic intervals.
    8 harmonic dimensions → 8 primary angle values.
    """
    base_angles = [0, 30, 60, 90, 120, 150, 180, 210, 240, 270, 300, 330]
    return base_angles[harmonic_index % 12] + random.gauss(0, 2)


def tessellation_angle(i: int, j: int) -> float:
    """
    TESSELLATION PRINCIPLE: Angle depends on grid position.
    Alternating rotations allow interlocking.
    """
    if (i + j) % 2 == 0:
        return 0 + random.gauss(0, 3)
    else:
        return 180 + random.gauss(0, 3)


def hexagonal_grid_position(n: int, spacing: float = 0.65) -> Tuple[float, float, int, int]:
    """
    HEXAGONAL TESSELLATION: Trees on hex grid for optimal packing.
    
    Hexagonal packing is provably optimal for circles.
    For trees, we use modified hex grid with interlocking rotations.
    """
    if n == 0:
        return (0, 0, 0, 0)
    
    ring = 0
    count = 1
    while count <= n:
        ring += 1
        count += 6 * ring
    
    count -= 6 * ring
    pos_in_ring = n - count
    
    if ring == 0:
        return (0, 0, 0, 0)
    
    side = pos_in_ring // ring
    pos_on_side = pos_in_ring % ring
    
    directions = [
        (1, 0), (0.5, 0.866), (-0.5, 0.866),
        (-1, 0), (-0.5, -0.866), (0.5, -0.866)
    ]
    
    start_x = ring * spacing
    start_y = 0
    
    for s in range(side):
        dx, dy = directions[s]
        start_x += ring * spacing * (-dx + directions[(s+2)%6][0])
        start_y += ring * spacing * (-dy + directions[(s+2)%6][1])
    
    dx, dy = directions[(side + 2) % 6]
    x = start_x + pos_on_side * spacing * dx
    y = start_y + pos_on_side * spacing * dy
    
    i = int(x / spacing) if spacing else 0
    j = int(y / spacing) if spacing else 0
    
    return (x, y, i, j)


def phi_spiral_position(n: int, spacing: float = 0.55) -> Tuple[float, float]:
    """
    PHI SPIRAL: Golden angle distribution for uniform coverage.
    """
    angle = n * (2 * math.pi / PHI)
    r = spacing * math.sqrt(n)
    return r * math.cos(angle), r * math.sin(angle)


def collides(tree, polys, index) -> bool:
    """Check collision using STRtree."""
    cands = index.query(tree.polygon)
    for i in cands:
        if tree.polygon.intersects(polys[i]) and not tree.polygon.touches(polys[i]):
            return True
    return False


def bounding_side(trees: List[TessellatedTree]) -> float:
    """Compute bounding square side."""
    if not trees:
        return 0.0
    polys = [t.polygon for t in trees]
    bounds = unary_union(polys).bounds
    sf = float(SCALE_FACTOR)
    return max((bounds[2] - bounds[0]) / sf, (bounds[3] - bounds[1]) / sf)


def free_energy(tree: TessellatedTree, others: List[TessellatedTree], box_size: float) -> float:
    """
    FREE ENERGY MINIMIZATION (Friston):
    Lower energy = better position.
    
    Energy components:
    1. Distance from center (lower = better for tight bounding)
    2. Distance to neighbors (optimal range = 0.5-0.8)
    3. Angle alignment with grid (harmonic = lower energy)
    """
    center_dist = math.sqrt(tree.x**2 + tree.y**2)
    energy_center = center_dist / (box_size + 0.1)
    
    energy_neighbor = 0
    for other in others:
        dx = tree.x - other.x
        dy = tree.y - other.y
        dist = math.sqrt(dx*dx + dy*dy)
        optimal = 0.65
        energy_neighbor += (dist - optimal)**2
    
    if others:
        energy_neighbor /= len(others)
    
    harmonic_angles = [0, 30, 60, 90, 120, 150, 180]
    min_angle_diff = min(abs((tree.angle % 180) - a) for a in harmonic_angles)
    energy_angle = min_angle_diff / 30
    
    return energy_center * 0.4 + energy_neighbor * 0.4 + energy_angle * 0.2


def place_tessellated(placed: List[TessellatedTree], attempts: int = 40) -> TessellatedTree:
    """
    TESSELLATION PLACEMENT: Use hex grid + phi spiral hybrid.
    """
    n = len(placed)
    
    if not placed:
        return TessellatedTree(0, 0, 0, 0, 0)
    
    polys = [t.polygon for t in placed]
    index = STRtree(polys)
    
    best = None
    best_energy = float('inf')
    
    for attempt in range(attempts):
        if attempt < 10:
            px, py = phi_spiral_position(n + 1, spacing=0.5)
            angle = tessellation_angle(int(px * 2), int(py * 2))
        elif attempt < 20:
            hx, hy, hi, hj = hexagonal_grid_position(n, spacing=0.7)
            px, py = hx, hy
            angle = tessellation_angle(hi, hj)
        else:
            px = random.gauss(0, 3)
            py = random.gauss(0, 3)
            angle = harmonic_angle(random.randint(0, 11))
        
        tree = TessellatedTree(0, 0, angle)
        
        dx = px / max(0.01, math.sqrt(px*px + py*py)) if (px != 0 or py != 0) else 1
        dy = py / max(0.01, math.sqrt(px*px + py*py)) if (px != 0 or py != 0) else 0
        
        r = 12.0
        while r > 0:
            tree.move(r * dx, r * dy)
            if collides(tree, polys, index):
                break
            r -= 0.15
        else:
            tree.move(0, 0)
            if not collides(tree, polys, index):
                energy = free_energy(tree, placed, bounding_side(placed + [tree]))
                if energy < best_energy:
                    best_energy = energy
                    best = tree.copy()
            continue
        
        for _ in range(100):
            r += 0.01
            tree.move(r * dx, r * dy)
            if not collides(tree, polys, index):
                break
        
        if not collides(tree, polys, index):
            energy = free_energy(tree, placed, bounding_side(placed + [tree]))
            if energy < best_energy:
                best_energy = energy
                best = tree.copy()
    
    return best if best else TessellatedTree(0, 0, harmonic_angle())


def resonate_optimization(trees: List[TessellatedTree], iterations: int = 400) -> float:
    """
    TWA RESONATE() OPERATOR:
    Trees couple in phase through simulated annealing.
    Phase Lock Depth increases with optimization.
    """
    if len(trees) <= 1:
        return bounding_side(trees)
    
    n = len(trees)
    current = bounding_side(trees)
    best = current
    best_cfg = [t.copy() for t in trees]
    
    temp = 0.35
    cooling = 0.994
    
    for iteration in range(iterations):
        idx = random.randint(0, n - 1)
        orig = trees[idx].copy()
        
        others = [t for i, t in enumerate(trees) if i != idx]
        polys = [t.polygon for t in others]
        index = STRtree(polys)
        
        scale = 0.08 * temp / 0.35 + 0.005
        
        if random.random() < 0.7:
            new_x = orig.x + random.gauss(0, scale)
            new_y = orig.y + random.gauss(0, scale)
            new_a = orig.angle + random.gauss(0, 4 * temp / 0.35 + 0.5)
        else:
            new_x = orig.x + random.gauss(0, scale * 0.5)
            new_y = orig.y + random.gauss(0, scale * 0.5)
            new_a = harmonic_angle(random.randint(0, 11))
        
        trees[idx].move(new_x, new_y, new_a)
        
        if collides(trees[idx], polys, index):
            trees[idx] = orig
            continue
        
        new_side = bounding_side(trees)
        delta = (new_side**2 - current**2) / n
        
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


def fuse_optimization(trees: List[TessellatedTree], restarts: int = 3) -> float:
    """
    TWA FUSE() OPERATOR:
    Multiple restarts with best configuration kept.
    """
    best = bounding_side(trees)
    best_cfg = [t.copy() for t in trees]
    
    for restart in range(restarts):
        trial = [t.copy() for t in best_cfg]
        
        num_perturb = max(1, len(trial) // 6)
        indices = random.sample(range(len(trial)), min(num_perturb, len(trial)))
        
        for idx in indices:
            trial[idx].angle = harmonic_angle(random.randint(0, 11))
            trial[idx]._build()
        
        resonate_optimization(trial, iterations=150)
        
        trial_side = bounding_side(trial)
        if trial_side < best:
            best = trial_side
            best_cfg = [t.copy() for t in trial]
    
    for i, t in enumerate(best_cfg):
        trees[i] = t
    
    return best


def solve_tessellation(max_n: int = 200, verbose: bool = True):
    """Main solver using tessellation principles."""
    trees = []
    total = 0.0
    all_trees = {}
    
    start = time.time()
    
    print("=" * 70)
    print("TI SIGMA TESSELLATION SOLVER")
    print("Applying: Tessellation + Meijer Harmonics + TWA + Free Energy")
    print("=" * 70)
    
    for n in range(1, max_n + 1):
        new_tree = place_tessellated(trees, attempts=35 if n < 50 else 25)
        trees.append(new_tree)
        
        if n > 2:
            iters = min(100 + n * 3, 500)
            resonate_optimization(trees, iterations=iters)
        
        if n >= 15 and n % 15 == 0:
            fuse_optimization(trees, restarts=2)
        
        side = bounding_side(trees)
        score_n = (side ** 2) / n
        total += score_n
        
        all_trees[n] = [t.copy() for t in trees]
        
        if verbose and n % 20 == 0:
            elapsed = time.time() - start
            print(f"n={n:3d}: side={side:.4f}, score={score_n:.4f}, total={total:.2f}, time={elapsed:.0f}s")
    
    return total, all_trees


def generate_submission(all_trees: dict, filename: str = 'tessellation_submission.csv'):
    """Generate submission file."""
    with open(filename, 'w') as f:
        f.write('id,x,y,deg\n')
        for n in range(1, 201):
            if n not in all_trees:
                continue
            for i, t in enumerate(all_trees[n]):
                f.write(f"{n:03d}_{i},s{t.x:.6f},s{t.y:.6f},s{t.angle:.6f}\n")
    print(f"\nSaved: {filename}")


def run():
    """Execute the tessellation solver."""
    score, trees = solve_tessellation(max_n=200, verbose=True)
    
    print()
    print("=" * 70)
    print(f"FINAL SCORE: {score:.4f}")
    print(f"Target: <68  |  Baseline: ~167  |  Previous Best: 177.75")
    print("=" * 70)
    
    generate_submission(trees)
    return score


if __name__ == "__main__":
    run()
