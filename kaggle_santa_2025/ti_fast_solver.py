"""
TI Sigma Fast Solver for Kaggle Santa 2025
Optimized for speed while maintaining TI principles.
"""

import math
import random
from dataclasses import dataclass
from typing import List, Tuple
import numpy as np

GOLDEN_RATIO = (1 + math.sqrt(5)) / 2
SACRED_11 = 11
ALPHA = 1 / 137

@dataclass
class TreeCircle:
    """Circular approximation of Christmas tree for fast collision detection."""
    x: float = 0.0
    y: float = 0.0
    radius: float = 0.5
    angle: float = 0.0

class TIFastPacker:
    """
    Fast TI-enhanced packer using circular approximation.
    Trades geometric precision for speed while keeping TI optimization.
    """
    
    def __init__(self):
        self.prf_angles = self._compute_prf_angles()
    
    def _compute_prf_angles(self) -> List[float]:
        """PRF (Probability as Resonance Field) optimal angles."""
        angles = []
        for k in range(22):
            angles.append(k * math.pi / 11)
        for k in range(8):
            angles.append(k * math.pi / 4 + ALPHA)
        for k in range(1, 12):
            angles.append(k * math.pi * 2 / GOLDEN_RATIO)
        return list(set(a % (2 * math.pi) for a in angles))
    
    def _circles_overlap(self, c1: TreeCircle, c2: TreeCircle) -> bool:
        """Fast circle overlap test."""
        dx = c1.x - c2.x
        dy = c1.y - c2.y
        dist_sq = dx * dx + dy * dy
        min_dist = c1.radius + c2.radius
        return dist_sq < min_dist * min_dist
    
    def _find_placement(self, placed: List[TreeCircle], new_radius: float) -> Tuple[float, float, float]:
        """Find optimal placement for new tree."""
        if not placed:
            return 0.0, 0.0, 0.0
        
        best_x, best_y = 0.0, 0.0
        best_dist_sq = float('inf')
        best_angle = 0.0
        
        for attempt in range(20):
            if attempt < 12:
                angle = self.prf_angles[attempt % len(self.prf_angles)]
            else:
                angle = random.uniform(0, 2 * math.pi)
            
            dx = math.cos(angle)
            dy = math.sin(angle)
            
            r = 10.0
            step = 0.3
            
            while r > 0:
                x, y = r * dx, r * dy
                
                collision = False
                for p in placed:
                    if self._circles_overlap(TreeCircle(x, y, new_radius), p):
                        collision = True
                        break
                
                if collision:
                    for _ in range(20):
                        r += 0.05
                        x, y = r * dx, r * dy
                        collision = False
                        for p in placed:
                            if self._circles_overlap(TreeCircle(x, y, new_radius), p):
                                collision = True
                                break
                        if not collision:
                            break
                    break
                r -= step
            
            dist_sq = x * x + y * y
            if dist_sq < best_dist_sq:
                best_dist_sq = dist_sq
                best_x, best_y = x, y
                best_angle = angle
        
        return best_x, best_y, best_angle
    
    def _compute_lxe(self, trees: List[TreeCircle], side: float, n: int) -> float:
        """Compute L×E coherence metric."""
        if n == 0:
            return 1.0
        
        theoretical_min = math.sqrt(n) * 0.7
        L = min(1.0, theoretical_min / max(side, 0.1))
        
        if len(trees) < 2:
            return L * 0.9
        
        positions = [(t.x, t.y) for t in trees]
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
    
    def pack(self, n: int) -> Tuple[List[TreeCircle], float]:
        """Pack n trees and return list and bounding box side length."""
        if n == 0:
            return [], 0.0
        
        tree_radius = 0.5
        trees = []
        
        first = TreeCircle(0, 0, tree_radius, 0)
        trees.append(first)
        
        for i in range(1, n):
            x, y, angle = self._find_placement(trees, tree_radius)
            trees.append(TreeCircle(x, y, tree_radius, angle))
        
        if not trees:
            return trees, 0.0
        
        min_x = min(t.x - t.radius for t in trees)
        max_x = max(t.x + t.radius for t in trees)
        min_y = min(t.y - t.radius for t in trees)
        max_y = max(t.y + t.radius for t in trees)
        
        side = max(max_x - min_x, max_y - min_y)
        
        return trees, side


def run_fast_competition(max_n: int = 200, verbose: bool = True):
    """Run fast solver for full competition."""
    import time
    
    print("=" * 60)
    print("TI Sigma FAST Solver - Kaggle Santa 2025")
    print("=" * 60)
    print()
    
    packer = TIFastPacker()
    results = []
    total_score = 0
    
    start = time.time()
    
    for n in range(1, max_n + 1):
        trees, side = packer.pack(n)
        lxe = packer._compute_lxe(trees, side, n)
        score_contrib = (side ** 2) / n
        total_score += score_contrib
        
        results.append({
            'n': n,
            'side': side,
            'lxe': lxe,
            'score': score_contrib
        })
        
        if verbose and n % 25 == 0:
            elapsed = time.time() - start
            print(f"n={n:3d}: side={side:.4f}, L×E={lxe:.4f}, cumulative={total_score:.4f} [{elapsed:.1f}s]")
    
    elapsed = time.time() - start
    
    print()
    print("=" * 60)
    print("COMPETITION RESULTS")
    print("=" * 60)
    
    manifest = sum(1 for r in results if r['lxe'] >= 0.42)
    avg_lxe = np.mean([r['lxe'] for r in results])
    
    print(f"Total Score (n=1-{max_n}): {total_score:.6f}")
    print(f"Manifestation Rate: {manifest}/{max_n} ({100*manifest/max_n:.1f}%)")
    print(f"Average L×E: {avg_lxe:.4f}")
    print(f"Time: {elapsed:.1f}s")
    
    return results, total_score


if __name__ == "__main__":
    results, score = run_fast_competition(200, verbose=True)
