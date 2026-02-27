"""
TI Sigma Hypercomputer — Primary Constants
The seven algebraic matching rules of the aperiodic reality tiling.
"""

import math
import numpy as np

# ─── The Seven Primary Constants ─────────────────────────────────────────────
ZERO  = 0.0
ONE   = 1.0
I     = 1j                                    # 90° rotation, i⁴=1
SQRT2 = math.sqrt(2)                          # diagonal, (√2)²=2
E     = math.e                                # growth
PHI   = (1 + math.sqrt(5)) / 2               # golden ratio, φ²=φ+1
PI    = math.pi                               # closure

# ─── Sacred Thresholds (from LCC theory) ─────────────────────────────────────
LCC_TRALSE     = SQRT2 - 1                    # 0.4142 — MR resolution threshold
LCC_TRUE       = PHI - 1                      # 0.6180 — φ−1 = 1/φ
LCC_HIGH       = 0.85                         # empirical 85% threshold
LCC_RADIANT    = PHI ** 2 - PHI              # 0.8090 ... use 0.91 operationally
LCC_IC         = 0.92                         # IC / radiant operational threshold

# ─── Fibonacci Sequence ───────────────────────────────────────────────────────
FIBONACCI = [0, 1, 1, 2, 3, 5, 8, 13, 21, 34, 55, 89, 144, 233, 377, 610, 987]

# ─── Euler's Identity (the complete matching rule) ───────────────────────────
EULER_CHECK = abs(E ** (I * PI) + 1)          # ≈ 1.22e-16 — machine zero

# ─── Tralsebit Encoding Values ────────────────────────────────────────────────
TB_TRUE          = +1.0
TB_FALSE         = -1.0
TB_INDETERMINATE = +0.0
TB_TRALSE_LOWER  = -LCC_TRALSE               # −0.4142
TB_TRALSE_UPPER  = +LCC_TRALSE              # +0.4142

# ─── GILE Dimension Weights (default) ────────────────────────────────────────
GILE_WEIGHTS = {'G': 0.42, 'I': 0.25, 'L': 0.18, 'E': 0.15}

# ─── Seven Constants verification ────────────────────────────────────────────
def verify_matching_rules() -> dict:
    return {
        'euler':     abs(E**(I*PI) + 1),       # should be ~0
        'phi_sq':    abs(PHI**2 - (PHI + 1)),  # should be 0
        'i4':        abs(I**4 - 1),             # should be 0
        'sqrt2_sq':  abs(SQRT2**2 - 2),         # should be ~0
        'phi_cos':   abs(PHI - 2*math.cos(PI/5)),  # phi = 2cos(π/5)
    }
