import numpy as np

PHI   = (1 + np.sqrt(5)) / 2       # Golden ratio  ≈ 1.6180
C_TI  = 1 / (PHI * np.sqrt(2))     # TI constant C ≈ 0.4370
T_TI  = 1 - np.exp(-np.e)          # TI threshold T ≈ 0.9340
ET    = np.sqrt(2) - 1              # Coherence threshold ET ≈ 0.4142
E_TI  = np.e                        # Euler's number ≈ 2.7183
PI_TI = np.pi                       # Pi ≈ 3.1416
SQRT2 = np.sqrt(2)                  # √2 ≈ 1.4142

PRIMARY_CONSTANTS = {
    'C': C_TI,
    'T': T_TI,
    '1': 1.0,
    '√2': SQRT2,
    'φ': PHI,
    'e': E_TI,
    'π': PI_TI,
}

RING_RADII = [C_TI, T_TI, 1.0, SQRT2, PHI, E_TI, PI_TI]

RING_NAMES  = ['C', 'T', '1', '√2', 'φ', 'e', 'π']

N_RINGS   = 7
N_LAYERS  = 8
N_VERTICES = N_RINGS * N_LAYERS + 1  # 57
