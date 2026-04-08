"""
Five BEC Phase Regimes = Five TI Sigma Truth Values.

Phase classification is based on the modulus |α| of a vertex amplitude α ∈ ℂ.
The five thresholds are TI Sigma primary constants:
  |α| > T_TI        → BEC phase         → TRUE          (PD > 2.0)
  C_TI < |α| ≤ T_TI → Supersolid        → TRALSE-INDET  (PD ∈ [1.5, 2.0])
  ET   < |α| ≤ C_TI → Frac. Quantum Hall→ TRALSE-FALSE  (PD ∈ [0.5, 1.5])
  ε    < |α| ≤ ET   → Mott Insulator    → FALSE         (PD < 0.5)
  |α| ≤ ε           → Fragmented        → DOUBLE-TRALSE (DT)

where ε = 1e-6 (numerical zero).
"""

from enum import Enum, auto
import numpy as np
from hypercomputer.constants import C_TI, T_TI, ET


EPSILON = 1e-6


class Phase(Enum):
    BEC            = "TRUE"            # Bose-Einstein Condensate → TRUE
    SUPERSOLID     = "TRALSE-INDET"    # Supersolid → Tralse-Indeterminate
    FQH            = "TRALSE-FALSE"    # Fractional Quantum Hall → Tralse-False
    MOTT           = "FALSE"           # Mott Insulator → FALSE
    FRAGMENTED     = "DOUBLE-TRALSE"   # Fragmented Condensate → Double Tralse


PHASE_COLORS = {
    Phase.BEC:        "#00cc44",   # Green  — TRUE
    Phase.SUPERSOLID: "#ffaa00",   # Amber  — TRALSE-INDET
    Phase.FQH:        "#aa44ff",   # Purple — TRALSE-FALSE
    Phase.MOTT:       "#cc2200",   # Red    — FALSE
    Phase.FRAGMENTED: "#222222",   # Black  — DT
}

PHASE_PD = {
    Phase.BEC:        2.5,
    Phase.SUPERSOLID: 1.75,
    Phase.FQH:        1.0,
    Phase.MOTT:       0.25,
    Phase.FRAGMENTED: 0.0,
}

PHASE_LABELS = {
    Phase.BEC:        "BEC (TRUE)",
    Phase.SUPERSOLID: "Supersolid (TRALSE-INDET)",
    Phase.FQH:        "Frac. Quantum Hall (TRALSE-FALSE)",
    Phase.MOTT:       "Mott Insulator (FALSE)",
    Phase.FRAGMENTED: "Fragmented Condensate (DT)",
}


def classify_amplitude(alpha: complex) -> Phase:
    mod = abs(alpha)
    if mod <= EPSILON:
        return Phase.FRAGMENTED
    elif mod <= ET:
        return Phase.MOTT
    elif mod <= C_TI:
        return Phase.FQH
    elif mod <= T_TI:
        return Phase.SUPERSOLID
    else:
        return Phase.BEC


def classify_state(amplitudes: np.ndarray) -> list:
    return [classify_amplitude(a) for a in amplitudes]


def phase_to_binary(phase: Phase) -> int:
    """MR collapse: resolve 5-valued truth to classical binary."""
    if phase in (Phase.BEC, Phase.SUPERSOLID):
        return 1
    elif phase in (Phase.MOTT, Phase.FQH):
        return 0
    else:
        return np.random.randint(0, 2)  # DT: maximum entropy → coin flip


def pd_score(amplitudes: np.ndarray) -> float:
    """Average PD score across all non-origin vertices."""
    phases = classify_state(amplitudes[1:])
    return np.mean([PHASE_PD[p] for p in phases])
