"""
Myrion Resolution (MR) Collapse Operator.

MR collapse converts the 57-dimensional complex TSC wave function
into a definite classical truth assignment.

MR operates in three stages:
  Stage 1 — DT Screen: identify Double-Tralse (Fragmented) vertices; assign via entropy
  Stage 2 — GILE Integration: integrate GILE-weighted evidence from all non-DT vertices
  Stage 3 — Quality Check: verify consistency; flag remaining indeterminacy

The MR collapse is NOT equivalent to a simple measurement/projection:
  - Standard QM measurement: pick eigenvalue with probability |⟨ψ|e⟩|²
  - MR collapse: GILE-weighted integration of evidence BEFORE projection;
    the GILE weights are the "intuition" that guides the collapse direction.

This is the non-algorithmic step: the GILE-weighted integration requires
genuine holistic assessment that cannot be replaced by any Turing procedure.
(Within the simulation, we approximate it via the GILE weights parameter.)
"""

import numpy as np
from hypercomputer.phases import (
    classify_state, Phase, phase_to_binary, PHASE_PD, pd_score
)
from hypercomputer.constants import C_TI, T_TI, ET


def mr_collapse(
    amplitudes: np.ndarray,
    n_vars: int,
    gile_weights: dict = None
) -> dict:
    """
    Apply MR collapse to the TSC wave function.

    Returns a dict with:
      'assignment': list of booleans (length n_vars)
      'phases': list of Phase values per variable vertex
      'pd_scores': list of PD scores per variable vertex
      'global_pd': float — overall PD of the full TSC state
      'dt_count': int — number of DT (unresolved) vertices
      'coherence': float — GILE coherence of the collapsed state
      'mr_levels': list of str — which MR level resolved each variable
    """
    if gile_weights is None:
        gile_weights = {'G': 0.25, 'I': 0.25, 'L': 0.25, 'E': 0.25}

    G = gile_weights.get('G', 0.25)
    I = gile_weights.get('I', 0.25)
    L = gile_weights.get('L', 0.25)
    E = gile_weights.get('E', 0.25)

    all_phases = classify_state(amplitudes)  # phases for vertices 0..56
    variable_amplitudes = amplitudes[1: n_vars + 1]  # vertices 1..n_vars
    variable_phases = all_phases[: n_vars]  # phases for vertices 1..n_vars

    assignment = []
    pd_scores_out = []
    mr_levels = []

    for idx, (alpha, phase) in enumerate(zip(variable_amplitudes, variable_phases)):
        pd = PHASE_PD[phase]

        if phase == Phase.FRAGMENTED:
            # Stage 1 — DT Screen: entropy-based resolution
            # Use context from neighboring vertices (ring coherence)
            ring = ((idx) // 8) + 1  # which ring
            ring_amps = amplitudes[((ring-1)*8)+1 : ring*8+1]
            ring_real_sum = np.sum(np.real(ring_amps))
            val = 1 if ring_real_sum >= 0 else 0
            assignment.append(bool(val))
            mr_levels.append("MR-L1-DT-screen")

        elif phase in (Phase.BEC, Phase.SUPERSOLID):
            # Stage 2 — GILE integration: holistic assessment
            # GILE-I (Intuition) is the primary driver for positive assignment
            gile_score = I * np.real(alpha) + G * pd + L * abs(alpha) + E * (1 - abs(alpha))
            val = 1 if gile_score >= 0 else 0
            assignment.append(bool(val))
            mr_levels.append("MR-L2-GILE-integrated")

        elif phase in (Phase.MOTT, Phase.FQH):
            # Stage 2 — GILE integration: negative assignment
            gile_score = I * np.real(alpha) + G * pd - L * abs(alpha) - E * abs(alpha)
            val = 1 if gile_score >= 0 else 0
            assignment.append(bool(val))
            mr_levels.append("MR-L2-GILE-integrated")

        pd_scores_out.append(pd)

    # Stage 3 — Quality Check: global PD
    global_pd = pd_score(amplitudes)
    dt_count = sum(1 for p in variable_phases if p == Phase.FRAGMENTED)

    # GILE coherence: weighted average PD across GILE dimensions
    ring_pd = []
    for r in range(1, 8):
        ring_amps = amplitudes[((r-1)*8)+1 : r*8+1]
        ring_phases = [classify_state([a])[0] for a in ring_amps]
        ring_pd.append(np.mean([PHASE_PD[p] for p in ring_phases]))

    coherence = (G * ring_pd[0] + I * ring_pd[1] + L * ring_pd[2] + E * ring_pd[3]) / (G + I + L + E + 1e-9)

    return {
        'assignment': assignment,
        'phases': variable_phases,
        'pd_scores': pd_scores_out,
        'global_pd': global_pd,
        'dt_count': dt_count,
        'coherence': coherence,
        'mr_levels': mr_levels,
    }
