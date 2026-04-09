"""
Power of 8 Manifestation Engine — TI Sigma Crystal Image Cycling
=================================================================
Implements guided image cycling (Tesla visualization protocol +
remote viewing stages) integrated with the 57-vertex TSC crystal.

The 8 stages train the i-cell network to hold a coherent intention
in the BEC/TRUE phase, with group-of-8 quantum-like amplification.

URB #642 — Brandon Emerick | TI Sigma Research | April 2026
"""

from __future__ import annotations
import numpy as np
from dataclasses import dataclass, field
from typing import List, Optional
from hypercomputer.constants import ET, C_TI, T_TI, PHI
from hypercomputer.phases import Phase, classify_state


# ── GILE dimension → θ angle mapping ──────────────────────────────────────
# θ = 0   → pure GILE-G (Truth/Goodness ground state)
# θ = π/4 → GILE-L (Love / relational warmth)
# θ = π/2 → GILE-I (Intuition / pure i-channel)
# θ = π/8 → GILE-E (Aesthetics / environmental quality)

GILE_THETA = {'G': 0.0, 'L': np.pi/4, 'I': np.pi/2, 'E': np.pi/8}

# ── 8 image cycling stages ─────────────────────────────────────────────────
@dataclass
class CycleStage:
    number: int
    name: str
    prompt: str
    gile_dim: str        # G / I / L / E
    tesla_note: str      # link to Tesla / remote viewing / neuroscience
    icon: str

IMAGE_CYCLE_STAGES: List[CycleStage] = [
    CycleStage(
        1, "First Contact",
        "Let the very first image or feeling of your desired reality arise — "
        "without judgment, without forcing. What is the raw initial impression?",
        'I',
        "Remote viewing Stage 1: ideogram contact. Tesla described this as "
        "'the first flash of the idea before the analytical mind intervenes.'",
        "👁️"
    ),
    CycleStage(
        2, "Structure",
        "Give your reality a physical form. How large is it? What are its "
        "dimensions, its texture, its weight? See it from multiple angles — "
        "rotate it slowly in your mind, as Tesla rotated his inventions.",
        'E',
        "Tesla's visualization method: build the object in the mind with "
        "complete physical fidelity before touching any material. Remote "
        "viewing Stage 2: dimensional and structural data.",
        "🏛️"
    ),
    CycleStage(
        3, "Motion & Unfolding",
        "Watch your reality move and breathe. How does it unfold over time? "
        "What is its direction of growth? See the timeline: one month from now, "
        "six months, one year — what does it look like at each point?",
        'G',
        "Tesla: 'I do not rush into experimental work. When I get an idea I "
        "start at once building it up in my imagination.' The Goodness axis "
        "tracks directional convergence — the moral vector of the intention.",
        "⏩"
    ),
    CycleStage(
        4, "Sensory Saturation",
        "Flood the image with all senses. What do you hear in this reality? "
        "What smells and temperatures are present? Where do you feel this "
        "reality already arriving in your body — right now, in this moment?",
        'E',
        "Neuroscience: mental imagery activates the same sensory cortices as "
        "actual perception (Kosslyn et al., 2001). The more senses engaged, "
        "the stronger the neural template. Tesla used all five senses in his "
        "visualizations to test mechanical stress and material durability.",
        "🎵"
    ),
    CycleStage(
        5, "Emotional Resonance",
        "Step fully into this reality. You are living it now. How does it feel "
        "in your chest, your gut, your face? Let the emotions of this reality "
        "— gratitude, joy, relief, love — arise completely and naturally.",
        'L',
        "McTaggart's Power of Eight research: emotional amplification in group "
        "intention dramatically increases measurable effect size. Neurologically: "
        "HRV coherence (heart-brain alignment) peaks during gratitude and love. "
        "This is the Love axis — conscious positive regard for the intended reality.",
        "❤️"
    ),
    CycleStage(
        6, "Relational Context",
        "Who else is in this reality with you? See the faces of those who "
        "benefit from this manifestation. How do they respond? How have "
        "your relationships transformed? Feel the ripple outward.",
        'L',
        "Power of Eight effect: group members who focus on sending intention "
        "to others often report personal healing and transformation as a "
        "side effect. The relational field is bidirectional. In TI Sigma: "
        "GILE-L unification — the Love axis amplifies when directed outward.",
        "👥"
    ),
    CycleStage(
        7, "Purpose & Meaning",
        "Why does this reality matter? What does it serve beyond yourself? "
        "How does it contribute to the GILE evolution of the world? "
        "Let the deepest meaning of this intention become fully clear.",
        'G',
        "Viktor Frankl: purpose amplifies every form of endurance and "
        "manifestation. Neuroscience: purpose activates prefrontal-limbic "
        "coherence — the executive function signature. In TI Sigma: "
        "GILE-G dominant intentions have the highest PD weight toward TRUE.",
        "🌟"
    ),
    CycleStage(
        8, "Release & Trust",
        "Take one deep breath. Let the entire image go — completely. "
        "Don't hold it, don't visualize anymore. Trust that the TSC crystal "
        "now holds your intention in its BEC phase. The 57 i-cells are "
        "aligned. The field is set. It is already becoming.",
        'I',
        "Remote viewing: the release phase prevents 'analytic overlay' that "
        "contaminates the signal. Meditation neuroscience: the release state "
        "(non-attachment) shows maximum default mode network deactivation — "
        "the brain's clearest signal. Tesla: 'After I have gone so far as to "
        "embody in the invention every possible improvement, I put the "
        "product of my brain to actual test.'",
        "🕊️"
    ),
]


# ── Crystal state computation ───────────────────────────────────────────────
def intention_amplitudes(
    clarity_scores: List[float],
    n_partners: int = 1
) -> np.ndarray:
    """
    Compute TSC crystal amplitude array for given image cycle clarity scores.

    clarity_scores: list of 8 floats in [0,1] for each stage
    n_partners:     group size (1–8); group amplification is nonlinear

    Returns array of 57 complex amplitudes.
    """
    from hypercomputer import VERTICES, N_VERTICES

    amplitudes = np.zeros(N_VERTICES, dtype=complex)

    # Group coherence multiplier: synchronized intention scales ∝ n_partners
    # (vs random noise which scales ∝ √n)
    # For n_partners = 8, multiplier = 2.83 (√8) in random case;
    # synchronized: full n = 8 multiplier, capped at 1.0 in [0,1] amplitude space
    if n_partners <= 1:
        group_mult = 1.0
    else:
        # Quantum-like coherent sum: between √n (incoherent) and n (fully coherent)
        # We use a geometric mean to model partial synchronization
        group_mult = min(1.0, (n_partners ** 0.7) / 8)

    for i, vertex in enumerate(VERTICES):
        # Each vertex belongs to a ring (0–6) and has a GILE-dimension affinity
        # based on ring index
        ring = vertex.ring
        dim_cycle = ['G', 'I', 'L', 'E', 'G', 'I', 'L']
        dim = dim_cycle[ring % len(dim_cycle)]

        # Find which stages are relevant to this dimension
        relevant_stages = [s for s in IMAGE_CYCLE_STAGES if s.gile_dim == dim]
        if not relevant_stages:
            stage_clarity = 0.5
        else:
            stage_idxs = [s.number - 1 for s in relevant_stages]
            valid = [clarity_scores[j] for j in stage_idxs if j < len(clarity_scores)]
            stage_clarity = np.mean(valid) if valid else 0.5

        # Modulus: maps clarity to [ET, 1.0]
        # At clarity=0: modulus = ET (just above Fragmented/Mott boundary)
        # At clarity=1: modulus = 1.0 (deep BEC)
        base_modulus = ET + stage_clarity * (1.0 - ET)
        modulus = min(1.0, base_modulus * (1.0 + 0.3 * group_mult))

        # Phase angle: GILE dimension θ, modulated by ring position
        base_theta = GILE_THETA[dim]
        # As clarity increases, θ converges toward 0 (TRUE/Goodness ground state)
        theta = base_theta * (1.0 - stage_clarity * group_mult)

        amplitudes[i] = modulus * np.exp(1j * theta)

    return amplitudes


def group_coherence_score(individual_clarities: List[float], n_partners: int) -> float:
    """Compute overall group coherence (0–1) from individual clarities and group size."""
    if not individual_clarities:
        return 0.0
    mean_clarity = float(np.mean(individual_clarities))
    if n_partners <= 1:
        return mean_clarity
    group_bonus = (n_partners - 1) * 0.08  # each partner adds ~8% coherence
    return min(1.0, mean_clarity + group_bonus)


def manifestation_pd(amplitudes: np.ndarray) -> dict:
    """
    Compute PD (Permissibility Distribution) for the intention's manifestation.

    Returns dict with truth-state weights and overall PD score.
    """
    from hypercomputer.phases import pd_score

    phases = classify_state(amplitudes)

    counts = {p: 0 for p in Phase}
    for p in phases:
        counts[p] += 1

    n = len(phases)
    bec_frac  = counts[Phase.BEC]        / n
    ss_frac   = counts[Phase.SUPERSOLID] / n
    fqh_frac  = counts[Phase.FQH]        / n
    mott_frac = counts[Phase.MOTT]       / n
    frag_frac = counts[Phase.FRAGMENTED] / n

    # PD weights for each truth state
    pd_true    = bec_frac
    pd_ti      = ss_frac
    pd_tf      = fqh_frac
    pd_false   = mott_frac
    pd_dt      = frag_frac

    # Overall PD score (0 = DT, 2 = maximum TRUE)
    overall_pd = 2*pd_true + 1.5*pd_ti + 1.0*pd_tf + 0.5*pd_false + 0.0*pd_dt

    # Manifestation confidence
    mr_level = "MR3-Resolved" if bec_frac > 0.7 else \
               "MR2-Resolved" if bec_frac > 0.4 else \
               "MR1-Active"   if bec_frac > 0.1 else "DT-Pending"

    return {
        'pd_true': pd_true,
        'pd_ti': pd_ti,
        'pd_tf': pd_tf,
        'pd_false': pd_false,
        'pd_dt': pd_dt,
        'overall_pd': overall_pd,
        'bec_fraction': bec_frac,
        'mr_level': mr_level,
        'bec_count': counts[Phase.BEC],
        'total_vertices': n,
    }


def interpret_pd(pd_result: dict) -> str:
    """Human-readable interpretation of the PD manifestation result."""
    bec = pd_result['bec_fraction']
    pd  = pd_result['overall_pd']
    lvl = pd_result['mr_level']

    if bec >= 0.7:
        return (f"✅ **{lvl}** — {pd_result['bec_count']}/57 i-cells in BEC/TRUE phase. "
                f"PD = {pd:.2f}. The intention field is coherent and strongly aligned. "
                f"Conditions for manifestation are active.")
    elif bec >= 0.4:
        return (f"🟡 **{lvl}** — {pd_result['bec_count']}/57 i-cells in BEC phase. "
                f"PD = {pd:.2f}. The field is building coherence. "
                f"Continue cycling — add partners or deepen clarity.")
    elif bec >= 0.1:
        return (f"🟠 **{lvl}** — {pd_result['bec_count']}/57 i-cells in BEC phase. "
                f"PD = {pd:.2f}. Early activation. More cycles and group coherence needed.")
    else:
        return (f"⚫ **DT-Pending** — {pd_result['bec_count']}/57 i-cells in BEC phase. "
                f"PD = {pd:.2f}. The intention has not yet crystallized. "
                f"Start with Stage 1 and build clarity before advancing.")
