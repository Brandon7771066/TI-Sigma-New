"""
Bell/CHSH device-independence (DI) feasibility for an LCC / Mood-Amplifier substrate.

Context (B166): Weak-LCC is a valid CONDITIONAL whose antecedent ("all common
causes ruled out") is NOT dischargeable from observation alone. The ONLY known
regime where correlations certify causal structure WITHOUT measuring/ruling out
every hidden common cause is the device-independent (DI) Bell regime: a
loophole-free CHSH violation 2*sqrt(2) > 2, which by Fine's theorem (1982)
certifies that NO local-hidden-variable (i.e. no common-cause) model exists.

LCC-PROOF-F3 asks: (a) can a candidate Mood-Amplifier substrate be placed in a
genuine DI regime, or (b) can we prove no biological substrate can reach it
(monogamy / decoherence / space-like-separation bound)?

This script does NOT run or fabricate any quantum-hardware experiment. It only
evaluates three TEXTBOOK physical bounds against the physical parameters of a
two-brain hyperscanning setup, to see whether route (a) is physically reachable.
All numbers are elementary / cited constants; the script is fully deterministic.

Cited physics (real):
- Fine, A. (1982). Hidden variables, joint probability, and the Bell inequalities.
  Phys. Rev. Lett. 48, 291.  (CHSH <=2 for ALL settings IFF a global joint
  measure / common-cause model exists.)
- Tsirelson, B. (1980). Quantum bound = 2*sqrt(2).
- Coffman, Kundu, Wootters (2000), Phys. Rev. A 61, 052306 (CKW monogamy);
  Toner & Verstraete (2006), arXiv:quant-ph/0611001 (CHSH monogamy:
  S_AB^2 + S_AC^2 <= 8).
- Tegmark, M. (2000). Importance of quantum decoherence in brain processes.
  Phys. Rev. E 61, 4194.  (neural decoherence ~1e-13..1e-20 s.)
- Loophole-free Bell tests: Hensen et al. (2015) Nature 526, 682 (locality +
  detection loopholes closed simultaneously using space-like separation).
"""

import json
import math
import hashlib
import os

C = 299_792_458.0  # speed of light, m/s (exact, SI)
TSIRELSON = 2.0 * math.sqrt(2.0)  # 2.8284..., quantum CHSH max
CLASSICAL_CHSH = 2.0


def spacelike_separation_budget(distance_m: float, event_duration_s: float) -> dict:
    """Locality loophole: measurement setting-choice + readout on each side must
    COMPLETE inside the light-cone gap, i.e. faster than d/c, else a subluminal
    influence could coordinate the two sides (common-cause loophole re-opens).

    A neural 'measurement' (evoked response / decodable EEG feature) takes ~ms.
    """
    light_gap_s = distance_m / C  # max time allowed for a space-like-separated event
    ratio = event_duration_s / light_gap_s  # >1 => too slow, loophole OPEN
    return {
        "distance_m": distance_m,
        "light_gap_s": light_gap_s,
        "neural_event_duration_s": event_duration_s,
        "slowness_ratio_event_over_lightgap": ratio,
        "locality_loophole_closable": bool(ratio <= 1.0),
    }


def decoherence_gap(decoherence_s: float, neural_process_s: float) -> dict:
    """Entanglement between the two substrates must SURVIVE at least one
    information-processing step. If tau_decoherence << tau_process, no coherent
    non-classical correlation can be shared."""
    orders = math.log10(neural_process_s / decoherence_s)
    return {
        "decoherence_time_s": decoherence_s,
        "neural_process_time_s": neural_process_s,
        "orders_of_magnitude_gap": orders,
        "coherence_survives_one_step": bool(decoherence_s >= neural_process_s),
    }


def monogamy_ceiling(S_AB: float) -> dict:
    """CHSH monogamy (Toner-Verstraete): S_AB^2 + S_AC^2 <= 8.
    If region A maximally violates with B (S_AB=2*sqrt(2)=>8), then S_AC^2<=0
    => S_AC<=2 (classical). So a *network* of pairwise-Bell-violating brain
    regions is barred: at most one maximal partner. Full-brain pairwise DI
    certification is impossible."""
    s2 = S_AB ** 2
    max_S_AC_sq = max(0.0, 8.0 - s2)
    max_S_AC = math.sqrt(max_S_AC_sq)
    return {
        "S_AB": S_AB,
        "max_possible_S_AC": max_S_AC,
        "second_partner_can_violate": bool(max_S_AC > CLASSICAL_CHSH),
    }


def main():
    # --- Parameters for a realistic two-person hyperscanning ("Mood Amplifier") ---
    DISTANCE_M = 1.0            # two seated participants ~1 m apart
    NEURAL_EVENT_S = 1e-3       # ms-scale decodable neural event (generous/fast)
    DECOHERENCE_S = 1e-13       # Tegmark (2000) UPPER end (most generous to the claim)
    NEURAL_PROCESS_S = 1e-3     # one neural processing step (~ms)

    locality = spacelike_separation_budget(DISTANCE_M, NEURAL_EVENT_S)
    decoh = decoherence_gap(DECOHERENCE_S, NEURAL_PROCESS_S)
    mono = monogamy_ceiling(TSIRELSON)

    # A DI certification of interaction-specific coupling on two brains would need
    # ALL of: (i) locality loophole closable, (ii) shared coherence survives,
    # (iii) a genuine 2-party CHSH>2. Network extension additionally needs (iv)
    # monogamy to permit >1 violating pair.
    route_a_reachable = (
        locality["locality_loophole_closable"]
        and decoh["coherence_survives_one_step"]
    )

    verdict = {
        "quantum_chsh_max_tsirelson": TSIRELSON,
        "classical_bound": CLASSICAL_CHSH,
        "locality_loophole": locality,
        "decoherence": decoh,
        "monogamy_network": mono,
        "route_a_two_brain_DI_reachable": bool(route_a_reachable),
        "route_b_negative_no_biological_DI": bool(not route_a_reachable),
        "interpretation": (
            "Route (a) is UNREACHABLE for a neural two-brain substrate: the "
            "locality loophole needs setting+readout within d/c (~ns over 1 m) but "
            "neural events take ~ms (~3e5 too slow), and any shared quantum coherence "
            "decoheres ~10 orders of magnitude (factor ~1e10) faster than one neural "
            "step (Tegmark 2000). "
            "Monogamy additionally bars a full-brain network of pairwise Bell violations. "
            "=> LCC-PROOF-F3(b) resolves NEGATIVE on known physics: the Bell/CHSH route "
            "stays a flagged STRUCTURAL RESONANCE (the corpus's no-global-joint-measure "
            "result), not a live experimental path to a non-conditional LCC. "
            "LCC-PROOF-F3(a) stays open only in principle (a non-neural engineered "
            "substrate is not excluded by THIS analysis)."
        ),
    }

    out_dir = os.path.dirname(os.path.abspath(__file__))
    res_dir = os.path.join(out_dir, "results")
    os.makedirs(res_dir, exist_ok=True)

    payload = json.dumps(verdict, sort_keys=True, indent=2)
    verdict["config_sha"] = hashlib.sha256(payload.encode()).hexdigest()[:12]

    with open(os.path.join(res_dir, "results.json"), "w") as f:
        json.dump(verdict, f, indent=2)

    print(payload)
    print("config_sha:", verdict["config_sha"])


if __name__ == "__main__":
    main()
