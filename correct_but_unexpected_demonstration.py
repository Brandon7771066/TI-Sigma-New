"""
correct_but_unexpected_demonstration.py
========================================

Controlled structural illustration for URB #812 (NOT empirical evidence).

What this script is: a sanity check that the mechanism described in URB
#812 §2-§3 is mathematically real — i.e., a rigid grader that checks only
E_Q produces a large measured "wrong" rate on an answerer who is, by
construction, always correct. It confirms the gap is not rhetorical.

What this script is NOT: a measurement of how often case (iii) happens in
real grading environments, or a claim that divergent answerers outperform
conventional ones in reality-graded environments. Both answerers are given
identical 100% real scores here, by construction. Real-world prevalence is
an empirical question this script does not address.

Closed-form prediction (which the simulation reproduces):
    rigid score (conventional) = p + (1 - p) / |C_Q|
    rigid score (divergent)    = 1 / |C_Q|
    rigid gap                  = p * (1 - 1 / |C_Q|)

Demonstrates the structural asymmetry between:

  - a "rigid" grader (marks correct iff answer is in the asker's expected
    set E_Q) vs. a "real-world" grader (marks correct iff answer is in the
    actual correct set C_Q),

and:

  - a "conventional" answerer (always tries to give an answer in E_Q,
    succeeding probabilistically) vs. a "divergent" answerer (samples
    uniformly from C_Q — always correct in reality, but not always
    matching E_Q).

The demonstration: the divergent answerer is *literally always correct*
(every answer is in C_Q), and yet under the rigid grader they are marked
"wrong" the majority of the time — because the rigid grader is running the
wrong evaluation procedure. Under the real-world grader, the divergent
answerer is correctly marked correct 100% of the time.

Pure NumPy. Deterministic seed. Wall time < 1 s.
"""
from __future__ import annotations
import json
import numpy as np

RNG_SEED = 20260430


def simulate(n_questions: int = 5000,
             c_q_size: int = 4,
             p_conventional_hits_e_q: float = 0.7,
             rng: np.random.Generator | None = None):
    """Run the simulation.

    Parameters
    ----------
    n_questions : number of questions in the test.
    c_q_size : size of the actual correct set C_Q for each question.
        E_Q is always a single element (the asker's anticipated answer)
        drawn from C_Q.
    p_conventional_hits_e_q : probability that the conventional answerer
        successfully produces the E_Q element. With prob (1 - p) they
        produce a uniformly random element of C_Q (still correct in
        reality, just not the expected one).
    """
    if rng is None:
        rng = np.random.default_rng(RNG_SEED)

    # For each question:
    #   - C_Q is encoded implicitly as integers {0, 1, ..., c_q_size - 1}.
    #   - E_Q is the singleton {0} WLOG (we can always relabel).
    expected_idx = 0

    # Conventional answerer: with prob p, picks 0 (matches E_Q); with prob
    # (1 - p), picks uniformly from {0, ..., c_q_size - 1}.
    conv_hits_eq = rng.random(n_questions) < p_conventional_hits_e_q
    conv_random_pick = rng.integers(0, c_q_size, size=n_questions)
    conv_answers = np.where(conv_hits_eq, expected_idx, conv_random_pick)

    # Divergent answerer: always picks uniformly from C_Q. Always correct
    # (in C_Q by construction), but only matches E_Q with prob 1 / c_q_size.
    div_answers = rng.integers(0, c_q_size, size=n_questions)

    # Rigid grader: correct iff answer == expected_idx (a check against E_Q).
    conv_rigid_correct = (conv_answers == expected_idx)
    div_rigid_correct = (div_answers == expected_idx)

    # Real-world grader: correct iff answer in C_Q. Both answerers always
    # pick from C_Q by construction, so this is always True.
    conv_real_correct = np.ones(n_questions, dtype=bool)
    div_real_correct = np.ones(n_questions, dtype=bool)

    return {
        "config": {
            "n_questions": n_questions,
            "c_q_size": c_q_size,
            "p_conventional_hits_e_q": p_conventional_hits_e_q,
            "rng_seed": RNG_SEED,
        },
        "conventional_answerer": {
            "rigid_grader_score": float(conv_rigid_correct.mean()),
            "real_grader_score": float(conv_real_correct.mean()),
            "answers_in_c_q_fraction": 1.0,  # always in C_Q by construction
        },
        "divergent_answerer": {
            "rigid_grader_score": float(div_rigid_correct.mean()),
            "real_grader_score": float(div_real_correct.mean()),
            "answers_in_c_q_fraction": 1.0,
        },
        "asymmetry": {
            "rigid_grader_punishes_divergent_by_pp": float(
                conv_rigid_correct.mean() - div_rigid_correct.mean()
            ) * 100,
            "real_grader_difference_pp": float(
                conv_real_correct.mean() - div_real_correct.mean()
            ) * 100,
            "interpretation": (
                "Both answerers are always correct in reality (both always "
                "answer within C_Q). The rigid grader nevertheless reports "
                "a large gap, because it is running the procedure "
                "'matches E_Q?' and reporting it as 'is correct?'. The "
                "real grader correctly reports 0pp gap. The rigid-grader "
                "gap is the asymmetric punishment of divergent-thinking "
                "answerers in conventional grading environments."
            ),
        },
    }


def main():
    print("=" * 70)
    print("URB #812 — Correct-But-Unexpected-Answer demonstration")
    print("=" * 70)
    rng = np.random.default_rng(RNG_SEED)
    report = simulate(rng=rng)

    cfg = report["config"]
    print(f"\nConfig: n={cfg['n_questions']}, |C_Q|={cfg['c_q_size']}, "
          f"P(conv hits E_Q)={cfg['p_conventional_hits_e_q']}, "
          f"seed={cfg['rng_seed']}")

    print("\n--- Conventional answerer (targets E_Q) ---")
    c = report["conventional_answerer"]
    print(f"  Rigid grader (E_Q only):  {c['rigid_grader_score']*100:5.2f}% 'correct'")
    print(f"  Real grader  (full C_Q):  {c['real_grader_score']*100:5.2f}% correct")
    print(f"  Answers actually in C_Q:  {c['answers_in_c_q_fraction']*100:5.2f}%")

    print("\n--- Divergent answerer (samples C_Q uniformly — always correct) ---")
    d = report["divergent_answerer"]
    print(f"  Rigid grader (E_Q only):  {d['rigid_grader_score']*100:5.2f}% 'correct'")
    print(f"  Real grader  (full C_Q):  {d['real_grader_score']*100:5.2f}% correct")
    print(f"  Answers actually in C_Q:  {d['answers_in_c_q_fraction']*100:5.2f}%")

    print("\n--- Asymmetry (rigid grader vs. reality) ---")
    a = report["asymmetry"]
    print(f"  Rigid-grader gap (conv - div): "
          f"{a['rigid_grader_punishes_divergent_by_pp']:+5.2f} pp "
          f"<-- this is the asymmetric punishment")
    print(f"  Real-grader gap  (conv - div): "
          f"{a['real_grader_difference_pp']:+5.2f} pp "
          f"<-- correctly zero; both are always correct")
    print(f"\n  Interpretation: {a['interpretation']}")

    out_path = "correct_but_unexpected_report.json"
    with open(out_path, "w") as f:
        json.dump(report, f, indent=2)
    print(f"\nReport written to {out_path}")


if __name__ == "__main__":
    main()
