"""T49-6 — DefT (Defective Truth) vs DT (Double Tralse) discrimination.

PRE-REG: H_PRIMARY: Cohen's κ on DefT-vs-DT subset (24 items) ≥ 0.40
(moderate). Pilot scale 18 (down from 24+6 distractors).
"""
from __future__ import annotations
import json, sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).parent))
from rater_lib import rate, sha256_str, percent_agreement, cohens_kappa

# Construction follows MR_TRUTH_LABELS_CANONICAL_RULING_2026-05-08:
# DT = τ(P) ∧ ¬τ(P) — proposition simultaneously satisfies and fails truth predicate.
# DefT (Defective Truth) = a proposition whose truth-evaluation has been corrupted
#   or whose evaluative apparatus is malfunctioning, NOT a proposition genuinely
#   bearing both truth-values simultaneously.

CLAIMS = [
    # 9 candidate-DT (genuine simultaneity):
    ("This sentence is both true and false.", "DT"),
    ("The electron passed through both slits and only one slit.", "DT"),
    ("Schrodinger's cat is alive and dead until the box is opened.", "DT"),
    ("The act was both consensual and coerced — both raters got the same evidence.", "DT"),
    ("The system is both stable and unstable at the bifurcation point.", "DT"),
    ("The vote was both legitimate and fraudulent given the disputed standards.", "DT"),
    ("The drug is both sedating and stimulating — different patients show opposite reactions.", "DT"),
    ("The proof is both valid and invalid depending on which axiom system you accept.", "DT"),
    ("The artwork is both original and a copy — copies were made before the original was signed.", "DT"),
    # 9 candidate-DefT (corrupted/malfunctioning evaluation):
    ("The thermometer reads 70 degrees but the sensor was damaged in transit.", "DefT"),
    ("The witness testified she saw the event but later admitted she was hallucinating from medication.", "DefT"),
    ("The poll showed 60% approval but the sampling frame excluded all non-landline households.", "DefT"),
    ("The lab result said positive but the sample was mislabeled at intake.", "DefT"),
    ("The historical document is dated 1850 but carbon analysis shows the ink is post-1950.", "DefT"),
    ("The translation reads 'peace' but the translator did not know the source language.", "DefT"),
    ("The verdict is guilty but the jury was tampered with.", "DefT"),
    ("The measurement is 4.7 cm but the ruler was not calibrated.", "DefT"),
    ("The weather forecast called for rain but the forecaster confused the Tuesday and Wednesday data files.", "DefT"),
]

RUBRIC = """The MR Truth Labels canonical ruling (2026-05-08) distinguishes:
- DT (Double Tralse): a proposition that SIMULTANEOUSLY satisfies and fails the truth predicate, formally τ(P) ∧ ¬τ(P). The proposition genuinely bears both truth-values at once.
- DefT (Defective Truth): a proposition whose truth-evaluation has been CORRUPTED or whose EVALUATIVE APPARATUS IS MALFUNCTIONING. The proposition does not genuinely bear both truth-values; rather, our means of assigning a truth-value has failed.

Key test: in DT, the both-and structure is in the WORLD. In DefT, the failure is in the MEASUREMENT/EVALUATION apparatus.

For each claim, label it 'DT' or 'DefT'.

Return JSON list: [{"id": int, "label": "DT" or "DefT"}, ...]

CLAIMS:
"""


def main():
    prompt = RUBRIC + "\n".join(f"{i}. {c[0]}" for i, c in enumerate(CLAIMS))
    corpus_sha = sha256_str(json.dumps(CLAIMS))
    rA = rate("A", prompt, max_tokens=4000)
    rB = rate("B", prompt, max_tokens=4000)
    dA = {int(it["id"]): it["label"] for it in rA}
    dB = {int(it["id"]): it["label"] for it in rB}
    ids = sorted(set(dA) & set(dB))

    import random
    rnd = random.Random(int(corpus_sha[:8], 16))
    perm = ids.copy(); rnd.shuffle(perm)
    cut = int(len(perm)*0.6)
    tune_ids = sorted(perm[:cut]); holdout_ids = sorted(perm[cut:])

    A = [dA[i] for i in holdout_ids]; B = [dB[i] for i in holdout_ids]
    truth = [CLAIMS[i][1] for i in holdout_ids]
    pa = percent_agreement(A, B)
    kappa = cohens_kappa(A, B)
    acc_A = percent_agreement(A, truth)
    acc_B = percent_agreement(B, truth)

    if kappa != kappa:
        verdict = "DISCONFIRM_DEGENERATE"
    elif kappa >= 0.70:
        verdict = "CONFIRM_STRONG_PILOT"
    elif kappa >= 0.40:
        verdict = "CONFIRM_PILOT"
    elif kappa >= 0.20:
        verdict = "WEAK_PILOT"
    else:
        verdict = "DISCONFIRM_PILOT"

    out = {
        "test_id": "T49-6_DefT_vs_DT_discrimination",
        "rater_independence": "same_model_two_personas",
        "pilot_flag": True,
        "n_claims": len(ids),
        "corpus_sha256": corpus_sha,
        "tune_ids": tune_ids, "holdout_ids": holdout_ids,
        "ratings_A": dA, "ratings_B": dB,
        "ground_truth_constructed": {i: CLAIMS[i][1] for i in ids},
        "metrics": {
            "holdout_inter_rater_kappa": kappa,
            "holdout_inter_rater_PA": pa,
            "holdout_rater_A_accuracy_vs_construction": acc_A,
            "holdout_rater_B_accuracy_vs_construction": acc_B,
        },
        "verdict": verdict,
    }
    Path(__file__).parent.joinpath("t49_6_results.json").write_text(json.dumps(out, indent=2, default=str))
    print(f"T49-6 verdict: {verdict}")
    print(f"  inter-rater κ: {kappa:.3f}  PA: {pa:.3f}")
    print(f"  accuracy vs constructed truth — A: {acc_A:.3f}  B: {acc_B:.3f}")
    return out


if __name__ == "__main__":
    main()
