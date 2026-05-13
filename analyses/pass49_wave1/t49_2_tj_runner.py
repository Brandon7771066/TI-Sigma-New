"""T49-2 — Tralse-Joules (TJ) measurement reliability.

PRE-REG: H_PRIMARY: ICC(2,1) for TJ between raters A and B on HOLDOUT
≥ 0.50 (moderate). Pilot scale N=15 down from N=30.
"""
from __future__ import annotations
import json, sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).parent))
from rater_lib import rate, sha256_str, icc_2_1

STIMULI = [
    "She crossed the street to reach the bookstore.",
    "He absentmindedly drummed his fingers on the table.",
    "The senator deliberately misquoted the bill to score political points.",
    "The toddler reached for the cup and knocked it over.",
    "She trained for two years to qualify for the marathon.",
    "He sneezed during the meeting.",
    "The hiker chose the longer trail to extend the experience.",
    "The clock struck noon.",
    "She wrote a letter intending to mend a 20-year estrangement.",
    "He blinked.",
    "The CEO restructured the company to maximize shareholder value.",
    "The cat batted at the laser pointer dot.",
    "She volunteered at the shelter every Saturday for a decade.",
    "He coughed during the recital.",
    "The activist staged the protest to draw international media attention.",
]

RUBRIC = """For each item, rate two dimensions on integer 0-10:
- tau (τ): truth-value of the intentional content of the action — how unambiguously intentional vs incidental is the act? (10 = clearly purposeful intentional act; 0 = clearly involuntary/incidental).
- delta (δ): effect-distribution magnitude — how large is the act's claimed or implied causal effect on the world? (10 = sweeping effect; 0 = trivial/local).

Then compute TJ = τ × δ (you only need to provide tau and delta; TJ is computed downstream).

Return JSON list: [{"id": int, "tau": int, "delta": int}, ...] one per item.

ITEMS:
"""


def main():
    prompt = RUBRIC + "\n".join(f"{i}. {s}" for i, s in enumerate(STIMULI))
    corpus_sha = sha256_str(json.dumps(STIMULI))
    rA = rate("A", prompt, max_tokens=4000)
    rB = rate("B", prompt, max_tokens=4000)
    dA = {int(it["id"]): it for it in rA}
    dB = {int(it["id"]): it for it in rB}
    ids = sorted(set(dA) & set(dB))

    # 60/40 split deterministic
    import random
    rnd = random.Random(int(corpus_sha[:8], 16))
    perm = ids.copy(); rnd.shuffle(perm)
    cut = int(len(perm)*0.6)
    tune_ids = sorted(perm[:cut]); holdout_ids = sorted(perm[cut:])

    tj_A = [dA[i]["tau"]*dA[i]["delta"] for i in holdout_ids]
    tj_B = [dB[i]["tau"]*dB[i]["delta"] for i in holdout_ids]
    icc = icc_2_1(tj_A, tj_B)

    # tau-only and delta-only ICCs for diagnostic
    icc_tau = icc_2_1([dA[i]["tau"] for i in holdout_ids], [dB[i]["tau"] for i in holdout_ids])
    icc_delta = icc_2_1([dA[i]["delta"] for i in holdout_ids], [dB[i]["delta"] for i in holdout_ids])

    if icc != icc:  # nan
        verdict = "DISCONFIRM_DEGENERATE"
    elif icc >= 0.70:
        verdict = "CONFIRM_STRONG_PILOT"
    elif icc >= 0.50:
        verdict = "CONFIRM_PILOT"
    elif icc >= 0.30:
        verdict = "WEAK_PILOT"
    else:
        verdict = "DISCONFIRM_PILOT"

    out = {
        "test_id": "T49-2_TJ_measurement_reliability",
        "rater_independence": "same_model_two_personas",
        "pilot_flag": True,
        "n_stimuli": len(ids),
        "corpus_sha256": corpus_sha,
        "tune_ids": tune_ids, "holdout_ids": holdout_ids,
        "ratings_A": dA, "ratings_B": dB,
        "metrics": {
            "holdout_ICC_TJ": icc,
            "holdout_ICC_tau": icc_tau,
            "holdout_ICC_delta": icc_delta,
            "TJ_A": tj_A, "TJ_B": tj_B,
        },
        "verdict": verdict,
    }
    Path(__file__).parent.joinpath("t49_2_results.json").write_text(json.dumps(out, indent=2, default=str))
    print(f"T49-2 verdict: {verdict}")
    print(f"  TJ ICC: {icc:.3f}  τ ICC: {icc_tau:.3f}  δ ICC: {icc_delta:.3f}")
    return out


if __name__ == "__main__":
    main()
