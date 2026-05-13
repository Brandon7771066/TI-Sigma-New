"""T49-1 — Authority Axis (AA) discriminative validity vs the 4 prior axes.

PRE-REGISTRATION (frozen at write-time, before any rater calls).

CLAIM: AA is rater-distinguishable from the other four truth-axes
(PD-real, PD-imaginary, MR Truth Labels, τ/δ). Operationally:
  H_PRIMARY: Cohen's κ (between raters A and B) on AA scores ≥ 0.40
  AND |corr(AA, X)| < 0.7 for X in {PD_real, PD_imag, MR, tau_over_delta}
  on the HOLDOUT segment (60/40 split by claim ID).

CORPUS: 20 hand-frozen TI-Sigma claim-statements (down-scaled from N=50
in the original sketch for session-budget; flagged as pilot scale).
"""
from __future__ import annotations
import json, math, sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).parent))
from rater_lib import rate, sha256_str, cohens_kappa, percent_agreement

CLAIMS = [
    "MR Truth Labels are base-4: True, False, Indeterminate, Double Tralse.",
    "Double Tralse is formally τ(P) ∧ ¬τ(P).",
    "The Authority Axis is a fifth truth-axis distinct from PD-real and PD-imaginary.",
    "Tralse-Joules is a quantifiable intentionality unit defined as TJ = τ(s) × δ(MR).",
    "GILE Intuition is a distributed network intelligence, not a localized cognitive faculty.",
    "Lazy-Binary Tralsity describes statements that force a categorical onto a continuous referent.",
    "qc26 GHZ-5 hardware-witnesses multipartite entanglement with |M_5|=14.535, a 71σ violation of the LHV bound.",
    "The MIM-revision Vertical Agency Model dissolves Affect, Behavior, Cognition into a single integrated stack.",
    "Asymmetric Success-Failure Performance is a meta-axiom predicting audience-tuned δ outperforms static δ.",
    "Mood Amplifiers can be evaluated for safety using AI simulation prior to human trials.",
    "Permaculture food forests can equal or exceed monoculture caloric output after a 5-7 year establishment phase.",
    "Group singing produces measurable LCC-band coherence across participants.",
    "The Three-C grade has Capital as its sole binding constraint.",
    "Paradoxical drug reactions are evidence of a body-mind tralseness substrate.",
    "Substrate-encoding sufficiency does not imply operational-logic equivalence.",
    "DefT (Defective Truth) is categorically distinct from DT (Double Tralse).",
    "Households of 2-3 people on large suburban lots are inefficient economies.",
    "Age discrimination is the most universally-distributed form of discrimination across the lifespan.",
    "The Universal Bridge Theorem connects Universal A Priori to operational TI-Sigma claims.",
    "All mathematical functions can be losslessly described in pure binary.",
]

AXES = ["PD_real", "PD_imag", "MR_label", "tau_over_delta", "AA"]
RUBRIC = """For each claim, rate it on each of FIVE truth-axes, integer 0-10:
- PD_real: degree of permissibility-distribution real-axis support (10 = fully supported by evidence; 0 = no real-evidence support).
- PD_imag: permissibility-distribution imaginary-axis modality / how counterfactual or speculative (10 = fully concrete; 0 = highly speculative/counterfactual).
- MR_label: MR Truth Label score: 10 = clearly True, 7 = mostly True, 5 = Indeterminate, 3 = Double-Tralse-like, 0 = clearly False.
- tau_over_delta: ratio of τ (truth) to δ (effect), 10 = high truth+small effect; 0 = low truth+large claimed effect.
- AA: Authority Axis — to what extent does this claim rest on speaker-authority vs independent verifiability? 10 = fully independently verifiable; 0 = relies entirely on speaker-authority.

Return a JSON list of objects: [{"id": int, "PD_real": int, "PD_imag": int, "MR_label": int, "tau_over_delta": int, "AA": int}, ...]
Provide one entry for EACH claim, indexed by id starting at 0.

CLAIMS:
"""


def main():
    prompt = RUBRIC + "\n".join(f"{i}. {c}" for i, c in enumerate(CLAIMS))
    corpus_sha = sha256_str(json.dumps(CLAIMS))

    rA = rate("A", prompt, max_tokens=8000)
    rB = rate("B", prompt, max_tokens=8000)

    def to_dict(items):
        return {int(it["id"]): it for it in items}

    dA, dB = to_dict(rA), to_dict(rB)
    ids = sorted(set(dA) & set(dB))

    # HOLDOUT split: 60% TUNE+VAL, 40% HOLDOUT, deterministic by sha
    import random
    rnd = random.Random(int(corpus_sha[:8], 16))
    perm = ids.copy()
    rnd.shuffle(perm)
    cut = int(len(perm) * 0.6)
    tune_ids = sorted(perm[:cut])
    holdout_ids = sorted(perm[cut:])

    def axis_corr(axis_x, axis_y, idset):
        xs = [dA[i][axis_x] for i in idset]
        ys = [dA[i][axis_y] for i in idset]
        n = len(xs)
        if n < 2:
            return float("nan")
        mx, my = sum(xs)/n, sum(ys)/n
        num = sum((xs[i]-mx)*(ys[i]-my) for i in range(n))
        dx = math.sqrt(sum((x-mx)**2 for x in xs))
        dy = math.sqrt(sum((y-my)**2 for y in ys))
        return num / (dx*dy) if dx*dy > 1e-12 else float("nan")

    holdout_aa_kappa = cohens_kappa(
        [dA[i]["AA"] for i in holdout_ids],
        [dB[i]["AA"] for i in holdout_ids],
    )
    holdout_aa_pa = percent_agreement(
        [dA[i]["AA"] for i in holdout_ids],
        [dB[i]["AA"] for i in holdout_ids],
    )
    other_corrs = {
        x: axis_corr("AA", x, holdout_ids)
        for x in ["PD_real", "PD_imag", "MR_label", "tau_over_delta"]
    }
    max_other_corr = max(abs(v) for v in other_corrs.values() if not math.isnan(v))

    primary_met = (holdout_aa_kappa >= 0.40) and (max_other_corr < 0.7)
    if math.isnan(holdout_aa_kappa) or holdout_aa_kappa < 0.20:
        verdict = "DISCONFIRM_RATER_NOISE"
    elif max_other_corr >= 0.7:
        verdict = "DISCONFIRM_AA_REDUCES_TO_OTHER_AXIS"
    elif primary_met:
        verdict = "CONFIRM_PILOT" if holdout_aa_kappa >= 0.40 else "WEAK_PILOT"
    else:
        verdict = "WEAK_PILOT"

    out = {
        "test_id": "T49-1_AA_discriminative_validity",
        "rater_independence": "same_model_two_personas (Claude, temp 0.0 vs 0.3)",
        "pilot_flag": True,
        "n_claims": len(ids),
        "corpus_sha256": corpus_sha,
        "holdout_ids": holdout_ids,
        "tune_val_ids": tune_ids,
        "ratings_A": dA,
        "ratings_B": dB,
        "metrics": {
            "holdout_AA_cohens_kappa": holdout_aa_kappa,
            "holdout_AA_percent_agreement": holdout_aa_pa,
            "holdout_AA_vs_other_axis_correlations": other_corrs,
            "max_abs_other_corr": max_other_corr,
        },
        "verdict": verdict,
    }
    Path(__file__).parent.joinpath("t49_1_results.json").write_text(json.dumps(out, indent=2, default=str))
    print(f"T49-1 verdict: {verdict}")
    print(f"  AA κ: {holdout_aa_kappa:.3f}  PA: {holdout_aa_pa:.3f}")
    print(f"  max |corr(AA, other)|: {max_other_corr:.3f}  per-axis: {other_corrs}")
    return out


if __name__ == "__main__":
    main()
