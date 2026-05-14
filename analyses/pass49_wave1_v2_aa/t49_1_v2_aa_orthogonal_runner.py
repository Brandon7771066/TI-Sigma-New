"""T49-1 v2 — AA discriminative validity with REDESIGNED RUBRIC + ORTHOGONAL CORPUS.

Brandon directive (2026-05-13): "Invest in rubric redesign and retest for AA.
Only demote AA if PD-real can truly account for what AA covers."

DESIGN CHANGES vs T49-1 v1:

1. CORPUS: 20 claims constructed in a 2x2 orthogonal matrix on the two
   *intended-to-be-independent* axes (5 per quadrant):
     Q1: HighAA (low-authority-route) + HighPD_real (well-supported)
     Q2: LowAA  (high-authority-route) + HighPD_real (well-supported)
     Q3: HighAA (low-authority-route) + LowPD_real (weakly-supported)
     Q4: LowAA  (high-authority-route) + LowPD_real (weakly-supported)
   If AA truly indexes *epistemic-routing* (independent of *evidence-support*),
   raters should produce ratings whose between-axis correlation on this
   corpus is materially lower than on the v1 corpus (where claims were
   not orthogonally controlled).

2. AA RUBRIC: REDESIGNED. v1 rubric ("10=fully independently verifiable;
   0=relies entirely on speaker-authority") conflated independent-checkability
   with evidence-support, almost guaranteeing collinearity with PD-real.
   v2 rubric isolates the *epistemic-routing question* from the
   *evidence-magnitude question*.

3. PD-REAL RUBRIC: also clarified to focus on *current evidence base*,
   not on *checkability-in-principle*.

DECISION RULE (Brandon-set):
- If AA-vs-PD_real correlation on HOLDOUT < 0.5: AA is REAFFIRMED as
  independent axis (rubric-redesign successfully separated the axes).
- If 0.5 <= corr < 0.7: AA stays PROVISIONAL (partial independence).
- If corr >= 0.7: AA is genuinely demoted (PD-real truly accounts for AA
  even under orthogonal-corpus + redesigned-rubric conditions).
"""
from __future__ import annotations
import json, math, sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).parent.parent / "pass49_wave1"))
from rater_lib import rate, sha256_str, cohens_kappa, percent_agreement


# Each tuple: (claim_text, expected_AA_quadrant_HIGH_or_LOW, expected_PDreal_HIGH_or_LOW)
# AA HIGH = independently verifiable / low-authority-routing
# AA LOW  = must-trust-speaker / high-authority-routing
CLAIMS_2x2 = [
    # Q1: HighAA + HighPD (5)
    ("Water boils at 100 degrees Celsius at one atmosphere of pressure.", "H", "H"),
    ("The Pythagorean theorem holds for all right triangles in Euclidean geometry.", "H", "H"),
    ("If you drop a stone and a feather in a vacuum chamber, they hit the bottom at the same time.", "H", "H"),
    ("Adding two even integers always produces an even integer.", "H", "H"),
    ("A pendulum's period depends on its length and local gravity, not on the mass of the bob.", "H", "H"),
    # Q2: LowAA + HighPD (5)  [must-trust-experts; well-established]
    ("LIGO detected gravitational waves from a binary black hole merger on September 14, 2015.", "L", "H"),
    ("The Higgs boson was observed at CERN in 2012 with statistical significance exceeding 5 sigma.", "L", "H"),
    ("The human genome contains approximately 20,000 protein-coding genes, per the latest GENCODE annotation.", "L", "H"),
    ("Type 1a supernovae have a characteristic light curve that allows them to be used as standard candles.", "L", "H"),
    ("The IPCC AR6 report concluded global average surface temperature has risen approximately 1.1 C since pre-industrial times.", "L", "H"),
    # Q3: HighAA + LowPD (5)  [independently checkable but weakly-supported]
    ("The next coin flip with this fair coin will land heads.", "H", "L"),
    ("There are exactly 7,432 grains of rice in this jar right now.", "H", "L"),
    ("It will rain in Seattle on August 13, 2027.", "H", "L"),
    ("The total number of leaves on this oak tree this morning is even.", "H", "L"),
    ("The price of Bitcoin will be above $100,000 USD on December 31, 2026.", "H", "L"),
    # Q4: LowAA + LowPD (5)  [must-trust-speaker AND weakly-supported]
    ("I had a vivid dream about my late grandmother last Tuesday night.", "L", "L"),
    ("My great-great-grandfather emigrated from County Cork in 1851 according to family oral history.", "L", "L"),
    ("During my meditation retreat I experienced a moment of non-dual awareness.", "L", "L"),
    ("The anonymous internet rumor claims a major tech CEO will resign next quarter.", "L", "L"),
    ("A psychic told my friend her aunt would call within three days, and she did.", "L", "L"),
]

CLAIMS = [c[0] for c in CLAIMS_2x2]
EXPECTED = [(c[1], c[2]) for c in CLAIMS_2x2]


REDESIGNED_RUBRIC = """For each claim, rate it on TWO axes, integer 0-10.

AXIS 1 — AA (Authority Axis): epistemic-routing question.
  TO EVALUATE THE CLAIM, must the rater route through trust in a particular
  speaker/source/institution beyond what they could in principle check
  themselves with reasonable resources?
  - 10 = NO authority-routing required. The claim is the kind of thing any
    competent person could verify themselves in principle, even if they
    haven't bothered. (e.g., "water boils at 100C" — anyone with a
    thermometer can check; "2+2=4" — anyone can compute.)
  - 0 = TOTAL authority-routing required. To accept the claim, you must
    trust a specific source whose reliability you cannot independently
    verify. (e.g., "I personally had a vision last Tuesday" — only the
    speaker has access to the evidence.)
  - 5 = MIXED. You could in principle check it yourself but the cost of
    independent verification is high enough that in practice you route
    through experts.

  IMPORTANT: AA is NOT about how well-supported the claim is by current
  evidence. AA is about WHETHER the warrant for belief routes through
  trusting-a-source. A weakly-supported claim that is independently
  checkable scores HIGH on AA. A well-supported claim that requires
  trusting expert institutions scores LOW on AA.

AXIS 2 — PD_real: evidence-support magnitude question.
  HOW MUCH current independent evidence supports the claim being TRUE?
  - 10 = overwhelming, well-replicated, multi-source evidence.
  - 0 = no current evidence one way or the other; speculation only.
  - 5 = some evidence but limited/disputed.

  IMPORTANT: PD_real is NOT about who supplies the evidence; PD_real is
  about how much evidence has accumulated. A LIGO detection has high
  PD_real EVEN IF you must trust the LIGO collaboration to access it.

The two axes are designed to be ORTHOGONAL. A claim can be:
- High AA + High PD: simple physics anyone can re-check, well-established.
- Low AA + High PD: institutional discoveries you must trust experts on.
- High AA + Low PD: simple factual prediction anyone can check, but no
  current evidence.
- Low AA + Low PD: speaker-only claims with no independent support.

Return a JSON list: [{"id": int, "AA": int, "PD_real": int}, ...] one entry per claim.

CLAIMS:
"""


def main():
    prompt = REDESIGNED_RUBRIC + "\n".join(f"{i}. {c}" for i, c in enumerate(CLAIMS))
    corpus_sha = sha256_str(json.dumps(CLAIMS_2x2))
    rA = rate("A", prompt, max_tokens=8000)
    rB = rate("B", prompt, max_tokens=8000)
    dA = {int(it["id"]): it for it in rA}
    dB = {int(it["id"]): it for it in rB}
    ids = sorted(set(dA) & set(dB))

    import random
    rnd = random.Random(int(corpus_sha[:8], 16))
    perm = ids.copy(); rnd.shuffle(perm)
    cut = int(len(perm)*0.6)
    tune_ids = sorted(perm[:cut]); holdout_ids = sorted(perm[cut:])

    def pearson(xs, ys):
        n = len(xs)
        if n < 2: return float("nan")
        mx, my = sum(xs)/n, sum(ys)/n
        num = sum((xs[i]-mx)*(ys[i]-my) for i in range(n))
        dx = math.sqrt(sum((x-mx)**2 for x in xs))
        dy = math.sqrt(sum((y-my)**2 for y in ys))
        return num/(dx*dy) if dx*dy>1e-12 else float("nan")

    # Per-rater AA-PDreal correlation; report both raters
    def axis_corr_for_rater(d, idset):
        return pearson([d[i]["AA"] for i in idset], [d[i]["PD_real"] for i in idset])

    holdout_corr_A = axis_corr_for_rater(dA, holdout_ids)
    holdout_corr_B = axis_corr_for_rater(dB, holdout_ids)
    holdout_corr_avg = (abs(holdout_corr_A) + abs(holdout_corr_B)) / 2

    # Tune for transparency
    tune_corr_A = axis_corr_for_rater(dA, tune_ids)
    tune_corr_B = axis_corr_for_rater(dB, tune_ids)

    # AA inter-rater agreement
    aa_kappa = cohens_kappa([dA[i]["AA"] for i in holdout_ids],
                            [dB[i]["AA"] for i in holdout_ids])
    aa_pa = percent_agreement([dA[i]["AA"] for i in holdout_ids],
                              [dB[i]["AA"] for i in holdout_ids])

    # Quadrant-recovery: for each claim, did the AA rating match the
    # *intended* quadrant? (HIGH AA expected if EXPECTED[i][0]=='H'.)
    def quad_recovery(d):
        hits = 0
        for i in holdout_ids:
            exp_aa, exp_pd = EXPECTED[i]
            aa_high = d[i]["AA"] >= 6
            pd_high = d[i]["PD_real"] >= 6
            aa_match = (aa_high == (exp_aa == "H"))
            pd_match = (pd_high == (exp_pd == "H"))
            if aa_match and pd_match:
                hits += 1
        return hits / len(holdout_ids)

    quad_recovery_A = quad_recovery(dA)
    quad_recovery_B = quad_recovery(dB)

    # Brandon decision rule
    if holdout_corr_avg < 0.5:
        verdict = "AA_REAFFIRMED_INDEPENDENT"
    elif holdout_corr_avg < 0.7:
        verdict = "AA_PROVISIONAL_PARTIAL_INDEPENDENCE"
    else:
        verdict = "AA_DEMOTED_PD_REAL_ACCOUNTS_FOR_AA"

    out = {
        "test_id": "T49-1_v2_AA_orthogonal_corpus_redesigned_rubric",
        "rater_independence": "same_model_two_personas (Claude, temp 0.0 vs 0.3)",
        "pilot_flag": True,
        "n_claims": len(ids),
        "corpus_sha256": corpus_sha,
        "design": "2x2 orthogonal: HighAA/LowAA x HighPD/LowPD, 5 per quadrant",
        "holdout_ids": holdout_ids, "tune_ids": tune_ids,
        "ratings_A": dA, "ratings_B": dB,
        "expected_quadrant": {i: EXPECTED[i] for i in ids},
        "metrics": {
            "holdout_AA_PDreal_corr_rater_A": holdout_corr_A,
            "holdout_AA_PDreal_corr_rater_B": holdout_corr_B,
            "holdout_AA_PDreal_corr_mean_abs": holdout_corr_avg,
            "tune_AA_PDreal_corr_rater_A": tune_corr_A,
            "tune_AA_PDreal_corr_rater_B": tune_corr_B,
            "holdout_AA_inter_rater_kappa": aa_kappa,
            "holdout_AA_inter_rater_PA": aa_pa,
            "holdout_quadrant_recovery_A": quad_recovery_A,
            "holdout_quadrant_recovery_B": quad_recovery_B,
        },
        "brandon_decision_rule": {
            "lt_0.5": "AA_REAFFIRMED_INDEPENDENT",
            "0.5_to_0.7": "AA_PROVISIONAL_PARTIAL_INDEPENDENCE",
            "gte_0.7": "AA_DEMOTED_PD_REAL_ACCOUNTS_FOR_AA",
        },
        "verdict": verdict,
    }
    Path(__file__).parent.joinpath("t49_1_v2_results.json").write_text(json.dumps(out, indent=2, default=str))
    print(f"T49-1 v2 verdict: {verdict}")
    print(f"  HOLDOUT |corr(AA, PDreal)| mean = {holdout_corr_avg:.3f}")
    print(f"    (rater A: {holdout_corr_A:.3f}; rater B: {holdout_corr_B:.3f})")
    print(f"  HOLDOUT AA inter-rater κ = {aa_kappa:.3f}; PA = {aa_pa:.3f}")
    print(f"  HOLDOUT quadrant recovery — A: {quad_recovery_A:.2%}; B: {quad_recovery_B:.2%}")
    return out


if __name__ == "__main__":
    main()
