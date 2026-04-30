"""
academic_concepts_bistability_catalog.py
==========================================

Companion catalog for URB #817. Documents ~20 academic concepts whose
constitutive bistability is well-known *within* their home discipline,
along with an honest assessment of how much each field has developed
explicit literature on the bistability and whether that literature
penetrates undergraduate teaching.

The point is to support URB #817's central claim: most academic
disciplines deal with constitutively tralse concepts as a routine part
of their subject matter, the within-discipline sophistication is often
real and substantial, but the cross-disciplinary theoretical handle on
tralseness as a general phenomenon is largely absent from undergraduate
training in most fields.

NOT empirical research. The "score" fields are author judgments
calibrated against publicly visible literature and curriculum
conventions, not survey data. Reasonable observers would shift several
ratings.

Pure Python stdlib. No randomness. Wall time < 1 s.
"""
from __future__ import annotations
import json
from typing import Dict, List


# Each concept is a record:
#   - "concept": the term in question
#   - "discipline": primary disciplinary home
#   - "bistability_kinds": which kinds of tralseness it exhibits
#       (definitional / contextual / vague / paradigm-shifted / political)
#   - "within_field_lit": how much explicit literature the field has on
#       the concept's bistability  (0 = none, 3 = extensive)
#   - "ugrad_teaching": how much the bistability is foregrounded in
#       standard undergraduate teaching of the field  (0 = ignored,
#       3 = central topic)
#   - "cross_disc_handle": whether the field connects its
#       within-discipline bistability awareness to the broader
#       linguistic / philosophy-of-language / HPS / STS / post-
#       structuralist / conceptual-history tradition on tralseness as a
#       general phenomenon. Scored on the same 0-3 scale as the other
#       two (0 = no connection, 1 = scattered/some, 2 = strong/well-
#       developed, 3 = central / extensively developed). Note that no
#       item in the current catalog is rated 3 on this dimension, which
#       itself reflects URB #817's central observation that the cross-
#       cutting handle is rare in undergraduate-accessible form across
#       most fields.
#   - "note": brief comment
CONCEPTS: List[Dict] = [
    {
        "concept": "consciousness",
        "discipline": "psychology / neuroscience / philosophy of mind",
        "bistability_kinds": ["definitional", "paradigm-shifted"],
        "within_field_lit": 3,
        "ugrad_teaching": 1,
        "cross_disc_handle": 1,
        "note": "Hard-problem and IIT/GWT/HOT debates explicitly involve definitional disputes; psych/neuro intro courses typically do not cover the bistability framing despite extensive philosophy literature; covered in URB #813.",
    },
    {
        "concept": "species",
        "discipline": "biology",
        "bistability_kinds": ["definitional", "vague"],
        "within_field_lit": 3,
        "ugrad_teaching": 2,
        "cross_disc_handle": 0,
        "note": "Mayr/Hull/Ghiselin/Sober species-concept debates are extensive; intro bio mentions the multiple concepts (biological, morphological, phylogenetic, ecological); cross-disciplinary connection to philosophy of language is rare even though the structural pattern matches definitional bistability exactly.",
    },
    {
        "concept": "gene",
        "discipline": "biology / genetics",
        "bistability_kinds": ["definitional", "paradigm-shifted"],
        "within_field_lit": 3,
        "ugrad_teaching": 1,
        "cross_disc_handle": 0,
        "note": "Molecular vs functional vs Mendelian gene concepts diverged after the 1960s; intro genetics typically uses one definition without naming the bistability; molecular biologists are sophisticated locally but rarely connect to general philosophy of language.",
    },
    {
        "concept": "intelligence",
        "discipline": "psychology / AI",
        "bistability_kinds": ["definitional", "vague", "political"],
        "within_field_lit": 3,
        "ugrad_teaching": 1,
        "cross_disc_handle": 0,
        "note": "g vs multiple-intelligences vs CHC vs operational AGI definitions are deeply contested; intro psych mentions IQ debates but rarely frames them as definitional-bistability problems; the AGI literature has begun to grapple with the bistability explicitly (Chollet et al.) but mostly without connecting to the tralseness tradition.",
    },
    {
        "concept": "race",
        "discipline": "anthropology / biology / sociology",
        "bistability_kinds": ["definitional", "political", "paradigm-shifted"],
        "within_field_lit": 3,
        "ugrad_teaching": 2,
        "cross_disc_handle": 1,
        "note": "Biological-vs-social-construct debates are foregrounded in undergraduate anthropology/sociology; the cross-disciplinary handle is more developed here than for most concepts on this list, partly because the political stakes have forced the field to be explicit about the definitional structure.",
    },
    {
        "concept": "depression",
        "discipline": "psychiatry",
        "bistability_kinds": ["definitional", "vague"],
        "within_field_lit": 2,
        "ugrad_teaching": 1,
        "cross_disc_handle": 0,
        "note": "DSM-III through DSM-5 have repeatedly renegotiated the diagnostic criteria; psychiatrists are sophisticated about the renegotiation but the field rarely frames it as an instance of general definitional bistability; the operational definitions are taught as if they were stable bivalent categories.",
    },
    {
        "concept": "recession",
        "discipline": "economics",
        "bistability_kinds": ["definitional", "operational"],
        "within_field_lit": 2,
        "ugrad_teaching": 1,
        "cross_disc_handle": 0,
        "note": "NBER definition vs technical 'two consecutive quarters of GDP decline' definition; the bistability is well-known to working economists; intro macroeconomics typically presents one definition without surfacing the structure.",
    },
    {
        "concept": "democracy",
        "discipline": "political science",
        "bistability_kinds": ["definitional", "political", "vague"],
        "within_field_lit": 3,
        "ugrad_teaching": 2,
        "cross_disc_handle": 1,
        "note": "Schumpeterian, deliberative, participatory, liberal, illiberal definitions all have established literatures; intro political science covers the conceptual diversity; the cross-disciplinary handle is partially developed because political theory overlaps with philosophy.",
    },
    {
        "concept": "fitness",
        "discipline": "evolutionary biology",
        "bistability_kinds": ["definitional", "operational"],
        "within_field_lit": 3,
        "ugrad_teaching": 1,
        "cross_disc_handle": 0,
        "note": "Propensity vs realized vs inclusive vs gene-centric fitness; substantial philosophy-of-biology literature; intro evolution typically uses a single operational definition without surfacing the bistability.",
    },
    {
        "concept": "mass",
        "discipline": "physics",
        "bistability_kinds": ["paradigm-shifted"],
        "within_field_lit": 2,
        "ugrad_teaching": 1,
        "cross_disc_handle": 0,
        "note": "Newtonian inertial-vs-gravitational mass vs relativistic invariant-vs-relativistic mass; the bistability across paradigms is well-known to physicists but typically taught as 'we now use the better definition' rather than as a Kuhnian definitional shift; classic illustration of paradigm-shift bistability.",
    },
    {
        "concept": "person",
        "discipline": "law / ethics / philosophy",
        "bistability_kinds": ["definitional", "political"],
        "within_field_lit": 3,
        "ugrad_teaching": 2,
        "cross_disc_handle": 2,
        "note": "Abortion, animal-rights, AI-personhood debates all turn on the definition; legal scholars and ethicists are explicit about the bistability and the cross-disciplinary handle is well-developed here because the field is philosophy-adjacent.",
    },
    {
        "concept": "model",
        "discipline": "many (statistics / science / philosophy / CS)",
        "bistability_kinds": ["definitional", "cross-disciplinary"],
        "within_field_lit": 1,
        "ugrad_teaching": 0,
        "cross_disc_handle": 0,
        "note": "Statistical fit vs mechanistic explanation vs formal logical structure vs computational simulation vs scale model; cross-disciplinary collaborations regularly stumble on this; rarely surfaced as a definitional problem in any single discipline's teaching.",
    },
    {
        "concept": "theory",
        "discipline": "many",
        "bistability_kinds": ["definitional", "cross-disciplinary"],
        "within_field_lit": 1,
        "ugrad_teaching": 1,
        "cross_disc_handle": 1,
        "note": "Hypothesis vs established framework vs axiomatic system vs interpretive lens; the everyday-vs-scientific bistability is familiar (the 'just a theory' confusion in evolution debates) but the deeper cross-disciplinary diversity is rarely surfaced.",
    },
    {
        "concept": "function",
        "discipline": "math / biology / CS / sociology",
        "bistability_kinds": ["definitional", "cross-disciplinary"],
        "within_field_lit": 1,
        "ugrad_teaching": 0,
        "cross_disc_handle": 0,
        "note": "Mathematical mapping vs biological role vs computational subroutine vs social purpose; each field uses 'function' fluently in its own sense; cross-disciplinary translation is regularly trip-causing and rarely flagged.",
    },
    {
        "concept": "system",
        "discipline": "many",
        "bistability_kinds": ["definitional", "cross-disciplinary"],
        "within_field_lit": 1,
        "ugrad_teaching": 0,
        "cross_disc_handle": 0,
        "note": "Formal axiomatic system vs dynamical system vs ecological system vs organizational system vs computational system; pervasive cross-disciplinary polysemy.",
    },
    {
        "concept": "harm",
        "discipline": "law / ethics / public policy / AI safety",
        "bistability_kinds": ["definitional", "vague", "political"],
        "within_field_lit": 2,
        "ugrad_teaching": 1,
        "cross_disc_handle": 1,
        "note": "Physical vs psychological vs financial vs reputational vs offense; harm-principle debates in political philosophy are extensive; AI safety has imported the concept with mostly implicit definitions; the bistability is real and consequential.",
    },
    {
        "concept": "consent",
        "discipline": "law / ethics / medicine / AI",
        "bistability_kinds": ["definitional", "vague", "operational"],
        "within_field_lit": 2,
        "ugrad_teaching": 1,
        "cross_disc_handle": 0,
        "note": "Informed-consent in medicine vs contractual consent in law vs sexual consent vs data-consent in tech; the cross-disciplinary handle is largely absent despite the practical stakes.",
    },
    {
        "concept": "addiction",
        "discipline": "psychiatry / neuroscience / sociology",
        "bistability_kinds": ["definitional", "vague", "political"],
        "within_field_lit": 2,
        "ugrad_teaching": 1,
        "cross_disc_handle": 0,
        "note": "Disease model vs behavioral model vs social model; DSM has shifted multiple times (substance dependence vs substance use disorder); intro psych typically presents one model without surfacing the bistability.",
    },
    {
        "concept": "art",
        "discipline": "aesthetics / art history",
        "bistability_kinds": ["definitional", "paradigm-shifted"],
        "within_field_lit": 3,
        "ugrad_teaching": 2,
        "cross_disc_handle": 1,
        "note": "Open-concept (Weitz) vs institutional (Dickie) vs aesthetic-property vs historical (Levinson) definitions; aesthetics is one of the few fields whose primary literature explicitly engages with definitional bistability of the central concept.",
    },
    {
        "concept": "set",
        "discipline": "mathematics / foundations",
        "bistability_kinds": ["definitional", "foundational"],
        "within_field_lit": 3,
        "ugrad_teaching": 0,
        "cross_disc_handle": 1,
        "note": "Naive set theory vs ZFC vs NBG vs Quine's NF vs constructive vs categorical foundations; a clear case where math's working core operates in stipulated-explication mode (URB §2) but the foundations have lively bistability that intro math courses do not surface.",
    },
]


def aggregate(concepts: List[Dict]) -> Dict:
    n = len(concepts)
    avg_lit = sum(c["within_field_lit"] for c in concepts) / n
    avg_teach = sum(c["ugrad_teaching"] for c in concepts) / n
    avg_cross = sum(c["cross_disc_handle"] for c in concepts) / n

    high_lit_low_teach = [
        c["concept"] for c in concepts
        if c["within_field_lit"] >= 2 and c["ugrad_teaching"] <= 1
    ]
    high_lit_low_cross = [
        c["concept"] for c in concepts
        if c["within_field_lit"] >= 2 and c["cross_disc_handle"] == 0
    ]
    no_cross_handle = [
        c["concept"] for c in concepts if c["cross_disc_handle"] == 0
    ]
    return {
        "n": n,
        "avg_within_field_lit": round(avg_lit, 2),
        "avg_ugrad_teaching": round(avg_teach, 2),
        "avg_cross_disc_handle": round(avg_cross, 2),
        "high_lit_low_teach": high_lit_low_teach,
        "high_lit_low_cross": high_lit_low_cross,
        "no_cross_handle": no_cross_handle,
    }


def main():
    print("=" * 76)
    print("URB #817 — Academic Concepts Bistability Catalog")
    print("=" * 76)
    print(f"\nTotal concepts cataloged: {len(CONCEPTS)}")
    print(f"Each scored on 0-3 scale for within-field literature, "
          f"undergrad teaching, and cross-disciplinary handle.\n")

    print("-" * 76)
    print(f"{'concept':25s}  {'lit':4s}  {'teach':6s}  {'cross':6s}")
    print("-" * 76)
    for c in CONCEPTS:
        print(f"{c['concept']:25s}  "
              f"{c['within_field_lit']:>4d}  "
              f"{c['ugrad_teaching']:>6d}  "
              f"{c['cross_disc_handle']:>6d}")

    agg = aggregate(CONCEPTS)
    print("\n" + "-" * 76)
    print("Aggregate")
    print("-" * 76)
    print(f"  avg within-field literature       : {agg['avg_within_field_lit']:.2f} / 3")
    print(f"  avg undergrad teaching foreground : {agg['avg_ugrad_teaching']:.2f} / 3")
    print(f"  avg cross-disc tralseness handle  : {agg['avg_cross_disc_handle']:.2f} / 3")
    print(f"\n  high within-field lit but low ugrad teaching ({len(agg['high_lit_low_teach'])}):")
    for x in agg["high_lit_low_teach"]:
        print(f"      - {x}")
    print(f"\n  high within-field lit but no cross-disc handle ({len(agg['high_lit_low_cross'])}):")
    for x in agg["high_lit_low_cross"]:
        print(f"      - {x}")
    print(f"\n  no cross-disc handle ({len(agg['no_cross_handle'])}):")
    for x in agg["no_cross_handle"]:
        print(f"      - {x}")

    interpretation = (
        f"Across {len(CONCEPTS)} academic concepts spanning many "
        f"disciplines, average within-field literature on the concept's "
        f"bistability is {agg['avg_within_field_lit']:.2f}/3 (substantial; "
        f"local sophistication is real), average undergraduate-teaching "
        f"foregrounding is {agg['avg_ugrad_teaching']:.2f}/3 (modest; the "
        f"bistability is rarely central to introductory teaching), and "
        f"average cross-disciplinary connection to the linguistic / "
        f"philosophy-of-language tradition on tralseness as a general "
        f"phenomenon is {agg['avg_cross_disc_handle']:.2f}/3 (low; "
        f"{len(agg['no_cross_handle'])} of {len(CONCEPTS)} concepts have "
        f"essentially no cross-disciplinary handle). "
        f"{len(agg['high_lit_low_teach'])} concepts have substantial "
        f"within-field literature on the bistability but only modest "
        f"undergrad-teaching foregrounding, and "
        f"{len(agg['high_lit_low_cross'])} have substantial within-field "
        f"literature but no cross-disciplinary handle. "
        f"This pattern supports URB #817's central claim: working "
        f"academics in most fields are sophisticated about the "
        f"bistability of THEIR OWN field's terms, but the cross-cutting "
        f"theoretical handle (Frege/Carnap/Strawson/Chalmers tradition) "
        f"is mostly absent from non-specialist training. The gap is in "
        f"cross-disciplinary transferable vocabulary, not in local "
        f"discipline-specific sophistication. RATINGS ARE AUTHOR "
        f"JUDGMENTS, not survey data; reasonable observers would shift "
        f"several scores; the qualitative pattern (high local lit + low "
        f"cross-disc handle) is robust to relabeling but the exact "
        f"averages should not be treated as a quantitative result."
    )

    print("\n" + "=" * 76)
    print("Interpretation")
    print("=" * 76)
    print(interpretation)

    report = {
        "n_concepts": len(CONCEPTS),
        "concepts": CONCEPTS,
        "aggregate": agg,
        "interpretation": interpretation,
    }
    out_path = "academic_concepts_bistability_catalog.json"
    with open(out_path, "w") as f:
        json.dump(report, f, indent=2)
    print(f"\nReport written to {out_path}")


if __name__ == "__main__":
    main()
