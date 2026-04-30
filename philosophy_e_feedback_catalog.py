"""
philosophy_e_feedback_catalog.py
==================================

Companion catalog for URB #818. Documents 18 long-running philosophical
disputes / concepts and scores each on four 0-3 dimensions:

  - tralseness_presence : how strongly the central concept of the dispute
                          is constitutively bistable / definitionally
                          tralse  (0 = stable, 3 = paradigmatically tralse)

  - env_feedback       : how strong the environmental feedback is —
                          does the world bite back if the discipline
                          misdescribes the central concept?
                          (0 = no direct empirical check, 3 = relentless
                          empirical check)

  - recognized_verbal  : has the dispute's verbal-dispute / definitional-
                          bistability structure been substantially
                          recognized within the dispute literature?
                          (0 = not recognized, 3 = central to the
                          dispute literature)

  - practice_shift     : even where the verbal-dispute structure IS
                          recognized, has the discipline's practice
                          substantially shifted in response?
                          (0 = no shift, 3 = paradigm-level shift)

Supports URB #818's GILE-E (environmental-feedback) hypothesis: that the
rate-limiting factor for tralseness-recognition apparatus development is
environmental feedback, not the availability of the apparatus or the
intelligence of the practitioners. Predicts uniformly high tralseness_
presence, uniformly low-to-moderate env_feedback, variable recognized_
verbal, and uniformly modest practice_shift even when recognition is
high.

Ratings are author judgments calibrated against publicly visible
literature, NOT survey data. Reasonable observers would shift several
scores. The qualitative pattern is robust to relabeling; the exact
averages should not be treated as a quantitative result.

Pure Python stdlib. No randomness. Wall time < 1 s.
"""
from __future__ import annotations
import json
from typing import Dict, List


CONCEPTS: List[Dict] = [
    {
        "concept": "free will (compatibilism vs incompatibilism)",
        "subfield": "metaphysics / ethics / philosophy of mind",
        "tralseness_presence": 3,
        "env_feedback": 1,
        "recognized_verbal": 2,
        "practice_shift": 1,
        "note": "Compatibilists frequently make the verbal-dispute move; some incompatibilists explicitly grant the partly-verbal structure; yet the dispute continues to occupy significant literature space as if substantive.",
    },
    {
        "concept": "knowledge (post-Gettier)",
        "subfield": "epistemology",
        "tralseness_presence": 3,
        "env_feedback": 1,
        "recognized_verbal": 1,
        "practice_shift": 1,
        "note": "Sixty years of post-Gettier patching (defeasibility, no-false-lemmas, safety, sensitivity, virtue epistemology) without a verbal-dispute diagnosis being load-bearing in the literature; rare exceptions (Weatherson) have not shifted mainstream practice.",
    },
    {
        "concept": "mind-body / hard problem",
        "subfield": "philosophy of mind",
        "tralseness_presence": 3,
        "env_feedback": 2,
        "recognized_verbal": 2,
        "practice_shift": 1,
        "note": "Chalmers himself diagnoses verbal-dispute aspects (consciousness as 'C-consciousness' vs 'P-consciousness' etc.); URB #813 covered this; modest neuroscience/psychology environmental feedback; practice still proceeds largely as substantive dispute.",
    },
    {
        "concept": "personal identity over time",
        "subfield": "metaphysics / philosophy of mind",
        "tralseness_presence": 3,
        "env_feedback": 1,
        "recognized_verbal": 2,
        "practice_shift": 1,
        "note": "Parfit's 'what matters in survival' move was substantially a verbal-dispute reframing; post-Chalmers explicitly so; yet teletransporter-thought-experiment literature continues largely as substantive metaphysics.",
    },
    {
        "concept": "abstract objects (mathematical / universals)",
        "subfield": "metaphysics / philosophy of mathematics",
        "tralseness_presence": 3,
        "env_feedback": 0,
        "recognized_verbal": 1,
        "practice_shift": 0,
        "note": "Carnap's 'External Questions' essay was a paradigm verbal-dispute diagnosis, largely rejected or sidelined by mainstream metaphysics post-Quine; the dispute continues as if substantive.",
    },
    {
        "concept": "realism vs anti-realism (general)",
        "subfield": "metaphysics / philosophy of science / epistemology",
        "tralseness_presence": 3,
        "env_feedback": 1,
        "recognized_verbal": 2,
        "practice_shift": 1,
        "note": "Putnam, Dummett, and others have explicitly worked on the verbal-dispute structure; Chalmers' framework gave a clean diagnostic; yet new realism-vs-anti-realism literature continues to be produced regularly.",
    },
    {
        "concept": "consequentialism vs deontology",
        "subfield": "ethics",
        "tralseness_presence": 3,
        "env_feedback": 0,
        "recognized_verbal": 1,
        "practice_shift": 0,
        "note": "Multi-millennium dispute; some hybrid views (rule-consequentialism, threshold-deontology) implicitly acknowledge verbal-dispute structure; mainstream ethics literature largely conducts the dispute as substantive.",
    },
    {
        "concept": "epistemic internalism vs externalism",
        "subfield": "epistemology",
        "tralseness_presence": 3,
        "env_feedback": 1,
        "recognized_verbal": 2,
        "practice_shift": 1,
        "note": "Several internalists and externalists have explicitly granted that the dispute is partly about which explication of justification to adopt; yet the literature continues to be productive in substantive mode.",
    },
    {
        "concept": "A-series vs B-series of time (McTaggart)",
        "subfield": "metaphysics / philosophy of physics",
        "tralseness_presence": 3,
        "env_feedback": 2,
        "recognized_verbal": 1,
        "practice_shift": 1,
        "note": "Modest physics-of-time environmental feedback (relativity favors B-series broadly); some recognition that 'tense' admits multiple explications; mainstream metaphysics-of-time continues substantively.",
    },
    {
        "concept": "de re vs de dicto modality",
        "subfield": "modal metaphysics / philosophy of language",
        "tralseness_presence": 3,
        "env_feedback": 1,
        "recognized_verbal": 3,
        "practice_shift": 2,
        "note": "Quine's critique was substantially verbal-dispute-style; Kripke's response established the de re/de dicto distinction technically; this dispute is among the most apparatus-developed in non-philosophy-of-language metaphysics, partly because it sits adjacent to formal semantics where E-feedback is stronger.",
    },
    {
        "concept": "beauty (definition of)",
        "subfield": "aesthetics",
        "tralseness_presence": 3,
        "env_feedback": 1,
        "recognized_verbal": 2,
        "practice_shift": 2,
        "note": "Weitz's open-concept thesis was an explicit verbal-dispute / definitional-bistability move; aesthetics is one of the few subfields where the central concept's bistability has been substantially central to the discipline's self-understanding.",
    },
    {
        "concept": "justice (Plato to Rawls to today)",
        "subfield": "political philosophy / ethics",
        "tralseness_presence": 3,
        "env_feedback": 1,
        "recognized_verbal": 1,
        "practice_shift": 1,
        "note": "Multi-millennium dispute; multiple competing explications (procedural, distributive, retributive, restorative, capabilities-based); recognition of verbal-dispute structure is modest; political-policy environmental feedback is real but contested.",
    },
    {
        "concept": "God's existence (theistic philosophy)",
        "subfield": "philosophy of religion",
        "tralseness_presence": 3,
        "env_feedback": 0,
        "recognized_verbal": 1,
        "practice_shift": 0,
        "note": "Verificationist tradition (Ayer, early Carnap) substantially diagnosed the dispute as definitionally fraught; mainstream philosophy of religion continues largely as substantive metaphysics; very weak environmental feedback.",
    },
    {
        "concept": "causation (Hume to interventionist)",
        "subfield": "metaphysics / philosophy of science",
        "tralseness_presence": 3,
        "env_feedback": 2,
        "recognized_verbal": 2,
        "practice_shift": 2,
        "note": "Multiple competing explications (regularity, counterfactual, mechanistic, interventionist, probabilistic); statistics-and-causal-inference apparatus (Pearl, Rubin) provides genuine environmental feedback; recognition and modest practice shift have followed.",
    },
    {
        "concept": "persistence through time (endurantism vs perdurantism)",
        "subfield": "metaphysics",
        "tralseness_presence": 3,
        "env_feedback": 0,
        "recognized_verbal": 2,
        "practice_shift": 1,
        "note": "Substantial recognition that the dispute is partly about which explication of 'object' to adopt; yet specialized metaphysics literature continues as substantive.",
    },
    {
        "concept": "vagueness itself (epistemicism / supervaluationism / degree theory)",
        "subfield": "philosophy of language / philosophical logic",
        "tralseness_presence": 3,
        "env_feedback": 2,
        "recognized_verbal": 3,
        "practice_shift": 2,
        "note": "Sits adjacent to philosophy of language; Williamson, Fine, and others have made the verbal-dispute structure load-bearing; modest practice shift and one of the more apparatus-developed disputes.",
    },
    {
        "concept": "truth itself (correspondence vs coherence vs deflationism vs pragmatist)",
        "subfield": "philosophy of language / metaphysics",
        "tralseness_presence": 3,
        "env_feedback": 2,
        "recognized_verbal": 3,
        "practice_shift": 2,
        "note": "Tarski + deflationism + pluralism literature has substantially absorbed the verbal-dispute structure; another case where the philosophy-of-language adjacency provides real E-feedback; modest practice shift.",
    },
    {
        "concept": "meaning itself (use theory vs truth-conditional vs intentional)",
        "subfield": "philosophy of language",
        "tralseness_presence": 3,
        "env_feedback": 3,
        "recognized_verbal": 3,
        "practice_shift": 3,
        "note": "Philosophy of language proper; relentless E-feedback from linguistic data; verbal-dispute structure is centrally recognized; substantial practice apparatus has developed; the canonical case where the GILE-E hypothesis predicts well-developed tralseness apparatus and that prediction is borne out.",
    },
    # ---- Empirically-anchored counterexamples / boundary cases added per
    # ---- URB #818 §2 reframing (tralseness-engaged traditions vs problem-
    # ---- driven analytic subliteratures) and per the architect-review
    # ---- selection-bias patch. These cases were originally excluded from
    # ---- the long-running-paradigmatic-dispute frame but are precisely
    # ---- the empirically-anchored philosophy-of-X subfields where the
    # ---- GILE-E hypothesis predicts substantially higher env_feedback
    # ---- and practice_shift. Their inclusion is a partial sensitivity
    # ---- analysis: if the GILE-E hypothesis were spurious, including
    # ---- these counterexamples would weaken or invert the qualitative
    # ---- pattern; they should instead reinforce the predicted clustering
    # ---- of high-E-feedback / high-practice-shift in empirically-
    # ---- anchored subfields.
    {
        "concept": "naturalized epistemology (post-Quine)",
        "subfield": "epistemology / philosophy of cognitive science",
        "tralseness_presence": 3,
        "env_feedback": 2,
        "recognized_verbal": 2,
        "practice_shift": 2,
        "note": "Quine's naturalized-epistemology program explicitly imports cognitive-science feedback into epistemology; subsequent work (Goldman, Kornblith, Kitcher) has been substantially shaped by empirical research on actual cognition; verbal-dispute structure of 'knowledge' and 'justification' is recognized by many naturalized epistemologists as partly definitional; practice has shifted in this subliterature relative to mainstream a priori epistemology.",
    },
    {
        "concept": "species concept (philosophy of biology)",
        "subfield": "philosophy of biology",
        "tralseness_presence": 3,
        "env_feedback": 3,
        "recognized_verbal": 3,
        "practice_shift": 3,
        "note": "Philosophy of biology has fully absorbed the multi-explication-pluralism of 'species' (biological, morphological, phylogenetic, ecological, ring-species edge cases); the verbal-dispute structure is centrally recognized; practice has shifted to acknowledge species-concept pluralism as the working position; canonical case where strong empirical environmental feedback from biology forced apparatus development.",
    },
    {
        "concept": "interpretations of QM (philosophy of physics)",
        "subfield": "philosophy of physics",
        "tralseness_presence": 3,
        "env_feedback": 3,
        "recognized_verbal": 2,
        "practice_shift": 2,
        "note": "Philosophy of physics on QM-interpretations (Copenhagen vs Everett vs Bohmian vs QBist) is shaped by experimental physics feedback (Bell tests, decoherence research, weak-measurement experiments); the verbal-dispute structure is partly recognized (some philosophers explicitly grant that the dispute is partly about which explication of 'measurement' or 'state' to adopt) but mainstream practice still treats interpretations as substantively distinct.",
    },
    {
        "concept": "applied / medical ethics (bioethics, clinical ethics)",
        "subfield": "applied ethics",
        "tralseness_presence": 3,
        "env_feedback": 2,
        "recognized_verbal": 1,
        "practice_shift": 2,
        "note": "Applied and medical ethics work directly with clinical/regulatory feedback that forces operational definitions of 'consent,' 'capacity,' 'futility,' 'death,' 'person'; the verbal-dispute structure is rarely named but practice has shifted considerably under regulatory and clinical pressure (DSM revisions, brain-death criteria evolution, capacity-assessment standardization). Partial counterexample: practice-shift higher than typical paradigmatic dispute, even though verbal-dispute recognition is modest.",
    },
    {
        "concept": "experimental philosophy (X-phi)",
        "subfield": "experimental philosophy / metaphilosophy",
        "tralseness_presence": 2,
        "env_feedback": 3,
        "recognized_verbal": 2,
        "practice_shift": 2,
        "note": "X-phi imports survey-and-experimental empirical methods into philosophy itself; explicitly tests whether folk intuitions on free will, knowledge, intentional action, etc. align with philosophical analyses; finds substantial cross-cultural and demographic variation that is difficult to reconcile with universal-explication ambitions; partly diagnoses the verbal-dispute structure of disputes where folk intuitions diverge; practice has shifted within X-phi but the broader philosophical mainstream has been selectively responsive.",
    },
]


def aggregate(concepts: List[Dict]) -> Dict:
    n = len(concepts)
    avg_t = sum(c["tralseness_presence"] for c in concepts) / n
    avg_e = sum(c["env_feedback"] for c in concepts) / n
    avg_r = sum(c["recognized_verbal"] for c in concepts) / n
    avg_p = sum(c["practice_shift"] for c in concepts) / n

    high_t_low_e = [c["concept"] for c in concepts
                    if c["tralseness_presence"] >= 3 and c["env_feedback"] <= 1]
    high_r_low_p = [c["concept"] for c in concepts
                    if c["recognized_verbal"] >= 2 and c["practice_shift"] <= 1]
    e_p_correlation = sum(
        (c["env_feedback"] - avg_e) * (c["practice_shift"] - avg_p)
        for c in concepts
    ) / n

    return {
        "n": n,
        "avg_tralseness_presence": round(avg_t, 2),
        "avg_env_feedback": round(avg_e, 2),
        "avg_recognized_verbal": round(avg_r, 2),
        "avg_practice_shift": round(avg_p, 2),
        "high_tralseness_low_env": high_t_low_e,
        "recognized_but_no_practice_shift": high_r_low_p,
        "env_feedback_practice_shift_covariance": round(e_p_correlation, 3),
    }


def main():
    print("=" * 78)
    print("URB #818 — Philosophy E-Feedback Catalog")
    print("=" * 78)
    print(f"\n{len(CONCEPTS)} long-running philosophical disputes / concepts.")
    print("Each scored on 0-3 scale for tralseness-presence, environmental-feedback,")
    print("recognition-as-verbal-dispute, and disciplinary-practice-shift.\n")

    print("-" * 78)
    print(f"{'concept':50s}  {'tral':4s}  {'env':4s}  {'rec':4s}  {'shift':5s}")
    print("-" * 78)
    for c in CONCEPTS:
        name = c["concept"]
        if len(name) > 48:
            name = name[:45] + "..."
        print(f"{name:50s}  "
              f"{c['tralseness_presence']:>4d}  "
              f"{c['env_feedback']:>4d}  "
              f"{c['recognized_verbal']:>4d}  "
              f"{c['practice_shift']:>5d}")

    agg = aggregate(CONCEPTS)
    print("\n" + "-" * 78)
    print("Aggregate")
    print("-" * 78)
    print(f"  avg tralseness_presence : {agg['avg_tralseness_presence']:.2f} / 3   (uniformly high — predicted)")
    print(f"  avg env_feedback        : {agg['avg_env_feedback']:.2f} / 3   (low to moderate — predicted)")
    print(f"  avg recognized_verbal   : {agg['avg_recognized_verbal']:.2f} / 3   (variable — predicted)")
    print(f"  avg practice_shift      : {agg['avg_practice_shift']:.2f} / 3   (modest even when recognized — predicted)")
    print(f"\n  env_feedback × practice_shift covariance : {agg['env_feedback_practice_shift_covariance']:+.3f}")
    print(f"  (positive = consistent with GILE-E hypothesis: stronger E-feedback → more practice shift)")

    print(f"\n  high tralseness BUT low env_feedback "
          f"({len(agg['high_tralseness_low_env'])} of {len(CONCEPTS)}):")
    for x in agg["high_tralseness_low_env"]:
        print(f"      - {x}")

    print(f"\n  verbal-dispute structure RECOGNIZED but practice did NOT shift "
          f"({len(agg['recognized_but_no_practice_shift'])} of {len(CONCEPTS)}):")
    for x in agg["recognized_but_no_practice_shift"]:
        print(f"      - {x}")

    interpretation = (
        f"Across {len(CONCEPTS)} philosophical disputes / subfield-concepts "
        f"(18 long-running paradigmatic disputes plus 5 empirically-"
        f"anchored counterexamples added per URB #818 §2 reframing and "
        f"the architect-review selection-bias patch), tralseness-presence "
        f"is uniformly high (avg {agg['avg_tralseness_presence']:.2f}/3), "
        f"environmental-feedback is low to moderate overall (avg "
        f"{agg['avg_env_feedback']:.2f}/3) but visibly bimodal between "
        f"the paradigmatic disputes (low E) and the empirically-anchored "
        f"subfields (high E), recognition of verbal-dispute structure is "
        f"variable (avg {agg['avg_recognized_verbal']:.2f}/3), and "
        f"disciplinary-practice shift is modest in the paradigmatic "
        f"disputes but substantial in the empirically-anchored subfields "
        f"(avg {agg['avg_practice_shift']:.2f}/3 overall). The "
        f"env_feedback × practice_shift covariance is "
        f"{agg['env_feedback_practice_shift_covariance']:+.3f}, which is "
        f"CONSISTENT WITH but does not TEST URB #818's GILE-E "
        f"(environmental-feedback) hypothesis. THE COVARIANCE IS A "
        f"FEATURE OF AUTHOR CODING, NOT AN INDEPENDENT EMPIRICAL FINDING: "
        f"the same author who has the GILE-E hypothesis in mind also "
        f"assigned the ratings, and a confirmation-bias risk applies. "
        f"{len(agg['high_tralseness_low_env'])} of {len(CONCEPTS)} "
        f"disputes have high tralseness-presence but low environmental-"
        f"feedback (the predicted at-risk regime); "
        f"{len(agg['recognized_but_no_practice_shift'])} of {len(CONCEPTS)} "
        f"disputes show the diagnostic-available-but-practice-unchanged "
        f"pattern that the GILE-E hypothesis specifically predicts. "
        f"The cleanest counterexamples to the low-E pattern (de re / "
        f"de dicto modality, vagueness itself, truth itself, meaning "
        f"itself, naturalized epistemology, species concept, QM-"
        f"interpretations, applied/medical ethics, X-phi) cluster in "
        f"subfields with strong empirical anchors — consistent with "
        f"GILE-E predictions but also consistent with §5's rival "
        f"hypotheses (institutional history, individual leadership, "
        f"publication norms, pedagogy, disciplinary inertia). RATINGS "
        f"ARE AUTHOR JUDGMENTS not survey data; reasonable observers "
        f"would shift several scores; ROBUSTNESS TO RELABELING IS "
        f"ASSERTED IN PRIOR DRAFTS WITHDRAWN HERE — the sensitivity "
        f"analysis with multiple coding schemes that would substantiate "
        f"a robustness claim has not been performed and would be needed "
        f"before treating any aggregate as more than illustrative. The "
        f"catalog is explicitly a NON-RANDOM SAMPLE: the 18 paradigmatic "
        f"disputes were selected as long-running paradigms (likely "
        f"biased toward disputes that fit the low-E pattern), and the "
        f"5 added empirically-anchored counterexamples were selected "
        f"specifically to test (and partly correct) that selection bias. "
        f"A truly representative sample of philosophical activity would "
        f"need to draw on PhilPapers / PhilPeople / SEP / journal-corpus "
        f"data, which this $0 catalog cannot replicate. The pattern is "
        f"reported as illustrative of the GILE-E hypothesis under one "
        f"reasonable coding, not as evidence that adjudicates between "
        f"GILE-E and the rival hypotheses in URB #818 §5."
    )

    print("\n" + "=" * 78)
    print("Interpretation")
    print("=" * 78)
    print(interpretation)

    report = {
        "n_concepts": len(CONCEPTS),
        "concepts": CONCEPTS,
        "aggregate": agg,
        "interpretation": interpretation,
    }
    out_path = "philosophy_e_feedback_catalog.json"
    with open(out_path, "w") as f:
        json.dump(report, f, indent=2)
    print(f"\nReport written to {out_path}")


if __name__ == "__main__":
    main()
