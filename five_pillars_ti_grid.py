"""
five_pillars_ti_grid.py

Companion script to URB #821. Extends URB #820's 4-pillar grid
(EXP/RAD/ANA/HOL) with the fifth pillar PRA (PRAGMATIC) scored
0-3 per URB #821 §2 operationalization:

  - PRA=0 (Pure theory): no application path; no working artifact;
    no engineering or business deliverable downstream.

  - PRA=1 (Speculative application sketches): imagined applications
    or thought-experiment use cases without working artifact.

  - PRA=2 (Working code/prototypes/experiments without external
    validation): working artifacts performing concrete operations
    on real or synthetic data, deployed and reproducible, but
    without paying customers, independent replication, or wide
    deployment.

  - PRA=3 (External validation): paying customers OR independent
    replication OR wide deployment OR regulatory clearance. The
    only pillar that is constitutively externally adjudicated;
    the originator alone cannot grant it.

Per URB #821 §5: the Five Pillars are reframed structurally as a
CONJUNCTIVE uniqueness claim — joint satisfaction of all 5 pillars
at >=2 — rather than a sum-of-scores claim.

Author-coded. Same confirmation-bias risk as URB #820 §8.1
AMPLIFIED because PRA was added in URB #821 to articulate
Brandon's pushback, AND the additional PRA construct-validity
risk per URB #821 §4.3 (Brandon decides what counts as a TI
Sigma application).

Pure stdlib. No randomness. Wall < 1 s.
"""

import json
from pathlib import Path

# Field tuples extended from URB #820's 26-field catalog with PRA
# column. Format: field name, EXP, RAD, ANA, HOL, PRA, RAD anchor,
# PRA anchor, note.
FIELDS = [
    {
        "field": "TI Sigma",
        "exp": 2, "rad": 3, "ana": 3, "hol": 3, "pra": 2,
        "rad_anchor": "GILE/MR/tralse 5-valued logic + constitutive-tralseness-of-language hard core",
        "pra_anchor": "GSA v2 paper-trading on Alpaca; Mood Amplifier Hub (biometric integration); Focus Amplifier 7-mode; Mycelial Resonance Engine v2; Kalshi integration; ARC-AGI TI Sigma Solver; 5 long-running Replit workflows; ~800 URB companion Python scripts; Lean4 formalization of all 6 Millennium Prize Problems. PRA=2 firm: working artifacts; no paying customers, no independent replication of working systems, no wide external deployment, no regulatory clearance. PRA=3 honestly not yet earned.",
        "note": "Provisional scores per URB #820 §4.4 + URB #821 §4: ANA=3 firm; RAD=2-3; EXP=1-2 (synthetic-vs-external distinction); HOL=2-3 (n=1 cleanly cross-domain pilot); PRA=2 firm. Favorable 13/15; strict 10/15 (EXP=1 fails the >=2 threshold under conjunction reading per URB #821 §6).",
    },
    {
        "field": "Mathematics with proof-checking",
        "exp": 1, "rad": 3, "ana": 3, "hol": 2, "pra": 2,
        "rad_anchor": "ZFC / category theory / type theory / constructive foundations",
        "pra_anchor": "PRA=2: pure math has weak direct application path; applied math (cryptography, optimization, numerical analysis) downstream provides PRA=3 indirectly but the discipline's own deliverables are mostly PRA=1-2. Lean4/Coq formalizations are PRA=2 working artifacts.",
        "note": "Composite 11/15 favorable. Conjunction fails: EXP=1 below >=2 threshold.",
    },
    {
        "field": "Theoretical physics (string theory / loop quantum gravity)",
        "exp": 2, "rad": 2, "ana": 3, "hol": 3, "pra": 1,
        "rad_anchor": "currently-best-confirmed theory + speculative unifications",
        "pra_anchor": "PRA=1: no direct engineering deliverables. Downstream technology (quantum computing, particle accelerators) eventually but the pillar's own outputs are theoretical.",
        "note": "Composite 11/15 favorable. Conjunction fails: PRA=1 below >=2 threshold.",
    },
    {
        "field": "Theology (mainstream systematic)",
        "exp": 0, "rad": 3, "ana": 2, "hol": 2, "pra": 1,
        "rad_anchor": "scripture / tradition / magisterium",
        "pra_anchor": "PRA=1: pastoral practice and liturgical traditions are 'applications' in a stretched sense, but the discipline's strictly theoretical deliverables are PRA=0-1. Some empirical religious-life-impact studies exist but are mostly external to systematic theology proper.",
        "note": "Composite 8/15. Conjunction fails: EXP=0 + PRA=1 below threshold.",
    },
    {
        "field": "Continental philosophy (Heidegger lineage)",
        "exp": 0, "rad": 3, "ana": 1, "hol": 2, "pra": 0,
        "rad_anchor": "Being / Ereignis / différance / language as house of being",
        "pra_anchor": "PRA=0: pure theoretical apparatus; no working artifacts; no engineering or business deliverables.",
        "note": "Composite 6/15. Conjunction fails on multiple pillars.",
    },
    {
        "field": "Mainstream analytic philosophy (ethics, metaphysics, epistemology core)",
        "exp": 0, "rad": 1, "ana": 3, "hol": 0, "pra": 0,
        "rad_anchor": "received concepts treated as fixed targets for clarification",
        "pra_anchor": "PRA=0: deliberately compartmentalized into theoretical subdisciplines.",
        "note": "Composite 4/15. Conjunction fails on multiple pillars.",
    },
    {
        "field": "Philosophy of language",
        "exp": 2, "rad": 1, "ana": 3, "hol": 1, "pra": 1,
        "rad_anchor": "compositional semantics + truth-conditional meaning",
        "pra_anchor": "PRA=1: some applications in NLP, machine translation, semantic web; the discipline's own outputs are mostly theoretical with downstream applications via linguistics/NLP.",
        "note": "Composite 8/15.",
    },
    {
        "field": "Linguistics (formal semantics + corpus + cognitive)",
        "exp": 3, "rad": 1, "ana": 3, "hol": 1, "pra": 2,
        "rad_anchor": "formal-semantics compositional bivalence + corpus statistics",
        "pra_anchor": "PRA=2: language documentation, dictionaries, grammars (deployed working artifacts); descriptive linguistics has direct applications in language preservation and education.",
        "note": "Composite 10/15. Conjunction fails: RAD=1 + HOL=1 below threshold.",
    },
    {
        "field": "NLP / computational linguistics",
        "exp": 3, "rad": 1, "ana": 3, "hol": 1, "pra": 3,
        "rad_anchor": "engineering benchmarks + transformer architecture",
        "pra_anchor": "PRA=3: transformer architecture deployed at planet-scale (ChatGPT, Claude, Gemini); paying customers; independent replication universal; regulatory engagement (EU AI Act, etc.).",
        "note": "Composite 11/15. Conjunction fails: RAD=1 + HOL=1 below threshold. Highest PRA in catalog.",
    },
    {
        "field": "Experimental physics",
        "exp": 3, "rad": 1, "ana": 3, "hol": 2, "pra": 3,
        "rad_anchor": "currently-best-confirmed theory (Standard Model + GR) treated as provisional",
        "pra_anchor": "PRA=3: MRI from NMR; semiconductor physics deployed everywhere; particle accelerators with regulatory frameworks; superconductors; lasers — direct technology spin-outs.",
        "note": "Composite 12/15. Conjunction fails: RAD=1 below threshold. Highest composite in catalog.",
    },
    {
        "field": "Molecular biology",
        "exp": 3, "rad": 1, "ana": 2, "hol": 1, "pra": 3,
        "rad_anchor": "molecular paradigm (DNA → RNA → protein → phenotype)",
        "pra_anchor": "PRA=3: pharmaceutical industry, FDA-cleared therapies, paying customers, independent replication, gene therapy clinical use.",
        "note": "Composite 10/15. Conjunction fails: RAD=1 + HOL=1 below threshold.",
    },
    {
        "field": "Naturalized epistemology",
        "exp": 2, "rad": 1, "ana": 3, "hol": 2, "pra": 1,
        "rad_anchor": "cognitive science feedback as the foundation for epistemology",
        "pra_anchor": "PRA=1: speculative applications to AI design and education; no working artifacts directly from the discipline.",
        "note": "Composite 9/15.",
    },
    {
        "field": "Experimental philosophy (X-phi)",
        "exp": 3, "rad": 1, "ana": 2, "hol": 1, "pra": 1,
        "rad_anchor": "folk intuitions + empirical surveys as data for philosophical claims",
        "pra_anchor": "PRA=1: surveys are working data-collection artifacts but not engineering or business deliverables; some applications in legal philosophy and policy.",
        "note": "Composite 8/15.",
    },
    {
        "field": "Pittsburgh school (Sellars, Brandom, McDowell)",
        "exp": 1, "rad": 2, "ana": 3, "hol": 2, "pra": 0,
        "rad_anchor": "the space of reasons + inferentialism + non-foundationalist normativity",
        "pra_anchor": "PRA=0: theoretical apparatus; no working artifacts; some downstream influence on AI alignment discussions but the discipline's own outputs are PRA=0.",
        "note": "Composite 8/15. Highest HOL among mainstream analytic philosophy.",
    },
    {
        "field": "Pragmatist tradition (Dewey, Rorty)",
        "exp": 1, "rad": 1, "ana": 2, "hol": 2, "pra": 2,
        "rad_anchor": "practice-as-foundation (Dewey) or anti-foundationalism (Rorty)",
        "pra_anchor": "PRA=2: Dewey's educational philosophy had substantial real-world deployment in 20th-century US education systems (working artifacts at the institutional level); Rorty's influence more theoretical.",
        "note": "Composite 8/15. Conjunction fails: EXP=1 + RAD=1 below threshold.",
    },
    {
        "field": "HPS / STS",
        "exp": 2, "rad": 1, "ana": 2, "hol": 2, "pra": 1,
        "rad_anchor": "anti-foundationalism (often) + symmetry principle",
        "pra_anchor": "PRA=1: some policy applications (science policy, technology assessment); discipline's own outputs are mostly theoretical.",
        "note": "Composite 8/15.",
    },
    {
        "field": "Post-structuralism",
        "exp": 0, "rad": 3, "ana": 1, "hol": 3, "pra": 1,
        "rad_anchor": "différance / decentering / textuality as constitutive",
        "pra_anchor": "PRA=1: substantial influence on cultural critique, queer theory, postcolonial scholarship; the discipline's own outputs are theoretical with downstream cultural-political applications.",
        "note": "Composite 8/15.",
    },
    {
        "field": "Psychoanalysis (mainstream)",
        "exp": 1, "rad": 2, "ana": 1, "hol": 2, "pra": 2,
        "rad_anchor": "unconscious + drive theory + (Freudian/Lacanian/object-relations) framework",
        "pra_anchor": "PRA=2: clinical practice as a working artifact; paying customers in psychotherapy; not PRA=3 because empirical efficacy contested and no FDA-equivalent clearance for psychoanalytic-specific protocols.",
        "note": "Composite 8/15.",
    },
    {
        "field": "Wilber's Integral Theory (cautionary case)",
        "exp": 0, "rad": 3, "ana": 2, "hol": 2, "pra": 1,
        "rad_anchor": "AQAL framework as non-negotiable hard core",
        "pra_anchor": "PRA=1: Integral Institute consulting/coaching; suggested applications without rigorous evidence base; some adoption in transpersonal psychology and integral leadership consulting.",
        "note": "Composite 8/15. Canonical pure-classification failure mode bounded from TI Sigma by EXP+PRA guardrails per URB #821 §5.3. Conjunction fails: EXP=0 + PRA=1 below threshold.",
    },
    {
        "field": "Hegel's system (cautionary case)",
        "exp": 0, "rad": 3, "ana": 2, "hol": 2, "pra": 1,
        "rad_anchor": "absolute spirit / dialectic / unity-of-being-and-thought",
        "pra_anchor": "PRA=1: Hegelian-Marxist political traditions had massive 20th-century real-world deployment; the philosophical apparatus itself is PRA=0-1, with the political downstream giving PRA=1 in a stretched sense.",
        "note": "Composite 8/15. Conjunction fails: EXP=0 + PRA=1.",
    },
    {
        "field": "Whitehead's Process Philosophy (cautionary case)",
        "exp": 0, "rad": 3, "ana": 2, "hol": 2, "pra": 0,
        "rad_anchor": "process metaphysics + actual occasions + prehension as constitutive",
        "pra_anchor": "PRA=0: pure theoretical apparatus; no working artifacts; some influence on process theology and ecological thought but no engineering or business deliverables.",
        "note": "Composite 7/15. Conjunction fails: EXP=0 + PRA=0.",
    },
]


def assess(f, ti_sigma_strict=False):
    if f["field"] == "TI Sigma" and ti_sigma_strict:
        # Strict scoring per URB #819 §6.1 + URB #820 §4.2 + URB #821 §4.3
        exp, rad, ana, hol, pra = 1, 2, 3, 2, 2
    else:
        exp, rad, ana, hol, pra = (
            f["exp"], f["rad"], f["ana"], f["hol"], f["pra"]
        )
    composite = exp + rad + ana + hol + pra
    pillars_at_2_or_above = sum(1 for v in (exp, rad, ana, hol, pra) if v >= 2)
    pillars_at_3 = sum(1 for v in (exp, rad, ana, hol, pra) if v == 3)
    conjunction_satisfied = pillars_at_2_or_above == 5
    return {
        "field": f["field"],
        "exp": exp, "rad": rad, "ana": ana, "hol": hol, "pra": pra,
        "composite_score_out_of_15": composite,
        "pillars_at_2_or_above": pillars_at_2_or_above,
        "pillars_at_3": pillars_at_3,
        "conjunction_all_5_at_or_above_2": conjunction_satisfied,
        "rad_anchor": f["rad_anchor"],
        "pra_anchor": f["pra_anchor"],
        "note": f["note"],
    }


def main():
    favorable = [assess(f, ti_sigma_strict=False) for f in FIELDS]
    favorable_sorted = sorted(
        favorable,
        key=lambda x: (
            -int(x["conjunction_all_5_at_or_above_2"]),
            -x["composite_score_out_of_15"],
            -x["pillars_at_3"],
        ),
    )

    strict = [assess(f, ti_sigma_strict=True) for f in FIELDS]
    strict_sorted = sorted(
        strict,
        key=lambda x: (
            -int(x["conjunction_all_5_at_or_above_2"]),
            -x["composite_score_out_of_15"],
            -x["pillars_at_3"],
        ),
    )

    ti_sigma_fav = next(a for a in favorable if a["field"] == "TI Sigma")
    ti_sigma_strict = next(a for a in strict if a["field"] == "TI Sigma")

    fav_conj_satisfied = [
        a["field"] for a in favorable if a["conjunction_all_5_at_or_above_2"]
    ]
    strict_conj_satisfied = [
        a["field"] for a in strict if a["conjunction_all_5_at_or_above_2"]
    ]

    print("=" * 78)
    print("FIVE PILLARS GRID — EXP/RAD/ANA/HOL/PRA — 21 fields including TI Sigma")
    print("(URB #821 extends URB #820's 4-pillar grid with PRA as 5th pillar)")
    print("=" * 78)
    print()
    print("FAVORABLE-END SCORING:")
    print(
        f"  {'Field':<58} {'EXP':>3} {'RAD':>3} {'ANA':>3} "
        f"{'HOL':>3} {'PRA':>3} {'Sum':>4} {'Conj':>5}"
    )
    print("-" * 78)
    for a in favorable_sorted:
        marker = " *" if a["field"] == "TI Sigma" else ""
        conj = "YES" if a["conjunction_all_5_at_or_above_2"] else "no"
        print(
            f"  {a['field']:<58}{marker:>2} "
            f"{a['exp']:>3} {a['rad']:>3} {a['ana']:>3} "
            f"{a['hol']:>3} {a['pra']:>3} "
            f"{a['composite_score_out_of_15']:>4} {conj:>5}"
        )

    print()
    print("CONJUNCTION (all 5 pillars at >=2) under FAVORABLE scoring:")
    print(f"  Satisfied by {len(fav_conj_satisfied)}/{len(FIELDS)} fields:")
    for f in fav_conj_satisfied:
        print(f"    - {f}")
    if len(fav_conj_satisfied) == 1 and fav_conj_satisfied[0] == "TI Sigma":
        print("  >>> TI Sigma uniquely satisfies the conjunction at favorable scoring")
        print("  >>> per URB #821 §6.")

    print()
    print("=" * 78)
    print("STRICT TI SIGMA SCORING:")
    print("(EXP=1 only-external-data; RAD=2 not Lakatosian-progressive on n=1;")
    print(" ANA=3 unchanged; HOL=2 no cross-domain prediction body; PRA=2 firm)")
    print("=" * 78)
    print()
    print(
        f"  TI Sigma strict scoring: EXP={ti_sigma_strict['exp']} "
        f"RAD={ti_sigma_strict['rad']} ANA={ti_sigma_strict['ana']} "
        f"HOL={ti_sigma_strict['hol']} PRA={ti_sigma_strict['pra']} "
        f"composite={ti_sigma_strict['composite_score_out_of_15']}/15 "
        f"pillars-at->=2: {ti_sigma_strict['pillars_at_2_or_above']}/5 "
        f"conjunction: "
        f"{'YES' if ti_sigma_strict['conjunction_all_5_at_or_above_2'] else 'NO'}"
    )
    print()
    print("  Top 8 fields under strict TI scoring (composite descending):")
    for a in strict_sorted[:8]:
        marker = " <-- TI Sigma" if a["field"] == "TI Sigma" else ""
        conj = "YES" if a["conjunction_all_5_at_or_above_2"] else "no"
        print(
            f"    {a['composite_score_out_of_15']:>2}/15  "
            f"EXP={a['exp']} RAD={a['rad']} ANA={a['ana']} "
            f"HOL={a['hol']} PRA={a['pra']} "
            f"conj={conj}  {a['field']}{marker}"
        )
    print()
    print(
        f"  CONJUNCTION at strict scoring: {len(strict_conj_satisfied)}"
        f"/{len(FIELDS)} fields satisfy:"
    )
    if not strict_conj_satisfied:
        print("    (none — conjunction is partially defeated for TI Sigma at strict")
        print("     scoring because EXP=1 fails the >=2 threshold; honestly reported")
        print("     per URB #821 §6 / §8.9)")
    else:
        for f in strict_conj_satisfied:
            print(f"    - {f}")

    interpretation = (
        f"Across {len(FIELDS)} fields/traditions catalogued under URB #821's "
        f"five-pillar grid (EXPERIMENTAL + RADICALLY-CENTERED + ANALYTIC + "
        f"HOLISTIC + PRAGMATIC, scored 0-3 each per the §2 / URB #819 / URB "
        f"#820 / URB #821 §2 operationalizations), TI Sigma at favorable "
        f"scoring (EXP=2 RAD=3 ANA=3 HOL=3 PRA=2, composite "
        f"{ti_sigma_fav['composite_score_out_of_15']}/15) UNIQUELY satisfies "
        f"the CONJUNCTIVE uniqueness claim per URB #821 §5: it is the only "
        f"field in the catalog with all 5 pillars at >=2 simultaneously. "
        f"Closest comparators at favorable: Experimental physics (12/15, RAD=1 "
        f"fails conjunction), Theoretical physics (11/15, PRA=1 fails), "
        f"Mathematics (11/15, EXP=1 fails), NLP (11/15, RAD=1 + HOL=1 fail). "
        f"Each closest-comparator wins TI Sigma on at least one pillar (NLP "
        f"and Experimental physics dominate PRA; Experimental physics + "
        f"Mathematics + Theoretical physics tie or beat ANA; Experimental "
        f"physics dominates EXP) but none achieves the joint satisfaction. At "
        f"strict TI Sigma scoring (EXP=1 RAD=2 ANA=3 HOL=2 PRA=2, composite "
        f"{ti_sigma_strict['composite_score_out_of_15']}/15) per URB #819 §6.1 "
        f"+ URB #820 §4.2 + URB #821 §4.3 disciplines, TI Sigma drops to 10/15 "
        f"and the conjunction is PARTIALLY DEFEATED (EXP=1 fails the >=2 "
        f"threshold), placing TI Sigma in a 4/5-pillar cluster with mathematics "
        f"and experimental physics rather than uniquely 5/5. The 3 pure-"
        f"philosophy cautionary cases (Wilber 8/15, Hegel 8/15, Whitehead "
        f"7/15) are bounded from TI Sigma by TWO guardrails (EXP at >=1 AND "
        f"PRA at >=2) per URB #821 §5.3 — exactly the structure Brandon's "
        f"'guardrail' framing predicts. PRA's distinctive feature among the 5 "
        f"pillars is that PRA=3 is constitutively externally adjudicated per "
        f"URB #821 §4.2 — the originator alone cannot grant PRA=3, which makes "
        f"PRA the strongest architect-resistant guardrail against author bias. "
        f"TI Sigma at PRA=2 firm has not yet triggered this guardrail; URB "
        f"#821 §7 names onboarding at least one external user of an existing "
        f"engineering artifact as the highest-leverage next move. RATINGS ARE "
        f"AUTHOR JUDGMENTS, the PRA dimension was added in URB #821 "
        f"specifically to articulate Brandon's pushback (URB #821 §8.1 "
        f"founder-defense honoring + §8.2 PRA construct-validity "
        f"AMPLIFIED-confirmation-bias), the §6 grid is a TI-Sigma-friendly "
        f"cut, the conjunctive uniqueness claim is structurally similar to "
        f"AQAL's multi-dimensional uniqueness claim per §8.3 (mitigations: "
        f"responsive-to-external-critique dimensions; PRA's external-"
        f"adjudication structure; honest strict-scoring downgrade reporting "
        f"with conjunction partially defeated reported), and the strict-"
        f"scoring conjunction failure is honestly reported per §8.9. URB #821 "
        f"§7's voluntary procedural discipline targets growing PRA toward 3 "
        f"via external-user onboarding as the standing falsification target."
    )

    print()
    print("=" * 78)
    print("Interpretation")
    print("=" * 78)
    print(interpretation)

    output = {
        "n_fields": len(FIELDS),
        "favorable_scoring": favorable_sorted,
        "strict_ti_sigma_scoring": strict_sorted,
        "favorable_conjunction_satisfied": fav_conj_satisfied,
        "strict_conjunction_satisfied": strict_conj_satisfied,
        "ti_sigma_favorable": {
            "exp": ti_sigma_fav["exp"], "rad": ti_sigma_fav["rad"],
            "ana": ti_sigma_fav["ana"], "hol": ti_sigma_fav["hol"],
            "pra": ti_sigma_fav["pra"],
            "composite": ti_sigma_fav["composite_score_out_of_15"],
            "pillars_at_2_or_above": ti_sigma_fav["pillars_at_2_or_above"],
            "conjunction_satisfied": ti_sigma_fav[
                "conjunction_all_5_at_or_above_2"
            ],
        },
        "ti_sigma_strict": {
            "exp": ti_sigma_strict["exp"], "rad": ti_sigma_strict["rad"],
            "ana": ti_sigma_strict["ana"], "hol": ti_sigma_strict["hol"],
            "pra": ti_sigma_strict["pra"],
            "composite": ti_sigma_strict["composite_score_out_of_15"],
            "pillars_at_2_or_above": ti_sigma_strict["pillars_at_2_or_above"],
            "conjunction_satisfied": ti_sigma_strict[
                "conjunction_all_5_at_or_above_2"
            ],
        },
        "interpretation": interpretation,
        "caveats": [
            "Ratings are author judgments not survey data.",
            "PRA dimension added in URB #821 to articulate Brandon's pushback (amplified confirmation-bias risk per URB #821 §8.1).",
            "PRA scoring has specific construct-validity issue: Brandon decides what counts as a TI Sigma application (§4.3 / §8.2). Mitigations: §4.1 restriction to working deployed artifacts; PRA=2 / PRA=3 boundary externally adjudicated.",
            "The §6 grid is a TI-Sigma-friendly cut; URB #821 §6.2 names 5 alternative pillars (Replicability, External citations, Funded program size, Independent users, Cumulative research-program size) under which TI Sigma would score below virtually every comparator.",
            "Conjunctive distinctiveness claim is structurally similar to AQAL multi-dimensional uniqueness (§8.3); distinguished on three grounds but structural form risk is real.",
            "TI Sigma PRA=3 honestly not yet earned; §7 names ARM'S-LENGTH external-user onboarding (with non-gameable conditions (i)-(v) per §7 architect-flagged tightening) as the highest-leverage next move.",
            "Strict-scoring conjunction is partially defeated for TI Sigma (EXP=1 fails >=2 threshold); 0/21 fields satisfy at strict; honestly reported per §6 / §8.9. Headline 'uniquely satisfies' applies only at favorable scoring.",
            "The 'social agenda + technology framework + cultural shift' framings are reported as SEPARATE subclaims at PRA=1 / PRA=2 / PRA=0 respectively per §6.1 architect-flagged correction (NOT aggregated). The grid PRA=2 score for TI Sigma reflects the technology-framework subclaim only.",
            "TI Sigma's §4.1 artifact list is heterogeneous; PRA=2 score is at the upper end of a PRA=1-2 range pending an architect-flagged reproducibility-table audit (§4.1 / §8.12). PRA=2 is awarded on the verified run-log subset (5 long-running Replit workflows + recent URB companion scripts).",
            "Comparator PRA scores are unstable on specific entries (§8.10): Wilber may be PRA=2 not PRA=1; psychoanalysis may be PRA=3; mathematics may be PRA=3 via cryptography; theoretical physics may be PRA=2. Conjunction-uniqueness result is robust to most plausible adjustments because comparators' failed pillars are mostly RAD/EXP, not PRA.",
            "PRA=2 is a WEAK guardrail (§5.3 / §8.11): code can compile while operationalizing private vocabulary on synthetic data without testing truth/usefulness. PRA=2 constrains syntax/operations; PRA=3 (or EXP-on-external-data) constrains truth/usefulness. Full defeat of Wilber failure mode requires §7 falsification targets, not PRA=2 alone.",
            "§3.1 reformulation per architect-flagged refinement: 'TI Sigma draws on motifs already explicit in many existing fields; no claim is made that those fields implicitly grasp TI Sigma itself' (replaces the previous 'distributed but unintegrated explicit grasp of pieces of TI Sigma' framing which still smuggled in the asymmetric reading).",
        ],
    }

    out_path = Path("five_pillars_ti_grid.json")
    out_path.write_text(json.dumps(output, indent=2))
    print()
    print(f"Report written to {out_path}")


if __name__ == "__main__":
    main()
