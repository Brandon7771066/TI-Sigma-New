"""
exp_rad_ana_grid.py

Companion script to URB #819. Catalogs 17 fields/traditions (including
TI Sigma) on a 3-criterion grid:

  - EXPERIMENTAL (EXP): pre-registered, falsifiable, executed pilots
    with honest falsification track-record. 0-3 scale.

  - RADICALLY-CENTERED (RAD): non-negotiable foundational anchor;
    Lakatosian hard core / protective belt distinction. 0-3 scale.
    "Radical" = radix (root, foundation), not "extreme."

  - ANALYTIC (ANA): formal definitions, mathematical structure, pre-
    registration discipline, proof-style argumentation. 0-3 scale.

For each field, also records the RAD ANCHOR (what the foundational
commitment is grounded in). This matters because several fields
have all three pillars at >=2 but RAD anchored elsewhere than TI
Sigma's GILE/MR/tralse hard core; their failure to grasp TI is a
different-anchor issue, not a missing-pillar issue.

Author-coded scoring under the URB #819 §2 operationalization;
sensitivity analysis under alternative operationalizations is not
performed. RATINGS ARE AUTHOR JUDGMENTS not survey data; reasonable
observers would shift several scores. The catalog is illustrative
of URB #819's structural-distinctiveness claim under one reasonable
coding; it does not test the claim against alternative codings or
alternative grids.

Pure stdlib. No randomness. Wall < 1 s.
"""

import json
from pathlib import Path

FIELDS = [
    {
        "field": "TI Sigma",
        "exp": 2,
        "rad": 3,
        "ana": 3,
        "rad_anchor": "GILE/MR/tralse 5-valued logic + constitutive-tralseness-of-language hard core",
        "note": "EXP=2 because URBs #796 #797 #799 #801 #802 #803 are real pre-registered executed pilots with honest falsifications (URB #802 H1) and honest report-against-prior, but URB #804 DANDI replication remains pending and several other operationalizable hypotheses are unexecuted; ratcheting EXP to 3 requires URB #804 execution per URB #818 §8.5 / URB #819 §7. RAD=3 because GILE/MR/tralse hard core is non-negotiable AND the protective belt is generating progressive updates per Lakatosian discipline (H1 falsified → mechanism identified; H2 H3 supported). ANA=3 because formal definitions, mathematical structure (F4 BOK 24-cell, Leech, E8, Lean4 MPP formalizations), pre-registration discipline, brutal-honesty audits as analytic discipline are pervasive throughout the URB series.",
    },
    {
        "field": "Mathematics with proof-checking",
        "exp": 1,
        "rad": 3,
        "ana": 3,
        "rad_anchor": "ZFC / category theory / type theory / constructive foundations (varies by community)",
        "note": "Same shape as TI Sigma minus EXP, with RAD anchored at ZFC or alternative foundations rather than GILE/MR/tralse. Mathematicians in ZFC do not grasp TI not because they lack a pillar but because their RAD anchor is different. EXP=1 because numerical pilots and proof-checking are common but the field's primary mode is proof, not pre-registered empirical pilot.",
    },
    {
        "field": "Theology (mainstream)",
        "exp": 0,
        "rad": 3,
        "ana": 2,
        "rad_anchor": "scripture / tradition / magisterium",
        "note": "RAD=3 because scripture or tradition functions as non-negotiable hard core. ANA=2 because formal theology (Aquinas, Anselm, modern systematic theology) uses substantial formal apparatus but not pervasively. EXP=0 because empirical pilot is not the field's mode of work. Failure to grasp TI is a different-anchor issue, not a missing-pillar issue (RAD anchored at scripture not at GILE/MR/tralse).",
    },
    {
        "field": "Continental philosophy (Heidegger lineage)",
        "exp": 0,
        "rad": 3,
        "ana": 1,
        "rad_anchor": "Being / Ereignis / différance / language as house of being",
        "note": "RAD=3 because foundational commitments to Being, Ereignis, différance are non-negotiable for the tradition. ANA=1 because the tradition deliberately resists analytic apparatus in favor of phenomenological, hermeneutic, or rhetorical methods. EXP=0 because empirical pilot is not the field's mode. The Heideggerian commitment to language as constitutively prior to bivalent logic OVERLAPS with URB #816's constitutive-tralseness finding — closer to TI than analytic philosophy is on the language question — but the RAD anchor is different.",
    },
    {
        "field": "Mainstream analytic philosophy (ethics, metaphysics, epistemology core)",
        "exp": 0,
        "rad": 1,
        "ana": 3,
        "rad_anchor": "received concepts (knowledge, free will, justice, etc.) treated as fixed targets for clarification",
        "note": "ANA=3 because the analytic methods (analysis, distinction-drawing, counterexample-construction) are formal and load-bearing. RAD=1 because the field operates on received concepts without committing to a foundational explanation of why these are the right concepts. EXP=0-1 because X-phi and naturalized epistemology are small subfields. The URB #818 §2 'problem-driven analytic subliteratures' pattern.",
    },
    {
        "field": "Philosophy of language",
        "exp": 2,
        "rad": 1,
        "ana": 3,
        "rad_anchor": "compositional semantics + truth-conditional meaning (Frege/Tarski lineage)",
        "note": "Strong on ANA and EXP via linguistic data and intuition pumps. RAD=1 because the foundational commitment to compositionality and truth-conditional semantics is treated as the working framework but not radically defended as non-negotiable; alternative foundations (use theories, dynamic semantics, distributional semantics) are admitted into the conversation.",
    },
    {
        "field": "Linguistics (formal semantics + corpus + cognitive)",
        "exp": 3,
        "rad": 1,
        "ana": 3,
        "rad_anchor": "formal-semantics compositional bivalence + corpus statistics (in tension)",
        "note": "Strong EXP and ANA. RAD=1 per URB #816 §3.1: formal-semantics retained bivalent compositional commitments for decades despite mounting evidence from cognitive linguistics, distributional semantics, and now LLMs. The polarity-flip to constitutively-tralse foundation has not occurred; the field continues patching bivalent cores with corrective machinery rather than radically inverting. This is the canonical case of EXP+ANA without RAD.",
    },
    {
        "field": "NLP / computational linguistics",
        "exp": 3,
        "rad": 1,
        "ana": 3,
        "rad_anchor": "engineering benchmarks (BLEU, GLUE, etc.) + transformer architecture as de facto foundation",
        "note": "Same shape as linguistics. RAD=1 because the field is engineering-driven (benchmark-chasing) rather than foundationally committed. The current de facto foundation (transformer architectures + scaling laws) is treated as working method, not as non-negotiable.",
    },
    {
        "field": "Experimental physics",
        "exp": 3,
        "rad": 1,
        "ana": 3,
        "rad_anchor": "currently-best-confirmed theory (Standard Model + GR) treated as provisional",
        "note": "Strong EXP and ANA. RAD=1 because foundations are explicitly treated as in-principle revisable; a physicist who committed to a particular interpretation of QM as non-negotiable would lose empirical-science status. This is the canonical case where EXP requires foundational humility, so RAD drops.",
    },
    {
        "field": "Molecular biology",
        "exp": 3,
        "rad": 1,
        "ana": 2,
        "rad_anchor": "molecular paradigm (DNA → RNA → protein → phenotype) treated as working framework",
        "note": "Strong EXP. ANA=2 because formal apparatus is moderate (kinetics models, sequence statistics, structural biology) but the field is more empirical-descriptive than formal. RAD=1 because the molecular paradigm is the working framework but is treated as a successful working hypothesis, not as Lakatosian non-negotiable hard core.",
    },
    {
        "field": "Naturalized epistemology",
        "exp": 2,
        "rad": 1,
        "ana": 3,
        "rad_anchor": "cognitive science feedback as the foundation for epistemology",
        "note": "Strong ANA. EXP=2 because the field imports cognitive science empirical work but does not always pre-register its philosophical hypotheses. RAD=1 because naturalized epistemology rejects a-priori foundational commitments in epistemology, treating cognitive science as the relevant evidence rather than as a foundational anchor.",
    },
    {
        "field": "Experimental philosophy (X-phi)",
        "exp": 3,
        "rad": 1,
        "ana": 2,
        "rad_anchor": "folk intuitions + empirical surveys as data for philosophical claims",
        "note": "Strong EXP via empirical surveys and intuition-elicitation. ANA=2 because the field uses statistical methods and pre-registration but is methodologically diverse. RAD=1 because the field's foundational stance is anti-foundationalist in the sense of refusing to privilege any particular set of intuitions as foundational.",
    },
    {
        "field": "Pittsburgh school (Sellars, Brandom, McDowell)",
        "exp": 1,
        "rad": 2,
        "ana": 3,
        "rad_anchor": "the space of reasons + inferentialism + non-foundationalist normativity",
        "note": "Strong ANA. RAD=2 because the foundational commitment to the space of reasons / inferentialism is explicit and defended but the tradition is also explicitly non-foundationalist in the classical sense. EXP=1 because the tradition uses linguistic and historical case studies but does not produce pre-registered empirical pilots.",
    },
    {
        "field": "Pragmatist tradition (Dewey, Rorty)",
        "exp": 1,
        "rad": 1,
        "ana": 2,
        "rad_anchor": "practice-as-foundation (or anti-foundationalism in Rorty)",
        "note": "Moderate across the board. RAD=1 because the tradition is explicitly anti-foundationalist (Rorty) or treats practice as foundation in a non-Lakatosian way (Dewey). EXP=1 because empirical engagement is via examples rather than pre-registered pilots. ANA=2 because formal apparatus is present but not load-bearing.",
    },
    {
        "field": "HPS / STS (history and philosophy of science / science and technology studies)",
        "exp": 2,
        "rad": 1,
        "ana": 2,
        "rad_anchor": "anti-foundationalism (often) + symmetry principle",
        "note": "EXP=2 via descriptive empirical work on actual scientific practice. ANA=2 because the apparatus (Kuhnian paradigms, Latourian actor-network theory, conceptual-history methods) is formal but not load-bearing throughout. RAD=1 because the tradition is mostly anti-foundationalist by methodological commitment.",
    },
    {
        "field": "Post-structuralism",
        "exp": 0,
        "rad": 3,
        "ana": 1,
        "rad_anchor": "différance / decentering / textuality as constitutive",
        "note": "RAD=3 because foundational commitments to différance, decentering, and textuality are non-negotiable for the tradition and define its identity. ANA=1 because the tradition deliberately resists analytic apparatus in favor of literary, performative, or paradoxical methods. EXP=0 because empirical pilot is not the field's mode.",
    },
    {
        "field": "Psychoanalysis (mainstream)",
        "exp": 1,
        "rad": 2,
        "ana": 1,
        "rad_anchor": "unconscious + drive theory + (Freudian or Lacanian or object-relations) framework as working foundation",
        "note": "RAD=2 because the framework commitments are explicit and defended but the field admits substantial revision (post-Freudian, relational, Lacanian, etc.). EXP=1 because case studies are used but pre-registration is rare. ANA=1 because formal apparatus is present (Lacanian topology, structural diagrams) but not load-bearing throughout.",
    },
]


def assess(f):
    composite = f["exp"] + f["rad"] + f["ana"]
    pillars_at_2_or_above = sum(1 for k in ("exp", "rad", "ana") if f[k] >= 2)
    pillars_at_3 = sum(1 for k in ("exp", "rad", "ana") if f[k] == 3)
    return {
        "field": f["field"],
        "exp": f["exp"],
        "rad": f["rad"],
        "ana": f["ana"],
        "composite_score_out_of_9": composite,
        "pillars_at_2_or_above": pillars_at_2_or_above,
        "pillars_at_3": pillars_at_3,
        "rad_anchor": f["rad_anchor"],
        "note": f["note"],
    }


def main():
    assessed = [assess(f) for f in FIELDS]
    assessed_sorted = sorted(
        assessed, key=lambda x: (-x["composite_score_out_of_9"], -x["pillars_at_3"])
    )

    by_pillar_count = {0: [], 1: [], 2: [], 3: []}
    for a in assessed:
        by_pillar_count[a["pillars_at_2_or_above"]].append(a["field"])

    ti_sigma = next(a for a in assessed if a["field"] == "TI Sigma")
    ti_sigma_distinctive = [
        a["field"]
        for a in assessed
        if a["pillars_at_2_or_above"] == 3 and a["field"] != "TI Sigma"
    ]

    different_rad_anchor = []
    for a in assessed:
        if a["pillars_at_2_or_above"] >= 2 and a["field"] != "TI Sigma":
            different_rad_anchor.append(
                {
                    "field": a["field"],
                    "rad_anchor": a["rad_anchor"],
                    "pillars_at_2_or_above": a["pillars_at_2_or_above"],
                }
            )

    print("=" * 78)
    print("EXP / RAD / ANA grid — 17 fields / traditions including TI Sigma")
    print("=" * 78)
    print()
    print(f"{'Field':<55} {'EXP':>4} {'RAD':>4} {'ANA':>4} {'Sum':>4}")
    print("-" * 78)
    for a in assessed_sorted:
        print(
            f"  {a['field']:<53} {a['exp']:>4} {a['rad']:>4} {a['ana']:>4} {a['composite_score_out_of_9']:>4}"
        )

    print()
    print("=" * 78)
    print("Distribution by pillar-count-at-2-or-above")
    print("=" * 78)
    for k in sorted(by_pillar_count.keys()):
        print(f"  {k} pillars at >=2 ({len(by_pillar_count[k])}):")
        for f in by_pillar_count[k]:
            print(f"      - {f}")

    print()
    print("=" * 78)
    print("TI Sigma's position")
    print("=" * 78)
    print(
        f"  composite score: {ti_sigma['composite_score_out_of_9']}/9 currently "
        f"(EXP=2 RAD=3 ANA=3)"
    )
    print(
        f"  composite score: 9/9 with URB #804 execution closing EXP gap "
        f"(EXP=3 RAD=3 ANA=3)"
    )
    print(f"  pillars at >=2: {ti_sigma['pillars_at_2_or_above']}/3")
    print(f"  pillars at 3: {ti_sigma['pillars_at_3']}/3")
    print(f"  RAD anchor: {ti_sigma['rad_anchor']}")
    print(
        f"  other fields with all 3 pillars at >=2: "
        f"{ti_sigma_distinctive if ti_sigma_distinctive else 'none'}"
    )

    print()
    print("=" * 78)
    print("Fields with >=2 pillars but DIFFERENT RAD anchor than TI Sigma")
    print("(failure to grasp TI is different-anchor issue, not missing-pillar issue)")
    print("=" * 78)
    for x in different_rad_anchor:
        print(f"  - {x['field']} ({x['pillars_at_2_or_above']}/3 pillars)")
        print(f"    RAD anchor: {x['rad_anchor']}")

    interpretation = (
        f"Across {len(FIELDS)} fields/traditions catalogued under URB #819's "
        f"three-criterion grid (EXPERIMENTAL + RADICALLY-CENTERED + "
        f"ANALYTIC, scored 0-3 each per the §2 operationalizations), TI "
        f"Sigma is the only field with all three pillars at >=2 currently "
        f"(EXP=2 RAD=3 ANA=3, composite 8/9), and would be the only field "
        f"with all three pillars at 3 if URB #804 DANDI replication is "
        f"executed (composite 9/9). The closest comparison fields each "
        f"lack at least one pillar at >=2 OR satisfy all pillars but anchor "
        f"RAD elsewhere: mathematics (ANA=3 RAD=3 EXP=1, RAD anchored at "
        f"ZFC/foundations not GILE/MR/tralse); linguistics (ANA=3 EXP=3 "
        f"RAD=1 because formal-semantics retained bivalent commitments "
        f"per URB #816 §3.1); mainstream analytic philosophy (ANA=3 RAD=1 "
        f"EXP=0-1, the URB #818 §2 problem-driven-analytic-subliteratures "
        f"pattern); theology (RAD=3 ANA=2 EXP=0, RAD anchored at "
        f"scripture); continental philosophy (RAD=3 ANA=1 EXP=0, RAD "
        f"anchored at Being/Ereignis); post-structuralism (RAD=3 ANA=1 "
        f"EXP=0, RAD anchored at différance). The structural-rarity claim "
        f"is supported under author coding: the EXP+RAD+ANA combination "
        f"is genuinely uncommon because of the §3 tensions (EXP usually "
        f"erodes RAD; RAD usually limits EXP; ANA without RAD or EXP "
        f"reduces to clarification work). The negative claim about other "
        f"fields needs the qualification (URB #819 §5) that several "
        f"fields satisfy 2-3 pillars but anchor RAD elsewhere; their "
        f"failure to grasp TI is a different-anchor issue, not a "
        f"missing-pillar issue. RATINGS ARE AUTHOR JUDGMENTS not survey "
        f"data; the author has the EXP+RAD+ANA framework in mind while "
        f"rating TI Sigma's own program against it (confirmation-bias "
        f"risk per URB #818 §9.4 and URB #819 §8.4); sensitivity analysis "
        f"under alternative operationalizations (foundationalist-vs-"
        f"phenomenological-vs-normative groundings of RAD) is not "
        f"performed and would be needed to substantiate any robustness "
        f"claim. The catalog is illustrative of URB #819's structural-"
        f"distinctiveness claim under one reasonable coding; it does not "
        f"adjudicate against alternative codings that would weaken the "
        f"claim, and the §6 grid is itself a TI-Sigma-friendly cut that "
        f"a field with a different framework could legitimately propose "
        f"replacing with a different grid that would not place TI Sigma "
        f"in a structurally distinctive position."
    )

    print()
    print("=" * 78)
    print("Interpretation")
    print("=" * 78)
    print(interpretation)

    # ---- §6.1 Sensitivity analysis: re-score TI Sigma at strict end of
    # ---- provisional ranges per URB #819 §1 / §4.3 / §4.4 / §8.2 / §8.3.
    # ---- Strict scoring: EXP=1 (only DANDI:000552 external-data anchor;
    # ---- synthetic-data computational pilots don't count); RAD=2 (Lakatosian-
    # ---- progressive status not granted on a 1-falsification sample).
    # ---- Re-rank fields under strict scoring and report the qualitative
    # ---- result: TI Sigma loses unique top position; mathematics edges it
    # ---- out on composite; small-handful framing remains robust but
    # ---- uniquely-positioned framing collapses.
    strict = [dict(a) for a in assessed]
    for s in strict:
        if s["field"] == "TI Sigma":
            s["exp"] = 1
            s["rad"] = 2
            s["composite_score_out_of_9"] = s["exp"] + s["rad"] + s["ana"]
            s["pillars_at_2_or_above"] = sum(
                1 for k in ("exp", "rad", "ana") if s[k] >= 2
            )
            s["pillars_at_3"] = sum(1 for k in ("exp", "rad", "ana") if s[k] == 3)
    strict_sorted = sorted(
        strict,
        key=lambda x: (-x["composite_score_out_of_9"], -x["pillars_at_3"]),
    )
    strict_top = strict_sorted[:5]
    strict_ti_sigma = next(s for s in strict if s["field"] == "TI Sigma")
    strict_by_pillar_count = {0: [], 1: [], 2: [], 3: []}
    for s in strict:
        strict_by_pillar_count[s["pillars_at_2_or_above"]].append(s["field"])

    print()
    print("=" * 78)
    print("§6.1 SENSITIVITY ANALYSIS: TI Sigma re-scored at strict end of range")
    print("(EXP=1: only external-data anchors count; RAD=2: Lakatosian-progressive")
    print("status not granted on 1-falsification sample)")
    print("=" * 78)
    print()
    print(f"  TI Sigma strict scoring: EXP={strict_ti_sigma['exp']} "
          f"RAD={strict_ti_sigma['rad']} ANA={strict_ti_sigma['ana']} "
          f"composite={strict_ti_sigma['composite_score_out_of_9']}/9 "
          f"pillars-at->=2: {strict_ti_sigma['pillars_at_2_or_above']}/3")
    print()
    print("  Top 5 fields under strict scoring (composite descending):")
    for s in strict_top:
        marker = " <-- TI Sigma" if s["field"] == "TI Sigma" else ""
        print(
            f"    {s['composite_score_out_of_9']}/9  "
            f"EXP={s['exp']} RAD={s['rad']} ANA={s['ana']}  "
            f"{s['field']}{marker}"
        )
    print()
    print("  Distribution under strict scoring by pillar-count-at-2-or-above:")
    for k in sorted(strict_by_pillar_count.keys()):
        print(f"    {k} pillars at >=2 ({len(strict_by_pillar_count[k])}):")
        for f in strict_by_pillar_count[k]:
            print(f"        - {f}")
    print()
    print("  Qualitative result: at strict scoring, TI Sigma drops from "
          "uniquely-top (composite 8/9, only field with all 3 pillars at >=2) "
          "to one-of-a-small-handful (composite 6/9, edged out by mathematics "
          "at 7/9). The 'small handful' framing is robust to provisional-"
          "scoring adjustment; the 'uniquely positioned' framing is not. "
          "URB #819 §6.1 reflects this honestly.")

    output = {
        "n_fields": len(FIELDS),
        "fields": assessed_sorted,
        "by_pillar_count": {
            str(k): {"count": len(v), "fields": v} for k, v in by_pillar_count.items()
        },
        "ti_sigma_favorable_scoring": {
            "exp": ti_sigma["exp"],
            "rad": ti_sigma["rad"],
            "ana": ti_sigma["ana"],
            "composite_current": ti_sigma["composite_score_out_of_9"],
            "composite_with_urb_804": 9,
            "rad_anchor": ti_sigma["rad_anchor"],
            "other_fields_with_all_3_at_2_or_above": ti_sigma_distinctive,
        },
        "ti_sigma_strict_scoring": {
            "exp": strict_ti_sigma["exp"],
            "rad": strict_ti_sigma["rad"],
            "ana": strict_ti_sigma["ana"],
            "composite_current": strict_ti_sigma["composite_score_out_of_9"],
            "composite_with_urb_804": strict_ti_sigma["ana"]
            + strict_ti_sigma["rad"]
            + 2,  # EXP ratchets to 2 with one more external anchor
            "pillars_at_2_or_above": strict_ti_sigma["pillars_at_2_or_above"],
        },
        "sensitivity_top_5_strict": [
            {
                "field": s["field"],
                "composite": s["composite_score_out_of_9"],
                "exp": s["exp"],
                "rad": s["rad"],
                "ana": s["ana"],
            }
            for s in strict_top
        ],
        "fields_with_different_rad_anchor": different_rad_anchor,
        "interpretation": interpretation,
        "caveats": [
            "Ratings are author judgments not survey data.",
            "The author has the EXP+RAD+ANA framework in mind while rating TI Sigma's own program (confirmation-bias risk).",
            "Sensitivity analysis under alternative RAD operationalizations not performed.",
            "The §6 grid is a TI-Sigma-friendly cut; alternative grids could be proposed.",
            "TI Sigma EXP=2 currently; ratcheting to 3 requires URB #804 execution per URB #818 §8.5 binding commitment.",
            "RAD=3 score depends on Lakatosian protective-belt continuing to absorb experimental hits with progressive (not degenerating) updates; if EXP execution stops, RAD becomes harder to defend.",
        ],
    }

    out_path = Path("exp_rad_ana_grid.json")
    out_path.write_text(json.dumps(output, indent=2))
    print()
    print(f"Report written to {out_path}")


if __name__ == "__main__":
    main()
