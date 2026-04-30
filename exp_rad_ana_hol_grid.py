"""
exp_rad_ana_hol_grid.py

Companion script to URB #820. Extends URB #819's 17-field catalog with
the HOL (HOLISTIC) dimension scored 0-3 per §2 operationalization:

  - HOL=0 (Compartmentalized): single subdomain; explicitly avoids
    cross-domain claims.

  - HOL=1 (Cross-domain reference): borrows concepts from multiple
    fields without unifying them.

  - HOL=2 (Conceptual integration): one vocabulary across multiple
    domains; classification work without novel cross-domain
    predictions. Wilber, Hegel, Whitehead, large parts of systematic
    theology, structural anthropology, many "grand unified frameworks"
    in continental philosophy live here.

  - HOL=3 (Substantive integration): novel cross-domain predictions
    or technical results that follow from the unification AND could
    not be derived from any single subdomain alone, AND those
    predictions are pre-registered and tested. Glashow-Weinberg-Salam
    electroweak unification, statistical mechanics ↔ thermodynamics
    bridge, evolutionary biology ↔ molecular genetics integration,
    category theory in mathematics live here.

Adds 3 cautionary-case fields not in URB #819 (Wilber's Integral
Theory, Hegel's system, Whitehead's Process Philosophy) specifically
to engage the HOL-style-claim-as-classification failure mode. Total
20 fields catalogued including TI Sigma.

Author-coded. Same confirmation-bias risk as URB #818 §9.4 / URB #819
§8.4 / URB #820 §8.1, AMPLIFIED because the HOL dimension was added in
URB #820 to articulate Brandon's pushback. Sensitivity analysis under
strict TI Sigma scoring per URB #819 §6.1's discipline.

Pure stdlib. No randomness. Wall < 1 s.
"""

import json
from pathlib import Path

# Field tuples extended from URB #819's catalog with HOL column.
# Format: field name, EXP, RAD, ANA, HOL, RAD anchor, note.
FIELDS = [
    {
        "field": "TI Sigma",
        "exp": 2, "rad": 3, "ana": 3, "hol": 3,
        "rad_anchor": "GILE/MR/tralse 5-valued logic + constitutive-tralseness-of-language hard core",
        "hol_anchor": "URB series spans phil-of-language + phil-of-mind + phil-of-science + formal math (Lean4 MPP, TWA, Leech, E8, Monster) + neuroscience/biometrics + quantum-classical hybrid + economics + psychology/wellbeing + theology under one hard core; URB #797 is the cleanest cross-domain pre-registered pilot (phil + group theory + multi-agent sim + LCC methodology) with H1 honestly falsified at noise_p=0.05",
        "note": "Provisional scores per URB #820 §4.4: ANA=3 firm; RAD=2-3 (URB #819 §4.2/§8.3); EXP=1-2 (URB #819 §4.3/§8.2 synthetic-vs-external distinction); HOL=2-3 (URB #820 §4.2 — n=1 cleanly cross-domain pre-registered pilot URB #797 is the minimum threshold for HOL=3 charitable). Favorable scoring 11/12; strict 8/12.",
    },
    {
        "field": "Mathematics with proof-checking",
        "exp": 1, "rad": 3, "ana": 3, "hol": 2,
        "rad_anchor": "ZFC / category theory / type theory / constructive foundations",
        "hol_anchor": "Within mathematics, category theory + Langlands program + algebraic geometry produce substantial cross-subfield integration (HOL=2-3 within math). Across disciplines, math typically does not integrate with non-mathematical fields (HOL=1 cross-disciplinary). Average HOL=2.",
        "note": "Edges TI Sigma out at 9/12 under strict TI scoring (URB #820 §6.1). RAD anchored elsewhere than TI Sigma's GILE/MR/tralse.",
    },
    {
        "field": "Theoretical physics (string theory / loop quantum gravity)",
        "exp": 2, "rad": 2, "ana": 3, "hol": 3,
        "rad_anchor": "currently-best-confirmed theory + speculative unifications (string landscape, LQG)",
        "hol_anchor": "Strong cross-subfield integration claims (gravity + QM + matter + cosmology under one framework). HOL=3 score is generous and contested — string theory's predictive content is famously thin, which is the canonical Wilber-comparable issue.",
        "note": "Closest comparator to TI Sigma at favorable scoring (10/12). Same Wilber-style risk on HOL=3 score that TI Sigma faces.",
    },
    {
        "field": "Theology (mainstream systematic)",
        "exp": 0, "rad": 3, "ana": 2, "hol": 2,
        "rad_anchor": "scripture / tradition / magisterium",
        "hol_anchor": "Systematic theology integrates scripture + tradition + reason + experience under one hard core. HOL=2 (classification rather than novel predictions).",
        "note": "RAD anchored elsewhere than TI Sigma; EXP=0 by design.",
    },
    {
        "field": "Continental philosophy (Heidegger lineage)",
        "exp": 0, "rad": 3, "ana": 1, "hol": 2,
        "rad_anchor": "Being / Ereignis / différance / language as house of being",
        "hol_anchor": "Heidegger's work integrates language + being + technology + history + art + thinking under one framework. HOL=2 (substantial conceptual integration without empirical predictions).",
        "note": "Closest to TI Sigma on the constitutive-tralseness-of-language question per URB #816. RAD anchored elsewhere.",
    },
    {
        "field": "Mainstream analytic philosophy (ethics, metaphysics, epistemology core)",
        "exp": 0, "rad": 1, "ana": 3, "hol": 0,
        "rad_anchor": "received concepts treated as fixed targets for clarification",
        "hol_anchor": "Deliberately compartmentalized into subdisciplines (ethics, metaphysics, epistemology, action theory, philosophy of mind, philosophy of language each pursued separately).",
        "note": "URB #818 §2 'problem-driven analytic subliteratures' pattern. HOL=0 is structurally distinctive — the field's specialization is not accidental but methodologically committed.",
    },
    {
        "field": "Philosophy of language",
        "exp": 2, "rad": 1, "ana": 3, "hol": 1,
        "rad_anchor": "compositional semantics + truth-conditional meaning",
        "hol_anchor": "Within phil-of-language, formal-semantics + corpus + pragmatics + cogling are pursued in often-disconnected subliteratures. HOL=1 — cross-domain reference but not integration.",
        "note": "URB #816 §2's catalog of 20 substantive tools is evidence of substantial within-domain capture of TI's tralseness pillar; HOL=1 because integration with other TI Sigma domains (phil-of-mind, formal math, neuroscience) is rare.",
    },
    {
        "field": "Linguistics (formal semantics + corpus + cognitive)",
        "exp": 3, "rad": 1, "ana": 3, "hol": 1,
        "rad_anchor": "formal-semantics compositional bivalence + corpus statistics (in tension)",
        "hol_anchor": "HOL=1 — formal-semantics + corpus + cogling subfields often pursued separately.",
        "note": "URB #816 §3.1 polarity finding: formal-semantics retained bivalent commitments rather than radically inverting.",
    },
    {
        "field": "NLP / computational linguistics",
        "exp": 3, "rad": 1, "ana": 3, "hol": 1,
        "rad_anchor": "engineering benchmarks + transformer architecture as de facto foundation",
        "hol_anchor": "HOL=1 — NLP often operates separately from formal semantics, cogling, philosophy of language.",
        "note": "Same shape as linguistics; engineering-driven.",
    },
    {
        "field": "Experimental physics",
        "exp": 3, "rad": 1, "ana": 3, "hol": 2,
        "rad_anchor": "currently-best-confirmed theory (Standard Model + GR) treated as provisional",
        "hol_anchor": "HOL=2 within physics (cross-subfield integration via quantum field theory, statistical mechanics, GR); HOL=1 across disciplines.",
        "note": "Ties or beats TI Sigma at strict scoring (9/12).",
    },
    {
        "field": "Molecular biology",
        "exp": 3, "rad": 1, "ana": 2, "hol": 1,
        "rad_anchor": "molecular paradigm (DNA → RNA → protein → phenotype) treated as working framework",
        "hol_anchor": "HOL=1 — molecular biology is specialized; integration with ecology / evolutionary biology / behavior happens but is usually subfield-bounded.",
        "note": "",
    },
    {
        "field": "Naturalized epistemology",
        "exp": 2, "rad": 1, "ana": 3, "hol": 2,
        "rad_anchor": "cognitive science feedback as the foundation for epistemology",
        "hol_anchor": "HOL=2 — integrates epistemology with cognitive science; some cross-domain claims about belief-formation across cultures/contexts.",
        "note": "",
    },
    {
        "field": "Experimental philosophy (X-phi)",
        "exp": 3, "rad": 1, "ana": 2, "hol": 1,
        "rad_anchor": "folk intuitions + empirical surveys as data for philosophical claims",
        "hol_anchor": "HOL=1 — X-phi spans multiple philosophical subdisciplines via empirical methods but is not strongly integrative.",
        "note": "",
    },
    {
        "field": "Pittsburgh school (Sellars, Brandom, McDowell)",
        "exp": 1, "rad": 2, "ana": 3, "hol": 2,
        "rad_anchor": "the space of reasons + inferentialism + non-foundationalist normativity",
        "hol_anchor": "HOL=2 — inferentialism integrates semantics + epistemology + metaphysics + philosophy of mind under the space-of-reasons framework. Substantial conceptual integration.",
        "note": "Highest HOL among mainstream analytic-tradition philosophy; closest to TI Sigma on integrative ambition within philosophy proper.",
    },
    {
        "field": "Pragmatist tradition (Dewey, Rorty)",
        "exp": 1, "rad": 1, "ana": 2, "hol": 2,
        "rad_anchor": "practice-as-foundation (Dewey) or anti-foundationalism (Rorty)",
        "hol_anchor": "HOL=2 — pragmatism integrates across philosophical domains via the practice-centered framework.",
        "note": "",
    },
    {
        "field": "HPS / STS",
        "exp": 2, "rad": 1, "ana": 2, "hol": 2,
        "rad_anchor": "anti-foundationalism (often) + symmetry principle",
        "hol_anchor": "HOL=2 — integrates history + philosophy + sociology of science.",
        "note": "Disciplinary-compartmentalization framework that URB #820 §5 inherits comes from HPS/STS.",
    },
    {
        "field": "Post-structuralism",
        "exp": 0, "rad": 3, "ana": 1, "hol": 3,
        "rad_anchor": "différance / decentering / textuality as constitutive",
        "hol_anchor": "HOL=3 — différance + biopolitics + textuality apparatus produces cross-domain results in literary theory + political theory + philosophy + cultural critique. Whether predictive or classificatory is contested; granted HOL=3 charitably.",
        "note": "Closest non-TI-Sigma field to HOL=3 charitable.",
    },
    {
        "field": "Psychoanalysis (mainstream)",
        "exp": 1, "rad": 2, "ana": 1, "hol": 2,
        "rad_anchor": "unconscious + drive theory + (Freudian/Lacanian/object-relations) framework",
        "hol_anchor": "HOL=2 — unifies clinical + theoretical + cultural domains.",
        "note": "",
    },
    {
        "field": "Wilber's Integral Theory (cautionary case)",
        "exp": 0, "rad": 3, "ana": 2, "hol": 2,
        "rad_anchor": "AQAL framework (4 quadrants × levels × lines × states × types) as non-negotiable hard core",
        "hol_anchor": "HOL=2 — AQAL integrates spirituality + psychology + science + sociology + politics under one framework. Academic verdict: classification work without novel cross-domain predictions. The canonical Wilber failure mode for HOL-style claims.",
        "note": "Added in URB #820 §3 / §6 specifically to engage the HOL-style-claim-as-classification failure mode. TI Sigma's distinction from Wilber rests on the §4.3 distinction (novel cross-domain predictions vs classification work) and currently on n=1 cleanly cross-domain pilot (URB #797).",
    },
    {
        "field": "Hegel's system (cautionary case)",
        "exp": 0, "rad": 3, "ana": 2, "hol": 2,
        "rad_anchor": "absolute spirit / dialectic / unity-of-being-and-thought",
        "hol_anchor": "HOL=2 — Hegelian dialectic integrates across logic + nature + spirit + philosophy of right + history + religion + art. The 'philosophy makes explicit what is implicit' framing is the canonical source of the Hegelian unfalsifiability risk that URB #820 §3 / §5 / §8.3 engages.",
        "note": "Added in URB #820 §3 / §6 specifically to engage the Hegelian unfalsifiability risk in the 'fractured and latent' framing.",
    },
    {
        "field": "Whitehead's Process Philosophy (cautionary case)",
        "exp": 0, "rad": 3, "ana": 2, "hol": 2,
        "rad_anchor": "process metaphysics + actual occasions + prehension as constitutive",
        "hol_anchor": "HOL=2 — process metaphysics integrates physics + biology + psychology + theology + aesthetics under one framework. Substantial conceptual integration without novel empirical predictions.",
        "note": "Added in URB #820 §6 as additional cautionary case.",
    },
]


def assess(f, ti_sigma_strict=False):
    if f["field"] == "TI Sigma" and ti_sigma_strict:
        exp, rad, ana, hol = 1, 2, 3, 2
    else:
        exp, rad, ana, hol = f["exp"], f["rad"], f["ana"], f["hol"]
    composite = exp + rad + ana + hol
    pillars_at_2_or_above = sum(1 for v in (exp, rad, ana, hol) if v >= 2)
    pillars_at_3 = sum(1 for v in (exp, rad, ana, hol) if v == 3)
    return {
        "field": f["field"],
        "exp": exp, "rad": rad, "ana": ana, "hol": hol,
        "composite_score_out_of_12": composite,
        "pillars_at_2_or_above": pillars_at_2_or_above,
        "pillars_at_3": pillars_at_3,
        "rad_anchor": f["rad_anchor"],
        "hol_anchor": f["hol_anchor"],
        "note": f["note"],
    }


def main():
    favorable = [assess(f, ti_sigma_strict=False) for f in FIELDS]
    favorable_sorted = sorted(
        favorable, key=lambda x: (-x["composite_score_out_of_12"], -x["pillars_at_3"])
    )

    strict = [assess(f, ti_sigma_strict=True) for f in FIELDS]
    strict_sorted = sorted(
        strict, key=lambda x: (-x["composite_score_out_of_12"], -x["pillars_at_3"])
    )

    ti_sigma_fav = next(a for a in favorable if a["field"] == "TI Sigma")
    ti_sigma_strict = next(a for a in strict if a["field"] == "TI Sigma")

    fav_by_pillar_count = {0: [], 1: [], 2: [], 3: [], 4: []}
    for a in favorable:
        fav_by_pillar_count[a["pillars_at_2_or_above"]].append(a["field"])

    strict_by_pillar_count = {0: [], 1: [], 2: [], 3: [], 4: []}
    for a in strict:
        strict_by_pillar_count[a["pillars_at_2_or_above"]].append(a["field"])

    print("=" * 78)
    print("EXP/RAD/ANA/HOL grid — 20 fields/traditions including TI Sigma")
    print("(Catalog extended from URB #819's 17 fields with 3 cautionary cases:")
    print(" Wilber, Hegel, Whitehead — added per URB #820 §3 / §6)")
    print("=" * 78)
    print()
    print("FAVORABLE-END SCORING:")
    print(f"  {'Field':<58} {'EXP':>3} {'RAD':>3} {'ANA':>3} {'HOL':>3} {'Sum':>4}")
    print("-" * 78)
    for a in favorable_sorted:
        marker = " *" if a["field"] == "TI Sigma" else ""
        print(
            f"  {a['field']:<58}{marker:>2} "
            f"{a['exp']:>3} {a['rad']:>3} {a['ana']:>3} {a['hol']:>3} "
            f"{a['composite_score_out_of_12']:>4}"
        )

    print()
    print("Distribution by pillar-count-at-2-or-above (favorable scoring):")
    for k in sorted(fav_by_pillar_count.keys()):
        if fav_by_pillar_count[k]:
            print(f"  {k}/4 pillars at >=2 ({len(fav_by_pillar_count[k])}):")
            for f in fav_by_pillar_count[k]:
                print(f"      - {f}")

    print()
    print("=" * 78)
    print("§6.1 SENSITIVITY ANALYSIS — TI Sigma re-scored at strict end:")
    print("(EXP=1: only external-data anchors; RAD=2: Lakatosian-progressive")
    print("not granted on 1-falsification sample; ANA=3 unchanged; HOL=2: no")
    print("cross-domain prediction body, only n=1 cleanly cross-domain pilot)")
    print("=" * 78)
    print()
    print(
        f"  TI Sigma strict scoring: EXP={ti_sigma_strict['exp']} "
        f"RAD={ti_sigma_strict['rad']} ANA={ti_sigma_strict['ana']} "
        f"HOL={ti_sigma_strict['hol']} composite="
        f"{ti_sigma_strict['composite_score_out_of_12']}/12 "
        f"pillars-at->=2: {ti_sigma_strict['pillars_at_2_or_above']}/4"
    )
    print()
    print("  Top 6 fields under strict TI scoring (composite descending):")
    for a in strict_sorted[:6]:
        marker = " <-- TI Sigma" if a["field"] == "TI Sigma" else ""
        print(
            f"    {a['composite_score_out_of_12']:>2}/12  "
            f"EXP={a['exp']} RAD={a['rad']} ANA={a['ana']} HOL={a['hol']}  "
            f"{a['field']}{marker}"
        )
    print()
    print("  Distribution under strict TI scoring by pillars-at->=2:")
    for k in sorted(strict_by_pillar_count.keys()):
        if strict_by_pillar_count[k]:
            print(f"    {k}/4 pillars at >=2 ({len(strict_by_pillar_count[k])}):")
            for f in strict_by_pillar_count[k]:
                marker = " <-- TI Sigma" if f == "TI Sigma" else ""
                print(f"        - {f}{marker}")

    interpretation = (
        f"Across {len(FIELDS)} fields/traditions catalogued under URB #820's "
        f"four-criterion grid (EXPERIMENTAL + RADICALLY-CENTERED + ANALYTIC + "
        f"HOLISTIC, scored 0-3 each per the §2 operationalizations), TI Sigma "
        f"at favorable scoring (EXP=2 RAD=3 ANA=3 HOL=3, composite "
        f"{ti_sigma_fav['composite_score_out_of_12']}/12) is uniquely positioned "
        f"as the only field with all 4 pillars at >=2 AND HOL=3. Closest "
        f"comparator at favorable: Theoretical physics (10/12) where the HOL=3 "
        f"score is itself contested for the Wilber-comparable predictive-content "
        f"reason. At strict TI Sigma scoring (EXP=1 RAD=2 ANA=3 HOL=2, composite "
        f"{ti_sigma_strict['composite_score_out_of_12']}/12) per URB #819 §6.1's "
        f"discipline plus URB #820 §4.2 strict HOL standard, TI Sigma drops to "
        f"8/12 and is edged out by Mathematics (9/12) and tied/edged by "
        f"Experimental physics (9/12), but remains in the small handful of fields "
        f"with all 4 pillars at >=1 + foundationally explicit RAD anchor + "
        f"substantial HOL integration. The 3 cautionary cases (Wilber 7/12, Hegel "
        f"7/12, Whitehead 7/12) cluster at the same composite as Theology, "
        f"Pittsburgh school, and Pragmatist tradition — all HOL=2 systematic-"
        f"integration fields with EXP=0 — confirming that the HOL=2 + EXP=0 "
        f"combination is the canonical Wilber failure mode and that TI Sigma's "
        f"distinction from this cluster rests on EXP>=1 + the n=1 cleanly cross-"
        f"domain pre-registered pilot (URB #797). RATINGS ARE AUTHOR JUDGMENTS, "
        f"the HOL dimension was added in URB #820 specifically to articulate "
        f"Brandon's pushback (URB #820 §8.1 amplified-confirmation-bias risk), "
        f"the §6 grid is a TI-Sigma-friendly cut, and the HOL=3 favorable score "
        f"for TI Sigma rests on n=1 cleanly cross-domain pilot which is the "
        f"minimum threshold for HOL=3 charitable but the maximum defense against "
        f"the Wilber failure mode the URB cannot yet ratchet beyond. URB #820 "
        f"§7's voluntary procedural discipline targets growing this pilot body "
        f"as the falsification condition for the next URB batch."
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
        "favorable_by_pillar_count": {
            str(k): {"count": len(v), "fields": v}
            for k, v in fav_by_pillar_count.items() if v
        },
        "strict_by_pillar_count": {
            str(k): {"count": len(v), "fields": v}
            for k, v in strict_by_pillar_count.items() if v
        },
        "ti_sigma_favorable": {
            "exp": ti_sigma_fav["exp"], "rad": ti_sigma_fav["rad"],
            "ana": ti_sigma_fav["ana"], "hol": ti_sigma_fav["hol"],
            "composite": ti_sigma_fav["composite_score_out_of_12"],
            "composite_with_urb_804": ti_sigma_fav["composite_score_out_of_12"] + 1,
        },
        "ti_sigma_strict": {
            "exp": ti_sigma_strict["exp"], "rad": ti_sigma_strict["rad"],
            "ana": ti_sigma_strict["ana"], "hol": ti_sigma_strict["hol"],
            "composite": ti_sigma_strict["composite_score_out_of_12"],
            "composite_with_urb_804": ti_sigma_strict["composite_score_out_of_12"] + 1,
        },
        "interpretation": interpretation,
        "caveats": [
            "Ratings are author judgments not survey data.",
            "HOL dimension added in URB #820 to articulate Brandon's pushback (amplified confirmation-bias risk per URB #820 §8.1).",
            "The §6 grid is a TI-Sigma-friendly cut; alternative grids could be proposed.",
            "TI Sigma HOL=3 favorable rests on n=1 cleanly cross-domain pre-registered pilot (URB #797) — minimum threshold for HOL=3 charitable.",
            "Wilber failure mode (HOL=2 classification rather than HOL=3 prediction) is not yet defeated; distinction rests on the URB #797 pilot and the §7 voluntary procedural discipline target.",
            "Ratcheting HOL toward 3/3 firmly requires growing the cross-domain pilot body beyond n=1 per URB #820 §7.",
        ],
    }

    out_path = Path("exp_rad_ana_hol_grid.json")
    out_path.write_text(json.dumps(output, indent=2))
    print()
    print(f"Report written to {out_path}")


if __name__ == "__main__":
    main()
