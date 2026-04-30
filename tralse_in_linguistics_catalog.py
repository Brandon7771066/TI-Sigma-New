"""
tralse_in_linguistics_catalog.py
==================================

Companion catalog for URB #816. NOT empirical research; a structured
typology of what linguistics and philosophy of language already have for
handling tralse-like phenomena, plus a coverage matrix showing where
each tool fits and where the gaps are.

The point of this catalog is to make §2 of URB #816 machine-readable and
to support the URB's claim that linguistics is NOT silent on these
phenomena — the field has substantial existing tools, and the
TI-Sigma-specific contribution is reframing rather than technical
replacement. Readers tempted to over-claim that "linguistics didn't know
about X" can consult this catalog and check.

Pure Python stdlib. No randomness. Wall time < 1 s.
"""
from __future__ import annotations
import json
from typing import Dict, List


# Each tool / theory is a record:
#   - "name":               canonical name in the literature
#   - "introduced":         decade or year of introduction
#   - "key_figures":        people most associated with it
#   - "phenomenon":         the natural-language phenomenon it addresses
#   - "tralse_type":        which kind of tralseness it captures
#                           (polysemy / vagueness / context / presupposition /
#                            indexicality / implicature / dynamic-update /
#                            distributional / definitional-bistability)
#   - "mechanism":          what the tool actually does formally
#   - "constitutive":       does the tool treat tralseness as
#                           constitutive (True) or corrective (False)?
#                           "Corrective" = the tool patches a bivalent
#                           core; "Constitutive" = the tool treats the
#                           tralse phenomenon as default / foundational.
#   - "limit":              what the tool does NOT capture
TOOLS: List[Dict] = [
    {
        "name": "Theory of Descriptions",
        "introduced": "1905",
        "key_figures": ["Bertrand Russell"],
        "phenomenon": "denotation failure ('the present King of France is bald')",
        "tralse_type": "presupposition",
        "mechanism": "rewrite definite descriptions as existential quantifications; preserves bivalence by making such sentences false rather than gappy",
        "constitutive": False,
        "limit": "preserves bivalence by stipulation; many linguists later preferred Strawson's gap analysis as more faithful to ordinary usage",
    },
    {
        "name": "Sense / Reference distinction",
        "introduced": "1892",
        "key_figures": ["Gottlob Frege"],
        "phenomenon": "two terms with same reference but different cognitive content (Hesperus / Phosphorus); also raised proto-presuppositional concerns (e.g. denotation failure of 'the present King of France') though without formalizing them in the modern Strawson/Heim sense",
        "tralse_type": "polysemy (proto)",
        "mechanism": "two-level meaning: sense (mode of presentation) + reference (object)",
        "constitutive": False,
        "limit": "binary distinction; cited here mainly for sense/reference, not for a fully developed presupposition theory (which traces more directly to Strawson 1950 and Heim 1983); does not handle context-conditioned reference shifts at the granularity LLMs do",
    },
    {
        "name": "Presupposition / truth-value gaps",
        "introduced": "1950",
        "key_figures": ["P. F. Strawson"],
        "phenomenon": "sentences with failed presuppositions ('the King of France is bald' when there is no king)",
        "tralse_type": "presupposition",
        "mechanism": "third truth-value (gap, undefined, or 'neither true nor false')",
        "constitutive": False,
        "limit": "handles presupposition specifically; not a general theory of tralseness",
    },
    {
        "name": "Three-valued logics (Kleene, Bochvar)",
        "introduced": "1938 / 1939",
        "key_figures": ["Stephen Kleene", "Dmitri Bochvar"],
        "phenomenon": "presupposition failure, partial functions, undefined values",
        "tralse_type": "presupposition",
        "mechanism": "third truth-value with strong/weak connective tables",
        "constitutive": False,
        "limit": "specifically for undefinedness; does not address polysemy, vagueness, or definitional bistability",
    },
    {
        "name": "Two Dogmas of Empiricism",
        "introduced": "1951",
        "key_figures": ["W. V. O. Quine"],
        "phenomenon": "the analytic-synthetic distinction breaks down on examination",
        "tralse_type": "definitional-bistability (proto)",
        "mechanism": "argument that meaning and fact cannot be cleanly separated; web-of-belief holism",
        "constitutive": True,
        "limit": "philosophical critique; does not provide a positive formal alternative",
    },
    {
        "name": "Distributional structure",
        "introduced": "1954",
        "key_figures": ["Zellig Harris", "J. R. Firth (1957)"],
        "phenomenon": "lexical meaning as patterns of co-occurrence",
        "tralse_type": "distributional",
        "mechanism": "meaning as distribution over linguistic contexts ('you shall know a word by the company it keeps')",
        "constitutive": True,
        "limit": "originally informal; took five decades to become computationally tractable (word2vec 2013)",
    },
    {
        "name": "The Structure of Scientific Revolutions",
        "introduced": "1962",
        "key_figures": ["Thomas Kuhn"],
        "phenomenon": "scientific terms shift meaning across paradigms (mass, species, gene)",
        "tralse_type": "definitional-bistability (across time)",
        "mechanism": "paradigms as systems of meaning; incommensurability across paradigm shifts",
        "constitutive": True,
        "limit": "largely historical / philosophical; not a formal semantics",
    },
    {
        "name": "Fuzzy sets / fuzzy semantics",
        "introduced": "1965",
        "key_figures": ["Lotfi Zadeh"],
        "phenomenon": "vague predicates with no sharp boundary ('tall', 'red', 'old')",
        "tralse_type": "vagueness",
        "mechanism": "graded membership in [0,1]; truth-degrees rather than truth-values",
        "constitutive": True,
        "limit": "gradient-based; less natural for discrete bistability and for combinatorial tralseness",
    },
    {
        "name": "Prototype theory in linguistics",
        "introduced": "1973-1975",
        "key_figures": ["Eleanor Rosch"],
        "phenomenon": "category membership is graded; prototypical members vs peripheral ('robin' vs 'penguin' as 'bird')",
        "tralse_type": "vagueness / categorization",
        "mechanism": "categories defined by similarity to prototype, not by necessary-and-sufficient conditions",
        "constitutive": True,
        "limit": "psychological focus; less developed as a formal semantic system",
    },
    {
        "name": "Supervaluation for vagueness",
        "introduced": "1975",
        "key_figures": ["Kit Fine"],
        "phenomenon": "Sorites paradox; vague predicates",
        "tralse_type": "vagueness",
        "mechanism": "truth = true on all admissible precisifications; preserves classical tautologies despite vagueness",
        "constitutive": False,
        "limit": "preserves bivalence at the cost of higher-order vagueness; Williamson 1994 critiques the framework's stability",
    },
    {
        "name": "Possible-worlds semantics for modality",
        "introduced": "1968-1973",
        "key_figures": ["Robert Stalnaker", "David Lewis", "Angelika Kratzer"],
        "phenomenon": "counterfactuals, possibility, necessity",
        "tralse_type": "context (modal base)",
        "mechanism": "truth relative to a world; modals quantify over accessible worlds",
        "constitutive": False,
        "limit": "world-relative bivalence; does not directly address polysemy or definitional bistability",
    },
    {
        "name": "Scalar implicature",
        "introduced": "1972",
        "key_figures": ["Laurence Horn", "Stephen Levinson"],
        "phenomenon": "'some' implicates 'not all'; pragmatic strengthening of literal content",
        "tralse_type": "implicature",
        "mechanism": "Gricean-style maxim-driven inference layered on top of bivalent semantic content",
        "constitutive": False,
        "limit": "two-layer architecture (semantics bivalent, pragmatics adds content); preserves bivalent core",
    },
    {
        "name": "Scorekeeping / contextualism",
        "introduced": "1979",
        "key_figures": ["David Lewis", "Keith DeRose", "Jason Stanley"],
        "phenomenon": "truth-conditions depend on conversational context (epistemic standards, comparison classes)",
        "tralse_type": "context",
        "mechanism": "context as an index that shifts truth-conditions; conversational scoreboard updated by participants",
        "constitutive": False,
        "limit": "preserves bivalent truth at each context-index; the index is the parameter, the truth is bivalent given the index",
    },
    {
        "name": "Dynamic semantics / file change semantics / DRT",
        "introduced": "1981-1991",
        "key_figures": ["Hans Kamp", "Irene Heim", "Jeroen Groenendijk", "Martin Stokhof"],
        "phenomenon": "anaphora across sentences; cross-sentential dynamics; donkey sentences",
        "tralse_type": "dynamic-update",
        "mechanism": "meaning as context-update potential; sentences update an information state rather than mapping to truth-values directly",
        "constitutive": True,
        "tag_contested": True,
        "limit": "TAG IS CONTESTABLE: tagged constitutive here because the headline move is meaning-as-update rather than meaning-as-truth, but most dynamic-semantics frameworks still preserve truth/satisfaction conditions relative to contexts and so could equally well be tagged corrective; this URB takes the constitutive reading but reasonable interpreters would tag it differently; also the philosophical ramification (meaning-as-update vs meaning-as-truth) was not foregrounded by the field as a foundational shift",
    },
    {
        "name": "Cognitive linguistics / Women, Fire, and Dangerous Things",
        "introduced": "1987",
        "key_figures": ["George Lakoff", "Ronald Langacker", "Charles Fillmore"],
        "phenomenon": "embodied meaning, frames, image schemas, conceptual metaphor",
        "tralse_type": "all (foundational reframing)",
        "mechanism": "meaning as embodied conceptual structure; explicitly opposed to truth-conditional bivalent semantics",
        "constitutive": True,
        "limit": "treated by formal-semantics mainstream as a competing paradigm rather than as a foundational corrective; institutional integration has been partial",
    },
    {
        "name": "Demonstratives / indexicality",
        "introduced": "1989 (publication; lectures circulated from 1977)",
        "key_figures": ["David Kaplan"],
        "phenomenon": "'I', 'here', 'now', 'this' have context-dependent reference",
        "tralse_type": "indexicality",
        "mechanism": "two-level semantics: character (function from context to content) + content (proposition); preserves bivalent truth at each context",
        "constitutive": False,
        "limit": "preserves bivalent truth-conditions per context; the tralseness is in the context-dependence, not in the truth-value itself",
    },
    {
        "name": "Vagueness (Williamson)",
        "introduced": "1994",
        "key_figures": ["Timothy Williamson"],
        "phenomenon": "Sorites; epistemicism; survey of supervaluation, fuzzy logic, contextualism",
        "tralse_type": "vagueness",
        "mechanism": "epistemicist defense of bivalence: vague predicates have sharp boundaries we don't know",
        "constitutive": False,
        "limit": "explicitly defends bivalence at the cost of an unknowable sharp boundary; the most thorough modern defense of the bivalent-core architecture against vagueness pressure",
    },
    {
        "name": "Verbal Disputes",
        "introduced": "2011",
        "key_figures": ["David Chalmers"],
        "phenomenon": "philosophical disputes that hinge on definitional choice rather than substantive disagreement",
        "tralse_type": "definitional-bistability",
        "mechanism": "method of elimination: strike out the contested term; if substantive disagreement vanishes, the dispute was merely verbal",
        "constitutive": True,
        "limit": "diagnostic / methodological; does not propose a unified semantics for definitional bistability beyond the diagnostic move",
    },
    {
        "name": "Inquisitive semantics",
        "introduced": "2009-present",
        "key_figures": ["Jeroen Groenendijk", "Floris Roelofsen", "Ivano Ciardelli"],
        "phenomenon": "questions and assertions in a unified framework; meaning as proposing alternatives",
        "tralse_type": "alternatives / dynamic",
        "mechanism": "propositions as sets of possibilities; both questions and assertions express semantic content",
        "constitutive": True,
        "limit": "unifies questions and assertions; less developed for polysemy and definitional bistability specifically",
    },
    {
        "name": "Distributional semantics at scale (word2vec, GloVe, BERT, GPT)",
        "introduced": "2013-present",
        "key_figures": ["Tomas Mikolov", "Jeffrey Pennington", "Jacob Devlin", "OpenAI / Anthropic / Google teams"],
        "phenomenon": "context-conditioned meaning representation at industrial scale",
        "tralse_type": "all (distributional, context, polysemy, implicature emerge in the geometry)",
        "mechanism": "high-dimensional vector embeddings + attention; meaning as context-conditioned predictive distribution",
        "constitutive": True,
        "limit": "foundationally non-bivalent; opaque to symbolic analysis; the philosophical implications for semantics have been noticed but not unified into a foundational shift in linguistic theory",
    },
]


def coverage_matrix(tools: List[Dict]) -> Dict:
    """Compute which tralseness types are covered, by how many tools,
    and how many of each type are constitutive vs corrective."""
    types: Dict[str, Dict[str, int]] = {}
    for t in tools:
        ttype = t["tralse_type"]
        if ttype not in types:
            types[ttype] = {"total": 0, "constitutive": 0, "corrective": 0}
        types[ttype]["total"] += 1
        if t["constitutive"]:
            types[ttype]["constitutive"] += 1
        else:
            types[ttype]["corrective"] += 1
    return types


def main():
    print("=" * 76)
    print("URB #816 — Tralseness in Linguistics: structured catalog")
    print("=" * 76)
    print(f"\nTotal tools / theories cataloged: {len(TOOLS)}")
    n_constitutive = sum(1 for t in TOOLS if t["constitutive"])
    n_corrective = len(TOOLS) - n_constitutive
    print(f"  constitutive (treat tralseness as default/foundational): {n_constitutive}")
    print(f"  corrective   (patches to a bivalent core):               {n_corrective}")

    print("\n" + "-" * 76)
    print("By tralseness type:")
    print("-" * 76)
    types = coverage_matrix(TOOLS)
    for ttype, counts in sorted(types.items()):
        print(f"  {ttype:35s}  total={counts['total']}  "
              f"constitutive={counts['constitutive']}  "
              f"corrective={counts['corrective']}")

    print("\n" + "-" * 76)
    print("Chronology (decade introduced → tools):")
    print("-" * 76)
    by_decade: Dict[str, List[str]] = {}
    for t in TOOLS:
        decade = t["introduced"][:3] + "0s" if t["introduced"][0].isdigit() else t["introduced"]
        by_decade.setdefault(decade, []).append(t["name"])
    for decade in sorted(by_decade.keys()):
        print(f"  {decade}: {', '.join(by_decade[decade])}")

    n_contested = sum(1 for t in TOOLS if t.get("tag_contested"))
    interpretation = (
        f"Linguistics and philosophy of language have at least "
        f"{len(TOOLS)} substantial tools / theories addressing tralse-"
        f"like phenomena, spanning {sorted(by_decade.keys())[0]} to "
        f"{sorted(by_decade.keys())[-1]}. Of these, this catalog tags "
        f"{n_constitutive} as constitutive (default / foundational) and "
        f"{n_corrective} as corrective (patches to a bivalent core), "
        f"with {n_contested} explicitly marked as having a contested tag "
        f"(reasonable interpreters would classify them differently). "
        f"The constitutive/corrective tags are INTERPRETIVE LABELS, not "
        f"objective measurements: another reasonable observer could "
        f"shift several items between buckets and the apparent 50/50 "
        f"split is a function of which items are included and how the "
        f"borderline ones are tagged, not a quantitative finding. The "
        f"corrective tools are mostly in the dominant formal-semantics "
        f"mainstream (Russell's theory of descriptions, Kleene/Bochvar "
        f"three-valued logics, supervaluation, possible-worlds modality, "
        f"scalar implicature, contextualism, Kaplanian indexicality, "
        f"Williamson's epistemicism). The constitutive tools are mostly "
        f"outside the formal mainstream (Quine, Harris/Firth "
        f"distributional, Kuhn, fuzzy sets, prototype theory, dynamic "
        f"semantics [contested], cognitive linguistics, Chalmers' "
        f"verbal-disputes diagnostic, inquisitive semantics, modern "
        f"distributional / LLM-based semantics). This is the structural "
        f"observation behind URB #816: the technical machinery exists, "
        f"but the constitutive vs corrective polarity is split across "
        f"the field, and the formal-mainstream commitment to bivalent-"
        f"core-with-patches has been the institutionally dominant frame. "
        f"TI Sigma's specific PROPOSED contribution is foundational "
        f"reframing (invert the polarity, make tralseness the default) "
        f"plus unification of the philosophical ramifications — NOT new "
        f"technical mechanisms, and NOT a settled result; the proposal "
        f"itself is a hypothesis to be argued for."
    )

    print("\n" + "=" * 76)
    print("Interpretation")
    print("=" * 76)
    print(interpretation)

    report = {
        "n_tools": len(TOOLS),
        "n_constitutive": n_constitutive,
        "n_corrective": n_corrective,
        "by_tralse_type": types,
        "by_decade": by_decade,
        "tools": TOOLS,
        "interpretation": interpretation,
    }
    out_path = "tralse_in_linguistics_catalog.json"
    with open(out_path, "w") as f:
        json.dump(report, f, indent=2)
    print(f"\nReport written to {out_path}")


if __name__ == "__main__":
    main()
