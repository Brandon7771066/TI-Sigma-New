"""
definitionally_bistable_sentences.py
======================================

Companion encoding for URB #815 (NOT empirical evidence; not a model of
any specific natural-language understanding system). Demonstrates the
Tralse-5-valued treatment of definitionally bistable sentences — surface
sentences "X is Y" whose classical truth-value flips under a legitimate
re-explication of one of the polysemous terms — and contrasts it with
the bivalent treatment, which is forced to either choose an explication
silently or report inconsistency.

What this script does:
- Encodes 5 example sentences (Brandon's "balance is appropriateness"
  case plus 4 historical / canonical examples from philosophy).
- For each, lists its defensible explications and the classical
  truth-value under each.
- Computes the bivalent verdict (INCONSISTENT_UNDER_BIVALENCE if T and F
  both appear among the explications) and the Tralse-5-valued verdict
  (DT, t, or f as appropriate, plus T or F if the explications agree).
- Demonstrates that Tralse 5-valued logic represents the bistability
  cleanly without forcing an early explication choice.

What this script is NOT:
- A claim that the listed explications are exhaustive for any sentence.
- A claim that the assigned per-explication truth-values are universally
  uncontested (some are; some have their own internal disputes).
- A theorem about natural language. It is a typology + small machine that
  illustrates the structural point of URB #815.

Pure Python stdlib. No NumPy. No randomness. Wall time < 1 s.
"""
from __future__ import annotations
import json
from typing import Dict, List, Tuple


# Tralse 5-valued logic constants:
#   T  = classically true
#   F  = classically false
#   t  = true-DT (mostly true under dominant explication, alternative flips it)
#   f  = false-DT (mostly false under dominant explication, alternative flips it)
#   DT = double-tralse (genuine indeterminate; no fact-of-the-matter
#                       without explication)
TRALSE_VALUES = {"T", "F", "t", "f", "DT"}


# Each sentence is a record:
#   - "sentence":    the surface natural-language sentence
#   - "explications": dict mapping a brief label of the explication of the
#                     contested term to its classical truth-value (T or F)
#                     under that explication
#   - "dominant":    optional label of the explication considered most
#                    common in current usage (drives t vs f vs DT
#                    assignment when classifying the unparameterized
#                    sentence)
#   - "note":        prose note about the sentence
SENTENCES: List[Dict] = [
    {
        "sentence": "Balance is appropriateness.",
        "explications": {
            "balance = equilibrium / equal-weight":           "F",
            "balance = harmony as fit-for-purpose":           "T",
            "balance = moderation (context-free midpoint)":   "F",
        },
        "dominant": None,  # genuinely contested; no dominant usage
        "note": (
            "Brandon's URB #814 case. The two principal explications of "
            "'balance' map to opposite truth-values; without a stipulated "
            "explication the sentence sits at DT."
        ),
    },
    {
        "sentence": "Freedom is constraint.",
        "explications": {
            "freedom = absence of external interference (negative liberty, Berlin)":  "F",
            "freedom = capacity for self-direction (positive liberty / Stoic / Buddhist; requires self-discipline)": "T",
        },
        "dominant": None,
        "note": (
            "Classic positive-vs-negative-liberty case. Berlin's 1958 "
            "lecture 'Two Concepts of Liberty' is the canonical "
            "articulation; the explication choice is itself a major "
            "philosophical-political question."
        ),
    },
    {
        "sentence": "Knowledge is justified true belief.",
        "explications": {
            "pre-Gettier dominant analytic analysis of knowledge (tradition discussed back to Plato's Theaetetus, which itself entertains and rejects several candidates)":  "T",
            "post-Gettier (1963) — counterexamples widely accepted as showing JTB is insufficient as an analysis of knowledge":                                                "F",
            "reliabilist account (Goldman 1967 onward)":                                                                                                                       "F",
        },
        "dominant": "post-Gettier (1963) — counterexamples widely accepted as showing JTB is insufficient as an analysis of knowledge",
        "note": (
            "Historical pivot: the dominant analytic ANALYSIS of "
            "knowledge shifted after Gettier's 1963 three-page paper. "
            "The claim here is about the dominant analysis (T → F), "
            "not about a wholesale change in the natural-language "
            "meaning of 'knowledge,' which is itself broader than any "
            "particular philosophical analysis."
        ),
    },
    {
        "sentence": "Numbers exist.",
        "explications": {
            "Platonism (abstract objects exist independently of minds)":           "T",
            "nominalism (only concrete particulars exist; numbers are fictions)":  "F",
            "fictionalism (numbers exist as useful fictions; ontology agnostic)":  "F",
        },
        "dominant": None,
        "note": (
            "Long-running metaphysics debate that Chalmers (2011) cites "
            "as a paradigm verbal dispute about the explication of "
            "'exists'."
        ),
    },
    {
        "sentence": "A sentence is meaningful only if verifiable.",
        "explications": {
            "early/strict logical positivism (Vienna Circle, ~1920s-1930s) — early formulations; positivists themselves later weakened the principle (verifiability → confirmability → testability) partly in response to self-application objections": "T",
            "mainstream post-positivist philosophy of science (Quine 1951, Kuhn 1962, etc.) — verifiability principle widely rejected": "F",
            "(self-application: this sentence is itself not empirically verifiable, so under strict verifiability it would be meaningless)": "F",
        },
        "dominant": "mainstream post-positivist philosophy of science (Quine 1951, Kuhn 1962, etc.) — verifiability principle widely rejected",
        "note": (
            "Included as a historically important contested thesis with "
            "a classical-logic self-application problem layered on top "
            "of the definitional issue. The early-positivist T-assignment "
            "is itself a simplification: Vienna Circle members weakened "
            "the principle multiple times precisely because of the "
            "self-application objection and other problems. This row is "
            "NOT a clean T-under-A / F-under-B case in the same way the "
            "first four rows are; it illustrates that real philosophical "
            "sentences can have both definitional bistability AND "
            "internal logical issues, and the Tralse representation "
            "accommodates both via the t/f gradient."
        ),
    },
]


def classical_bivalent_verdict(record: Dict) -> str:
    """Bivalent logic assigns T or F to a sentence ONCE its terms have
    been disambiguated. For an unparameterized definitionally bistable
    sentence (one where some explications give T and others give F),
    bivalent logic must either pick an explication silently (and report
    the corresponding T or F) or report that the sentence is ambiguous
    / under-specified at the natural-language level. The label
    'AMBIGUOUS_WITHOUT_EXPLICATION' captures the latter — it is a
    statement about the sentence, not a claim that classical logic has
    become inconsistent."""
    polarities = set(record["explications"].values())
    if "T" in polarities and "F" in polarities:
        return "AMBIGUOUS_WITHOUT_EXPLICATION"
    if polarities == {"T"}:
        return "T"
    if polarities == {"F"}:
        return "F"
    return "UNDETERMINED"


def tralse_5valued_verdict(record: Dict) -> str:
    """Tralse 5-valued logic represents the bistability without forcing
    an early explication choice. Returns one of {T, F, t, f, DT}."""
    polarities = set(record["explications"].values())
    has_T, has_F = "T" in polarities, "F" in polarities

    if has_T and not has_F:
        return "T"
    if has_F and not has_T:
        return "F"
    if not has_T and not has_F:
        return "DT"

    # Genuinely bistable: both T and F appear among the explications.
    dominant = record.get("dominant")
    if dominant is None:
        return "DT"
    dominant_value = record["explications"].get(dominant)
    if dominant_value == "T":
        return "t"
    if dominant_value == "F":
        return "f"
    return "DT"


def main():
    print("=" * 76)
    print("URB #815 — Definitionally Bistable Sentences — demonstration")
    print("=" * 76)

    results = []
    for i, rec in enumerate(SENTENCES, 1):
        bv = classical_bivalent_verdict(rec)
        tv = tralse_5valued_verdict(rec)
        results.append({
            "index": i,
            "sentence": rec["sentence"],
            "explications": rec["explications"],
            "dominant_explication": rec["dominant"],
            "classical_bivalent_verdict": bv,
            "tralse_5valued_verdict": tv,
            "note": rec["note"],
        })

        print(f"\n[{i}] {rec['sentence']}")
        for label, val in rec["explications"].items():
            marker = " (dominant)" if label == rec.get("dominant") else ""
            print(f"      under  ['{label}']{marker}")
            print(f"          → classical truth-value = {val}")
        print(f"      bivalent verdict (no explication chosen): {bv}")
        print(f"      Tralse 5-valued verdict:                  {tv}")
        print(f"      note: {rec['note']}")

    n_bistable = sum(
        1 for r in results
        if r["classical_bivalent_verdict"] == "AMBIGUOUS_WITHOUT_EXPLICATION"
    )
    n_clean = len(results) - n_bistable

    print("\n" + "=" * 76)
    print("Summary")
    print("=" * 76)
    print(f"  total sentences examined:                     {len(results)}")
    print(f"  ambiguous-without-explication "
          f"(definitionally bistable): {n_bistable}")
    print(f"  unambiguous (all explications agree):         {n_clean}")
    print(f"  Tralse-5-valued representation: ALL {len(results)} sentences "
          "receive a single value")
    print(f"    in {{T, F, t, f, DT}}.")

    interpretation = (
        "All 5 sentences exhibit definitional bistability (at least one "
        "T-explication and one F-explication). Within each individual "
        "explication, bivalent classical logic assigns a clean T or F. "
        "At the natural-language level (no explication chosen), bivalent "
        "logic must either pick an explication silently or report the "
        "sentence as ambiguous / under-specified. The Tralse 5-valued "
        "vocabulary adds a single-symbol name for the bistable state — "
        "DT for sentences with no dominant explication, t/f for those "
        "with a dominant explication that an alternative flips. This is "
        "a small but useful expressive gain for philosophical-discourse "
        "work; it does not claim that bivalent logic is broken, only "
        "that giving the bistable state its own name is convenient "
        "enough to be worth coining. The phenomenon itself has been "
        "named in the established stack: polysemy (linguistics, the "
        "mechanism), equivocation (logic, the fallacy form), verbal "
        "dispute (Chalmers 2011, the debate form), and Carnapian "
        "explication (Carnap 1950, the precision-making remedy)."
    )

    report = {
        "tralse_values": sorted(TRALSE_VALUES),
        "n_sentences": len(results),
        "n_bivalent_inconsistent": n_bistable,
        "n_bivalent_clean": n_clean,
        "results": results,
        "interpretation": interpretation,
    }

    print(f"\nInterpretation: {interpretation}")

    out_path = "definitionally_bistable_sentences_report.json"
    with open(out_path, "w") as f:
        json.dump(report, f, indent=2)
    print(f"\nReport written to {out_path}")


if __name__ == "__main__":
    main()
