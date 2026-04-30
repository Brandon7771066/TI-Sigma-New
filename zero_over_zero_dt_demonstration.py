"""
zero_over_zero_dt_demonstration.py
==================================

Companion demonstration for URB #811: 0/0 is not "indeterminate," it is
nonsense, which under TI Sigma's five-valued truth system maps to DT
(Double Tralse).

What this script shows:
1. Raw 0/0 in IEEE 754 (numpy) returns NaN — the floating-point substrate's
   recognition that the operation produces "not a number." This is the
   computational cousin of DT.
2. Raw 0/0 in symbolic algebra (sympy) returns nan — same recognition at
   the symbolic level.
3. Limits of "0/0-form" expressions (e.g., lim sin(x)/x as x->0) are NOT
   raw 0/0; they are well-defined limit operations whose VALUES are
   determinate (T) once evaluated. The seven classical "indeterminate forms"
   collapse to T or F when treated as limit problems with the L'Hopital
   apparatus, and are DT only when treated as raw arithmetic without any
   limit-taking context.
4. The ONE-WAY SUBSTITUTION ERROR: substituting x=0 into sin(x)/x to "get
   0/0" and then treating that 0/0 as the value of the original expression
   conflates a syntactic pattern (the form) with a semantic value (the
   limit). The form is a marker that says "use a different evaluation
   procedure," not an answer.

Output: zero_over_zero_dt_report.json + console table.
"""
from __future__ import annotations
import json
import math
import warnings
import numpy as np
import sympy as sp

warnings.filterwarnings("ignore", category=RuntimeWarning)


def ieee_zero_over_zero():
    """Show what IEEE 754 actually does with 0/0."""
    a = np.float64(0.0)
    b = np.float64(0.0)
    with np.errstate(divide="ignore", invalid="ignore"):
        result = a / b
    return {
        "input": "np.float64(0.0) / np.float64(0.0)",
        "result_repr": repr(result),
        "is_nan": bool(np.isnan(result)),
        "is_finite": bool(np.isfinite(result)),
        "ieee_classification": "NaN (Not-a-Number)",
        "ti_sigma_classification": "DT (Double Tralse) — the substrate refuses "
                                   "to assign a numerical value because the "
                                   "operation is malformed",
    }


def sympy_zero_over_zero():
    """Show what symbolic algebra does with raw 0/0."""
    raw = sp.Integer(0) / sp.Integer(0)
    return {
        "input": "sp.Integer(0) / sp.Integer(0)",
        "result_repr": str(raw),
        "is_nan": raw is sp.nan,
        "ti_sigma_classification": "DT — sympy returns sp.nan, the symbolic "
                                   "marker that the expression has no "
                                   "well-defined value",
    }


def limit_demonstrations():
    """Show that 0/0-FORM limits ARE well-defined (T), not DT.

    The point: treating limits as raw 0/0 is the category error. The limit
    is a different operation with a well-defined value; the '0/0 form' is
    just a syntactic flag saying 'use L'Hopital or series expansion.'
    """
    x = sp.Symbol("x")
    # Each case: (label, expression, point, dir, ti_label, expected,
    #            canonical_form_demonstrated)
    # dir is one of "+-" (two-sided), "+", "-".
    cases = [
        # 0/0 form
        ("lim x->0 of sin(x)/x", sp.sin(x) / x, 0, "+-", "T", 1, "0/0"),
        ("lim x->0 of (1-cos(x))/x^2", (1 - sp.cos(x)) / x**2, 0,
         "+-", "T", sp.Rational(1, 2), "0/0"),
        ("lim x->0+ of x/x^2", x / x**2, 0, "+",
         "T (right-limit; left-limit is -oo, so two-sided is DT)",
         sp.oo, "0/0"),
        ("lim x->0 of x^2/x", x**2 / x, 0, "+-", "T", 0, "0/0"),
        ("lim x->0 of (sin(x) - x)/x^3", (sp.sin(x) - x) / x**3, 0,
         "+-", "T", sp.Rational(-1, 6), "0/0"),
        # oo/oo form
        ("lim x->oo of e^x / x^2", sp.exp(x) / x**2, sp.oo, "+-",
         "T (= +oo, well-defined)", sp.oo, "oo/oo"),
        ("lim x->oo of ln(x) / x", sp.ln(x) / x, sp.oo, "+-", "T", 0, "oo/oo"),
        # 0 * oo form
        ("lim x->0+ of x*ln(x)", x * sp.ln(x), 0, "+", "T", 0, "0 * oo"),
        # oo - oo form
        ("lim x->0+ of (1/x - 1/sin(x))",
         (1 / x) - (1 / sp.sin(x)), 0, "+", "T", 0, "oo - oo"),
        # 0^0 form
        ("lim x->0+ of x^x", x**x, 0, "+", "T", 1, "0^0"),
        # oo^0 form
        ("lim x->oo of x^(1/x)", x**(1/x), sp.oo, "+-", "T", 1, "oo^0"),
        # 1^oo form
        ("lim x->0+ of (1+x)^(1/x)", (1 + x)**(1/x), 0, "+", "T", sp.E, "1^oo"),
    ]
    out = []
    for label, expr, point, direction, ti_label, expected, form in cases:
        try:
            if direction == "+-":
                val = sp.limit(expr, x, point)
            else:
                val = sp.limit(expr, x, point, direction)
            if val == sp.oo or val == -sp.oo:
                matches = (expected == val)
            else:
                try:
                    matches = bool(sp.simplify(val - expected) == 0)
                except Exception:
                    matches = (str(val) == str(expected))
            out.append({
                "limit_label": label,
                "expression": str(expr),
                "form_demonstrated": form,
                "direction": direction,
                "computed_value": str(val),
                "expected_value": str(expected),
                "matches_expected": matches,
                "ti_sigma_classification": ti_label,
                "comment": ("The LIMIT has a determinate value (T). The "
                            f"'{form}' form encountered by direct substitution "
                            "is a syntactic flag — DT only if you stop there."),
            })
        except Exception as e:
            out.append({
                "limit_label": label,
                "expression": str(expr),
                "form_demonstrated": form,
                "error": str(e),
            })
    return out


def indeterminate_forms_classification():
    """Map the seven classical 'indeterminate forms' to TI Sigma 5VL + DT."""
    forms = [
        {
            "form": "0/0",
            "as_raw_arithmetic": "DT (nonsense — equation 0 = 0*c has all c "
                                 "as solutions; no unique answer exists)",
            "as_limit_form": "T or F per case (resolvable by L'Hopital, "
                            "series expansion, or factoring)",
            "category_error_warning": "Conventional 'indeterminate form' "
                                       "label conflates these two cases.",
        },
        {
            "form": "infinity/infinity",
            "as_raw_arithmetic": "DT (infinity is not a number; ratio not "
                                 "defined in standard reals)",
            "as_limit_form": "T or F per case (L'Hopital applies)",
            "category_error_warning": "Same conflation as 0/0.",
        },
        {
            "form": "0 * infinity",
            "as_raw_arithmetic": "DT",
            "as_limit_form": "T or F per case (rewrite as 0/0 or "
                            "infinity/infinity then L'Hopital)",
            "category_error_warning": None,
        },
        {
            "form": "infinity - infinity",
            "as_raw_arithmetic": "DT",
            "as_limit_form": "T or F per case (algebraic manipulation)",
            "category_error_warning": None,
        },
        {
            "form": "0^0",
            "as_raw_arithmetic": "DT in general; conventionally DEFINED as 1 "
                                 "in combinatorics and discrete math (a "
                                 "convention, not a derivation)",
            "as_limit_form": "T or F per case (use exp/log transformation)",
            "category_error_warning": "The conventional convention 0^0 := 1 "
                                       "is a DEFINITION chosen for utility, "
                                       "not a derivation from the field axioms.",
        },
        {
            "form": "infinity^0",
            "as_raw_arithmetic": "DT",
            "as_limit_form": "T or F per case",
            "category_error_warning": None,
        },
        {
            "form": "1^infinity",
            "as_raw_arithmetic": "DT (literal 1^infinity is malformed: "
                                 "infinity is not a field element and so is "
                                 "not a valid exponent in standard fields). "
                                 "NOTE: 1^n with n a finite natural / integer "
                                 "/ rational is T = 1 by the standard "
                                 "exponentiation axioms — but that is not "
                                 "the '1^infinity form'.",
            "as_limit_form": "T or F per case (e.g., (1+1/n)^n -> e)",
            "category_error_warning": "An earlier draft labeled raw 1^infinity "
                                       "as Pre-True; corrected here. The form "
                                       "arises only in limit contexts where "
                                       "the base APPROACHES 1 without being "
                                       "exactly 1, so 1^anything = 1 cannot "
                                       "be invoked.",
        },
    ]
    return forms


def division_axiom_check():
    """Spell out why 0/0 is DT from the field axioms."""
    return {
        "field_axiom": "For a field F, division a/b is defined as the unique "
                       "element c such that a = b*c, provided b != 0.",
        "case_b_eq_0_a_eq_0": (
            "If b = 0 and a = 0, the equation 0 = 0*c is satisfied by EVERY "
            "c in F. There is no UNIQUE c. Therefore 0/0 is not a value in F; "
            "it fails the existence-and-uniqueness predicate that defines "
            "division."
        ),
        "case_b_eq_0_a_neq_0": (
            "If b = 0 and a != 0, the equation a = 0*c = 0 is NEVER satisfied "
            "(since a != 0). Therefore a/0 (a != 0) is not a value in F; it "
            "fails the existence predicate."
        ),
        "ti_sigma_mapping": {
            "0/0 (a=0, b=0)": "DT — the question 'what is 0/0?' has no unique "
                              "answer because the defining equation has too "
                              "many solutions (every element of F).",
            "a/0 with a != 0": "DT — the question has no answer because the "
                               "defining equation has no solutions.",
            "a/b with b != 0": "T — the question has a unique answer.",
        },
        "why_double_tralse_not_just_tralse": (
            "Tralse (T-tilde) marks 'ambiguous in a structurally meaningful "
            "way' — there is content to evaluate but the evaluation is "
            "underdetermined. DT (Double Tralse) marks 'the question itself "
            "is malformed' — the evaluation procedure does not apply at all. "
            "0/0 is the second case: it is not that we lack information about "
            "0/0, it is that 0/0 is not the kind of expression that has a value."
        ),
    }


def conventional_textbook_position():
    """Document the conventional position this URB pushes back on."""
    return {
        "textbook_label": "indeterminate form",
        "textbook_canonical_list": [
            "0/0", "infinity/infinity", "0 * infinity",
            "infinity - infinity", "0^0", "infinity^0", "1^infinity",
        ],
        "textbook_meaning": (
            "A syntactic pattern that arises when evaluating a limit by "
            "direct substitution; signals that L'Hopital's rule, series "
            "expansion, or algebraic manipulation is required."
        ),
        "where_it_goes_wrong": (
            "The label 'indeterminate FORM' is correctly restricted to limit "
            "contexts. But the same label is colloquially extended to RAW "
            "ARITHMETIC '0/0' as if it meant 'the value 0/0 is undetermined' "
            "or 'could be anything.' That extension is the category error: "
            "raw 0/0 is not a value with multiple candidate determinations; "
            "it is not a value at all. 'Indeterminate' suggests epistemic "
            "underdetermination; the correct label is malformed-by-construction, "
            "i.e., DT."
        ),
        "ti_sigma_correction": (
            "Distinguish: (a) 'indeterminate FORM' as a syntactic flag in "
            "limit contexts (legitimate, narrow usage), (b) 'indeterminate "
            "VALUE' applied to raw 0/0 (incorrect — it is DT, not T-tilde and "
            "not Pre-True). Reserving 'indeterminate' for case (a) only and "
            "labeling case (b) as DT eliminates the conflation."
        ),
    }


def main():
    report = {
        "title": "0/0 is DT (Double Tralse), not 'indeterminate' — "
                 "demonstration script for URB #811",
        "ieee_demonstration": ieee_zero_over_zero(),
        "sympy_raw_demonstration": sympy_zero_over_zero(),
        "limit_demonstrations": limit_demonstrations(),
        "indeterminate_forms_classification": indeterminate_forms_classification(),
        "division_axiom_analysis": division_axiom_check(),
        "conventional_position_critique": conventional_textbook_position(),
    }

    # Console summary
    print("=" * 70)
    print("URB #811 — 0/0 is DT companion demonstration")
    print("=" * 70)

    print("\n[1] IEEE 754 raw 0.0 / 0.0:")
    ieee = report["ieee_demonstration"]
    print(f"    Result: {ieee['result_repr']}  (is_nan={ieee['is_nan']})")
    print(f"    TI Sigma: {ieee['ti_sigma_classification']}")

    print("\n[2] Sympy raw Integer(0) / Integer(0):")
    sym = report["sympy_raw_demonstration"]
    print(f"    Result: {sym['result_repr']}  (is sp.nan = {sym['is_nan']})")
    print(f"    TI Sigma: {sym['ti_sigma_classification']}")

    print("\n[3] All seven canonical 'indeterminate-form' LIMITS "
          "(well-defined, T — different operation from raw arithmetic):")
    forms_covered = set()
    for entry in report["limit_demonstrations"]:
        if "error" in entry:
            print(f"    [ERR] {entry['limit_label']}: {entry['error']}")
        else:
            forms_covered.add(entry["form_demonstrated"])
            print(f"    [{entry['form_demonstrated']:>7}]  {entry['limit_label']}")
            print(f"               = {entry['computed_value']}  "
                  f"(expected {entry['expected_value']}, "
                  f"matches={entry['matches_expected']})")
    print(f"    Canonical forms covered: "
          f"{sorted(forms_covered)} (n={len(forms_covered)} of 7)")

    print("\n[4] Classification of conventional 'indeterminate forms':")
    for f in report["indeterminate_forms_classification"]:
        print(f"    {f['form']:>20}  raw: {f['as_raw_arithmetic'][:60]}...")
        print(f"    {'':>20}  lim: {f['as_limit_form'][:60]}")

    print("\n[5] Field-axiom analysis:")
    da = report["division_axiom_analysis"]
    print(f"    Axiom: {da['field_axiom']}")
    print(f"    a=0, b=0:  {da['case_b_eq_0_a_eq_0']}")
    print(f"    a!=0,b=0:  {da['case_b_eq_0_a_neq_0']}")

    print("\n[6] Why DT not Tralse:")
    print(f"    {da['why_double_tralse_not_just_tralse']}")

    out_path = "zero_over_zero_dt_report.json"
    with open(out_path, "w") as f:
        json.dump(report, f, indent=2, default=str)
    print(f"\nReport written to {out_path}")


if __name__ == "__main__":
    main()
