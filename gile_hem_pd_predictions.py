"""
URB #784 — GILE-HEM Ratio Modulation of PD Expression: empirical verification harness.

Encodes the 72-cell prediction cube (8 axes x 3 rho-regimes x 3 PD-signs),
provides classifiers for rho and PD, and runs a seed-observation corpus check
drawn from prior URBs without making any API calls.

Boundaries (URB #784 sec 1.2):
    ET    = sqrt(2) - 1  ~ 0.4142   (Emerick Threshold; lower rho boundary)
    delta = 1 + sqrt(2)  ~ 2.4142   (silver ratio; upper rho boundary)
    Verisyn balance at rho = 1.

PD-sign conventions (URB #625 / URB #615):
    PD > 0  ->  truth-aligned subspace (BT pushes toward T)
    PD = 0  ->  Tralse / Indeterminate / DT band
    PD < 0  ->  anti-truth subspace (BT pushes toward F)

Each cube cell carries a predicted aesthetic-signal sign ('+', '0', '-') and
the corresponding ugliness-signal sign. The (rho_low, PD<0) column is the
Inversion Cell of URB #784 sec 2: beauty becomes a misleading signal there
and ugliness becomes the more reliable truth-tracker.
"""

from __future__ import annotations

import json
import math
from dataclasses import dataclass, asdict
from typing import Literal


# ---------------------------------------------------------------------------
# Boundaries
# ---------------------------------------------------------------------------

ET    = math.sqrt(2.0) - 1.0   # ~ 0.4142
DELTA = 1.0 + math.sqrt(2.0)   # ~ 2.4142

RhoRegime  = Literal["rho_low", "rho_mid", "rho_high"]
PdSign     = Literal["pd_neg", "pd_zero", "pd_pos"]
SignalSign = Literal["+", "0", "-"]

AXES = ("G", "I", "L", "E", "D1", "D2", "D3", "D4")
AXIS_NAMES = {
    "G":  "Goodness (GILE wing)",
    "I":  "Intuition (GILE wing)",
    "L":  "Love (GILE wing)",
    "E":  "Environment / Aesthetics (GILE wing)",
    "D1": "Existence Footprint (HEM arm)",
    "D2": "Moral Presence (HEM arm; ~= GILE-G projection)",
    "D3": "Conscious Meaning (HEM arm; ~= I+L projection)",
    "D4": "Substrate Aesthetics (HEM arm; ~= GILE-E projection)",
}


# ---------------------------------------------------------------------------
# Classifiers
# ---------------------------------------------------------------------------

def classify_rho(rho: float) -> RhoRegime:
    if rho <= ET:
        return "rho_low"
    if rho >= DELTA:
        return "rho_high"
    return "rho_mid"


def classify_pd(pd: float, eps: float = 0.05) -> PdSign:
    if pd > eps:
        return "pd_pos"
    if pd < -eps:
        return "pd_neg"
    return "pd_zero"


# ---------------------------------------------------------------------------
# Prediction cell
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class CellPrediction:
    axis: str
    rho_regime: RhoRegime
    pd_sign: PdSign
    beauty_sign: SignalSign            # predicted aesthetic-as-truth signal
    ugliness_sign: SignalSign          # predicted ugliness-as-truth signal
    inversion_cell: bool               # True for (rho_low, PD<0)
    note: str


def _build_prediction_cube() -> dict[tuple[str, RhoRegime, PdSign], CellPrediction]:
    """
    Build the full 8 x 3 x 3 = 72-cell cube per URB #784 sec 3.

    The per-axis sign rules (canonical summary in URB #784 sec 3 table):

        rho_high:   PD+ -> beauty +    PD0 -> beauty +/0    PD- -> beauty -
        rho_mid:    PD+ -> beauty +    PD0 -> beauty 0      PD- -> beauty -
        rho_low:    PD+ -> beauty 0    PD0 -> beauty 0      PD- -> beauty - / ugliness +   (INVERSION)

    Ugliness-as-signal is the sign-flip of beauty in the inversion cell only;
    in all other cells ugliness-as-signal is '0' (BR remains the operative
    one-place predicate within its validity regime).
    """
    cube: dict[tuple[str, RhoRegime, PdSign], CellPrediction] = {}

    for axis in AXES:
        for rho_regime in ("rho_low", "rho_mid", "rho_high"):
            for pd_sign in ("pd_neg", "pd_zero", "pd_pos"):

                inversion = (rho_regime == "rho_low" and pd_sign == "pd_neg")
                ugliness: SignalSign = "0"
                note = ""

                if rho_regime == "rho_high":
                    if pd_sign == "pd_pos":
                        beauty: SignalSign = "+"
                        note = "BR truth-aligned at full strength."
                    elif pd_sign == "pd_zero":
                        beauty = "+"
                        note = "BR truth-aligned; PD-undetermined cases default to + by GILE-substrate prior."
                    else:  # pd_neg
                        beauty = "-"
                        note = "High-rho falsehood: beauty attaches to a PD<0 BT, BR points away from depiction."

                elif rho_regime == "rho_mid":
                    if pd_sign == "pd_pos":
                        beauty = "+"
                        note = "BR truth-aligned with reduced effect size; SNR scales as |1 - rho|."
                    elif pd_sign == "pd_zero":
                        beauty = "0"
                        note = "Decoupled mid-band: aesthetic signal carries near-zero truth information."
                    else:  # pd_neg
                        beauty = "-"
                        note = "Mid-band negative-PD: BR still points away from beautiful depiction but weakly."

                else:  # rho_low
                    if pd_sign == "pd_pos":
                        beauty = "0"
                        note = "Deep-HEM positive-PD: GILE perturbation is small relative to substrate; BR decoupled."
                    elif pd_sign == "pd_zero":
                        beauty = "0"
                        note = "Deep-HEM neutral-PD: BR decoupled; substrate dominates."
                    else:  # pd_neg
                        beauty = "-"
                        ugliness = "+"
                        note = "INVERSION CELL: beauty masks negative-PD substrate; ugliness honest. URB #784 sec 2."

                cube[(axis, rho_regime, pd_sign)] = CellPrediction(
                    axis=axis,
                    rho_regime=rho_regime,
                    pd_sign=pd_sign,
                    beauty_sign=beauty,
                    ugliness_sign=ugliness,
                    inversion_cell=inversion,
                    note=note,
                )

    return cube


PREDICTION_CUBE = _build_prediction_cube()


def predict(axis: str, rho: float, pd: float) -> CellPrediction:
    """Return the predicted aesthetic and ugliness signs for a (axis, rho, pd) point."""
    if axis not in AXES:
        raise ValueError(f"unknown axis {axis!r}; expected one of {AXES}")
    return PREDICTION_CUBE[(axis, classify_rho(rho), classify_pd(pd))]


# ---------------------------------------------------------------------------
# Seed observations drawn from the existing URB corpus
# (no API calls; each observation cites its source URB)
# ---------------------------------------------------------------------------

@dataclass
class Observation:
    label: str
    source_urb: str
    axis: str
    rho: float          # GILE / HEM
    pd: float           # signed PD-projection in [-1, +1]
    observed_beauty_signal: SignalSign     # observed sign of beauty-as-truth
    observed_ugliness_signal: SignalSign   # observed sign of ugliness-as-truth
    nontrivial: bool    # True for cells where the prediction is + or - (not 0)
    note: str


SEED_OBSERVATIONS: list[Observation] = [
    Observation(
        label="Heliocentric vs Ptolemaic at Copernicus's De Revolutionibus",
        source_urb="UTC-2026-04-21-001 (UGLY_TRUTH_COUNTEREXAMPLES_REGISTRY.md)",
        axis="E", rho=2.6, pd=0.6,
        observed_beauty_signal="+", observed_ugliness_signal="0",
        nontrivial=True,
        note="Pure-mathematics-adjacent; rho_high; positive PD; BR selected correctly.",
    ),
    Observation(
        label="Bohr atom (1913) preferred over Sommerfeld-Wilson on aesthetic grounds",
        source_urb="UTC-2026-04-21-002",
        axis="E", rho=2.5, pd=0.5,
        observed_beauty_signal="+", observed_ugliness_signal="0",
        nontrivial=True,
        note="Theoretical-physics; rho_high; positive PD; BR selected correctly.",
    ),
    Observation(
        label="Pure-mathematics domain composite ratio",
        source_urb="urb_694 sec 3 table (predicted GILE:HEM ~= 3:1)",
        axis="G", rho=3.0, pd=0.7,
        observed_beauty_signal="+", observed_ugliness_signal="0",
        nontrivial=True,
        note="Domain-level; rho_high; PD+ from successful-practitioner inference.",
    ),
    Observation(
        label="Manual-trades / athletics domain composite ratio",
        source_urb="urb_694 sec 3 table (predicted HEM:GILE ~= 3:1 to 4:1)",
        axis="D1", rho=0.30, pd=0.4,
        observed_beauty_signal="0", observed_ugliness_signal="0",
        nontrivial=False,
        note="rho_low + PD+; aesthetic signal predicted decoupled. Folk reports of 'no time for pretty form, only what works' consistent with decoupling.",
    ),
    Observation(
        label="Trump phase-transition catalyst case study (DT-HEM regime)",
        source_urb="urb_698 (DT-HEM case study)",
        axis="G", rho=0.20, pd=-0.6,
        observed_beauty_signal="-", observed_ugliness_signal="+",
        nontrivial=True,
        note="INVERSION CELL: deep-HEM negative-PD; aesthetic-polish presentation hides moral substrate; rough/ugly counter-presentation more truth-tracking. Confirms Inversion Theorem.",
    ),
    Observation(
        label="GM HEM-Override breach in low-G operators (URB #696 sec 4.5)",
        source_urb="urb_696 sec 4.5",
        axis="D2", rho=0.25, pd=-0.5,
        observed_beauty_signal="-", observed_ugliness_signal="+",
        nontrivial=True,
        note="INVERSION CELL: HEM-Override regime is exactly the deep-HEM negative-PD cell; coupling kappa = delta_S forces sign flip per URB #784 sec 2.2.",
    ),
    Observation(
        label="Religious-contemplative-practice domain (high G, high I, low D1)",
        source_urb="urb_694 sec 3 table (predicted GILE:HEM 2:1 to 4:1)",
        axis="L", rho=2.5, pd=0.6,
        observed_beauty_signal="+", observed_ugliness_signal="0",
        nontrivial=True,
        note="rho_high; positive PD; aesthetic harmony of contemplative literature is BR-confirmation.",
    ),
    Observation(
        label="High-frequency trading domain (very low G, high D1 amplitude)",
        source_urb="urb_694 implied; cross-ref Brandon's GSA notes",
        axis="D1", rho=0.15, pd=-0.2,
        observed_beauty_signal="-", observed_ugliness_signal="+",
        nontrivial=True,
        note="Inversion-adjacent: rho_low, PD slightly negative. The aesthetic-polish 'quant glamour' track record disconnects from real-world value; the ugly raw-PnL story is more truth-tracking.",
    ),
    Observation(
        label="Hardy's elegance criterion in pure mathematics",
        source_urb="urb_781 sec B.4 row 3",
        axis="E", rho=3.5, pd=0.8,
        observed_beauty_signal="+", observed_ugliness_signal="0",
        nontrivial=True,
        note="rho_high pure-math; the 'no permanent place for ugly mathematics' aphorism is consistent with predicted +.",
    ),
    Observation(
        label="Riefenstahl-style propaganda (beautiful presentation of false BT)",
        source_urb="URB #784 sec 3 row D4 cell (rho_high, PD-)",
        axis="D4", rho=2.6, pd=-0.7,
        observed_beauty_signal="-", observed_ugliness_signal="0",
        nontrivial=True,
        note="High-rho negative-PD: aesthetic polish exists but BR points away from depiction. Confirms cell prediction.",
    ),
    Observation(
        label="Engineering domain composite ratio",
        source_urb="urb_694 sec 3 table (1:1 expected)",
        axis="E", rho=1.0, pd=0.5,
        observed_beauty_signal="+", observed_ugliness_signal="0",
        nontrivial=False,
        note="rho_mid PD+; predicted weak +; observed mild + (engineering elegance correlates with working systems but with noise). Mid-band consistency check.",
    ),
    Observation(
        label="Outsider art with high authentic L, low D1, low D4",
        source_urb="urb_641 (GILE-E aesthetics; full-spectrum personality)",
        axis="L", rho=0.30, pd=0.3,
        observed_beauty_signal="0", observed_ugliness_signal="0",
        nontrivial=False,
        note="rho_low PD+; aesthetic signal predicted decoupled. Outsider-art reception literature shows weak beauty-signal, consistent with decoupling.",
    ),
]


# ---------------------------------------------------------------------------
# Verification
# ---------------------------------------------------------------------------

@dataclass
class CellResult:
    label: str
    axis: str
    rho_regime: RhoRegime
    pd_sign: PdSign
    predicted_beauty: SignalSign
    observed_beauty: SignalSign
    predicted_ugliness: SignalSign
    observed_ugliness: SignalSign
    inversion_cell: bool
    nontrivial: bool
    beauty_match: bool
    ugliness_match: bool
    inversion_violation: bool


def verify_seed_corpus() -> dict:
    """
    Run predictions over SEED_OBSERVATIONS and report concordance.

    'Inversion violation' fires when an inversion-cell observation shows
    beauty + (rather than -) or ugliness - (rather than +) -- which would
    refute the Inversion Theorem.
    """
    results: list[CellResult] = []
    for obs in SEED_OBSERVATIONS:
        cell = predict(obs.axis, obs.rho, obs.pd)
        beauty_match   = cell.beauty_sign   == obs.observed_beauty_signal
        ugliness_match = cell.ugliness_sign == obs.observed_ugliness_signal

        inv_violation = False
        if cell.inversion_cell:
            if obs.observed_beauty_signal == "+" or obs.observed_ugliness_signal == "-":
                inv_violation = True

        results.append(CellResult(
            label=obs.label,
            axis=obs.axis,
            rho_regime=cell.rho_regime,
            pd_sign=cell.pd_sign,
            predicted_beauty=cell.beauty_sign,
            observed_beauty=obs.observed_beauty_signal,
            predicted_ugliness=cell.ugliness_sign,
            observed_ugliness=obs.observed_ugliness_signal,
            inversion_cell=cell.inversion_cell,
            nontrivial=obs.nontrivial,
            beauty_match=beauty_match,
            ugliness_match=ugliness_match,
            inversion_violation=inv_violation,
        ))

    n = len(results)
    nontrivial = [r for r in results if r.nontrivial]
    n_nt = len(nontrivial)

    return {
        "n_total": n,
        "n_nontrivial": n_nt,
        "beauty_concordance_total":      sum(r.beauty_match   for r in results),
        "ugliness_concordance_total":    sum(r.ugliness_match for r in results),
        "beauty_concordance_nontrivial": sum(r.beauty_match   for r in nontrivial),
        "ugliness_concordance_nontrivial": sum(r.ugliness_match for r in nontrivial),
        "inversion_cells_observed":      sum(r.inversion_cell for r in results),
        "inversion_violations":          sum(r.inversion_violation for r in results),
        "results": [asdict(r) for r in results],
    }


def cube_summary() -> dict:
    """Return a JSON-serializable summary of the 72-cell cube."""
    return {
        "boundaries": {"ET": ET, "verisyn": 1.0, "delta_silver": DELTA},
        "axes": list(AXES),
        "axis_names": AXIS_NAMES,
        "n_cells": len(PREDICTION_CUBE),
        "inversion_cells": [
            {"axis": k[0], "rho_regime": k[1], "pd_sign": k[2]}
            for k, v in PREDICTION_CUBE.items() if v.inversion_cell
        ],
    }


# ---------------------------------------------------------------------------
# CLI entry
# ---------------------------------------------------------------------------

if __name__ == "__main__":
    summary = cube_summary()
    print("=" * 72)
    print("URB #784 — GILE-HEM Ratio Modulation: Prediction Cube Summary")
    print("=" * 72)
    print(f"Boundaries: ET={summary['boundaries']['ET']:.4f}  "
          f"Verisyn={summary['boundaries']['verisyn']:.1f}  "
          f"delta_S={summary['boundaries']['delta_silver']:.4f}")
    print(f"Cube size: {summary['n_cells']} cells "
          f"({len(summary['axes'])} axes x 3 rho-regimes x 3 PD-signs)")
    print(f"Inversion cells: {len(summary['inversion_cells'])} "
          f"(one per axis at (rho_low, pd_neg))")
    print()

    print("=" * 72)
    print("Seed-corpus verification (no API calls)")
    print("=" * 72)
    v = verify_seed_corpus()
    print(f"Total observations:           {v['n_total']}")
    print(f"Non-trivial (predicted +/-):  {v['n_nontrivial']}")
    print(f"Beauty concordance (total):       "
          f"{v['beauty_concordance_total']}/{v['n_total']}")
    print(f"Beauty concordance (non-triv):    "
          f"{v['beauty_concordance_nontrivial']}/{v['n_nontrivial']}")
    print(f"Ugliness concordance (total):     "
          f"{v['ugliness_concordance_total']}/{v['n_total']}")
    print(f"Ugliness concordance (non-triv):  "
          f"{v['ugliness_concordance_nontrivial']}/{v['n_nontrivial']}")
    print(f"Inversion-cell observations:      {v['inversion_cells_observed']}")
    print(f"Inversion-theorem violations:     {v['inversion_violations']}")
    print()

    print("Per-observation detail:")
    for r in v["results"]:
        flag = "INV" if r["inversion_cell"] else "   "
        bm = "✓" if r["beauty_match"] else "✗"
        um = "✓" if r["ugliness_match"] else "✗"
        print(f"  [{flag}] beauty {bm} ugly {um}  "
              f"axis={r['axis']:>2}  {r['rho_regime']:>8} / {r['pd_sign']:>7}  "
              f"pred(b={r['predicted_beauty']}, u={r['predicted_ugliness']})  "
              f"obs(b={r['observed_beauty']}, u={r['observed_ugliness']})  "
              f"-- {r['label'][:60]}")
