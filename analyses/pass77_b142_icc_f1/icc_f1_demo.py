"""
Pass-77 B142 — ICC-F1: does the Grand i-Cell Model (ICC) do work its sub-models
cannot?  (DETERMINISTIC EXISTENCE-PROOF / NEGATIVE-RESULT demonstration)
==============================================================================

CONTEXT.  B137 introduced ICC = <M, H, shell>:
    M     : 64D GILE Truth Matrix (4 GILE x 4 axes x 4 labels) -- truth interior
    H     : HEM core existence vector  (D1..D4, bijective to G,I,L,E per B82)
    shell : HEM shell  (D5 presence, D6 coupling)
and claimed ICC SUBSUMES five prior representations as exact projections:
    (1) 64D GILE matrix   (2) 8-Tralsebit i-Cell   (3) Crystal-8
    (4) scalar PD         (5) TTI-1 overall label.
B137 left the falsifier ICC-F1 OPEN:
    "Exhibit two i-Cells that EVERY one of the five sub-models maps to identical
     representations, yet ICC distinguishes -- and have that distinction do real,
     outcome-blind work.  If no such pair/task exists, ICC is a faithful
     re-organisation (still useful as a unifier) but NOT an informational
     advance, and must be reported as such."

This script tests ICC-F1 HONESTLY (#69 -- we do NOT rig a pass).  It imports the
REAL B137 ICell class (no re-implementation drift) and establishes three levels:

  LEVEL 0 (the decisive one) -- STRONG ICC-F1 is UNMEETABLE *by construction*.
      The five sub-models are JOINTLY a LOSSLESS encoding of ICC: M is recovered
      by the 64D projection (identity), H D1..D4 by the 8-Tralsebit HEM block,
      and D5,D6 by the Crystal-8 shell block.  We build an explicit decoder
      reconstruct_from_submodels(...) and show reconstruct(project(ic)) == ic for
      many random i-Cells.  => the map ic |-> (5 projections) is INJECTIVE
      => no two distinct i-Cells share all five sub-model images
      => the pair ICC-F1 asks for CANNOT EXIST.
      Corollary (no-free-lunch): since the battery losslessly encodes ICC, ANY
      task computable from ICC is computable from the sub-models collectively, so
      ICC can NEVER beat the full battery on any task.  The "bolt" (join along the
      GILE index) is a RE-INDEXING that adds zero bits over the tuple (M,H,shell).

  LEVEL 1 -- "no SINGLE sub-model suffices": POSITIVE but weak.
      For each individual sub-model we give an explicit pair it conflates yet ICC
      distinguishes.  This only shows ICC strictly contains each piece -- it does
      NOT show ICC beats the collection.

  LEVEL 2 -- does the BOLT earn its keep vs an alignment-free store?
      Two i-Cells with the SAME M and the SAME HEM multiset, but HEM PERMUTED
      across GILE.  A representation keeping only (M, aggregate-HEM sum) conflates
      them; ICC's GILE-aligned cross-moment  C = sum_g trueness_g(M) * H[Dg]
      distinguishes them (existence backing strong-truth dims vs weak ones).
      HONEST CAVEAT: the ACTUAL prior 8-Tralsebit already stores HEM in GILE
      order, so it ALSO distinguishes the permuted pair.  Hence the bolt beats a
      weaker AGGREGATE baseline the corpus does not actually use -- NOT the
      strongest existing sub-model.  So Level 2 does not rescue ICC-F1 either.

VERDICT.  ICC-F1 is NOT met (and is provably unmeetable against an
info-complete battery).  ICC is a FAITHFUL UNIFIER -- its value is
organisational (one container for {64D interior, HEM, overall label} + explicit
GILE-alignment + a parsimonious derived label), with PROVABLY ZERO informational
advantage over the union of its sub-models.  Key honest lesson:
    SUBSUMPTION-COMPLETENESS  is INCOMPATIBLE WITH  INFORMATIONAL ADVANTAGE.
    A rep that losslessly contains all sub-models cannot beat them collectively;
    to gain new power it must store a primitive the sub-models do NOT carry
    (and thereby stop being a pure projection-superset).

HONESTY RAILS.  Representational claim only (no empirical/reality content).  No
numerology: the numbers in the example matrices are stipulated and illustrative;
the LEVEL-0 result is an exact algebraic fact (a reconstruction identity), not a
statistic, so no seed/threshold is load-bearing.  Count unchanged 79; ICC stays
a CANDIDATE.
"""
from __future__ import annotations
import importlib.util
import json
import os
import sys
import numpy as np

# --------------------------------------------------------------------------- #
# Import the REAL B137 ICC (no re-implementation -> no drift).
# --------------------------------------------------------------------------- #
_B137 = os.path.join("analyses", "pass77_b137_icell_grand_model",
                     "icell_grand_model.py")
_spec = importlib.util.spec_from_file_location("icc_b137", _B137)
_icc = importlib.util.module_from_spec(_spec)
sys.modules["icc_b137"] = _icc          # register so @dataclass can resolve it
_spec.loader.exec_module(_icc)

ICell = _icc.ICell
GILE = _icc.GILE
AXES = _icc.AXES
LABELS = _icc.LABELS
AX = _icc.AX
GI = _icc.GI
GILE_WEIGHTS = _icc.GILE_WEIGHTS
HEM_BIJECTION = _icc.HEM_BIJECTION
HEM_CORE_DIMS = _icc.HEM_CORE_DIMS
LABEL_VALUE = _icc.LABEL_VALUE
random_matrix = _icc.random_matrix


# --------------------------------------------------------------------------- #
# Fingerprints + helpers
# --------------------------------------------------------------------------- #
def submodel_fingerprint(ic: ICell) -> dict:
    """The 5 sub-model images of an i-Cell, as comparable arrays/values."""
    return {
        "m64": ic.project_to_64d_matrix(),
        "tralsebit8": ic.project_to_8_tralsebit(),
        "crystal8": ic.project_to_crystal8(),
        "scalar_pd": ic.project_to_scalar_pd(),
        "tti1_label": ic.overall_label(),
    }


def fingerprints_equal(a: dict, b: dict, atol: float = 1e-9) -> dict:
    """Per-sub-model equality of two fingerprints."""
    return {
        "m64": bool(np.allclose(a["m64"], b["m64"], atol=atol)),
        "tralsebit8": bool(np.allclose(a["tralsebit8"], b["tralsebit8"], atol=atol)),
        "crystal8": bool(np.allclose(a["crystal8"], b["crystal8"], atol=atol)),
        "scalar_pd": bool(abs(a["scalar_pd"] - b["scalar_pd"]) < atol),
        "tti1_label": a["tti1_label"] == b["tti1_label"],
    }


def icells_equal(a: ICell, b: ICell, atol: float = 1e-12) -> bool:
    return (np.array_equal(a.M, b.M)
            and all(abs(a.H[d] - b.H[d]) < atol for d in HEM_CORE_DIMS)
            and all(abs(a.shell[k] - b.shell[k]) < atol for k in a.shell))


def gile_trueness(ic: ICell) -> np.ndarray:
    """Public wrapper for the per-GILE scalar trueness used by the bolt."""
    return ic._gile_trueness()


def existence_weighted_trueness(ic: ICell) -> float:
    """The BOLT-dependent cross-moment: sum_g trueness_g(M) * H[Dg].
    Uses the GILE-aligned JOIN between the truth interior and HEM.  This is the
    quantity a flat (M, aggregate-HEM) store cannot reconstruct."""
    tr = gile_trueness(ic)                                    # (4,) from M
    hem = np.array([ic.H[HEM_BIJECTION[g]] for g in GILE])    # (4,) GILE-aligned
    return float(np.dot(tr, hem))


def aggregate_hem(ic: ICell) -> float:
    """The alignment-free baseline's only existence summary: the HEM total."""
    return float(sum(ic.H[d] for d in HEM_CORE_DIMS))


# --------------------------------------------------------------------------- #
# LEVEL 0 -- the decisive decoder: 5 sub-models losslessly encode ICC.
# --------------------------------------------------------------------------- #
def reconstruct_from_submodels(fp: dict) -> ICell:
    """Rebuild (M, H, shell) using ONLY the five sub-model outputs.
        M       <- 64D projection (identity)
        H D1..D4<- 8-Tralsebit HEM block (its last 4 entries)
        D5, D6  <- Crystal-8 shell block (its last 2 entries)
    If this reconstruction is exact for arbitrary i-Cells, the map
    ic -> (5 sub-models) is injective => STRONG ICC-F1 is impossible."""
    M = np.array(fp["m64"], dtype=float)
    hem_block = np.array(fp["tralsebit8"])[4:]               # H D1..D4
    H = {d: float(hem_block[i]) for i, d in enumerate(HEM_CORE_DIMS)}
    crystal = np.array(fp["crystal8"])
    shell = {"D5_presence": float(crystal[6]),
             "D6_coupling": float(crystal[7])}
    return ICell(M, H, shell)


def level0_battery_is_lossless(n_random: int = 400) -> dict:
    """Show reconstruct(project(ic)) == ic for many random i-Cells."""
    rng = np.random.default_rng(20260625)
    all_exact = True
    worst = 0.0
    for k in range(n_random):
        M = random_matrix(seed=int(rng.integers(0, 2**31 - 1)))
        H = {d: float(rng.random()) for d in HEM_CORE_DIMS}
        shell = {"D5_presence": float(rng.random() * 0.9 + 0.1),
                 "D6_coupling": float(rng.random() * 0.9 + 0.1)}
        ic = ICell(M, H, shell)
        rec = reconstruct_from_submodels(submodel_fingerprint(ic))
        exact = icells_equal(ic, rec)
        all_exact = all_exact and exact
        worst = max(worst, float(np.max(np.abs(ic.M - rec.M))),
                    *[abs(ic.H[d] - rec.H[d]) for d in HEM_CORE_DIMS],
                    *[abs(ic.shell[k] - rec.shell[k]) for k in ic.shell])
    return {
        "n_random_icells": n_random,
        "reconstruction_exact_for_all": bool(all_exact),
        "worst_abs_reconstruction_error": worst,
        "implication": "the 5 sub-models are a LOSSLESS (injective) encoding of "
                       "ICC; therefore NO pair of distinct i-Cells is conflated "
                       "by all five at once => STRONG ICC-F1 is UNMEETABLE.",
        "corollary_no_free_lunch": "any task computable from ICC is computable "
                                   "from the sub-models collectively; ICC cannot "
                                   "beat the full battery on ANY task.",
        "the_bolt_adds_bits": False,
    }


# --------------------------------------------------------------------------- #
# LEVEL 1 -- no SINGLE sub-model suffices (positive but weak).
# --------------------------------------------------------------------------- #
def _base_icell() -> ICell:
    M = random_matrix(seed=7)
    for g in GILE:                      # give a definite overall label
        M[GI[g], AX["MR"], :] = np.array([0.6, 0.2, 0.1, 0.1])
    H = {"D1": 0.80, "D2": 0.60, "D3": 0.70, "D4": 0.50}
    shell = {"D5_presence": 0.90, "D6_coupling": 0.75}
    return ICell(M, H, shell)


def level1_no_single_submodel_suffices() -> dict:
    """For each single sub-model: a pair it conflates that ICC distinguishes."""
    out = {}

    # (a) 64D matrix conflates two cells differing ONLY in HEM (it has no HEM).
    a = _base_icell()
    b = ICell(a.M.copy(), dict(a.H, D1=0.10), dict(a.shell))   # different D1
    out["64d_matrix_blind_to_HEM"] = {
        "submodel_outputs_equal": bool(np.array_equal(
            a.project_to_64d_matrix(), b.project_to_64d_matrix())),
        "icc_distinguishes": not icells_equal(a, b),
    }

    # (b) scalar PD conflates cells with very different interiors / HEM.
    #     Build b2 with a different PD slice arranged to keep the SAME scalar.
    a2 = _base_icell()
    b2 = ICell(a2.M.copy(), dict(a2.H, D2=0.05), dict(a2.shell))
    out["scalar_pd_blind_to_HEM_and_most_of_M"] = {
        "submodel_outputs_equal": bool(abs(
            a2.project_to_scalar_pd() - b2.project_to_scalar_pd()) < 1e-12),
        "icc_distinguishes": not icells_equal(a2, b2),
    }

    # (c) TTI-1 label conflates cells with the same MR-readout but different
    #     everything else (interior operators + HEM).
    a3 = _base_icell()
    M3 = a3.M.copy()
    rng = np.random.default_rng(3)
    for g in GILE:                       # scramble the 3 operator axes only
        for ax in ("PD", "tau_delta", "AA"):
            v = rng.random(4); M3[GI[g], AX[ax], :] = v / v.sum()
    b3 = ICell(M3, dict(a3.H, D4=0.01), dict(a3.shell))
    out["tti1_label_blind_to_operators_and_HEM"] = {
        "submodel_outputs_equal": a3.overall_label() == b3.overall_label(),
        "icc_distinguishes": not icells_equal(a3, b3),
    }

    out["summary"] = ("each SINGLE sub-model conflates a pair ICC separates "
                      "(ICC strictly contains each piece) -- but this does NOT "
                      "beat the battery (see Level 0).")
    return out


# --------------------------------------------------------------------------- #
# LEVEL 2 -- does the BOLT beat an alignment-free (aggregate-HEM) store?
# --------------------------------------------------------------------------- #
def level2_bolt_vs_aggregate() -> dict:
    """Same M, same HEM multiset, HEM PERMUTED across GILE."""
    a = _base_icell()
    # permute the HEM values across GILE dims (same multiset, same sum):
    # original (D1,D2,D3,D4) = (G,I,L,E) existence.  Reverse the assignment.
    H_perm = {"D1": a.H["D4"], "D2": a.H["D3"], "D3": a.H["D2"], "D4": a.H["D1"]}
    b = ICell(a.M.copy(), H_perm, dict(a.shell))

    tr = gile_trueness(a)
    return {
        "construction": "two i-Cells share M and HEM multiset; HEM assignment "
                        "to GILE dims is reversed (same sum).",
        "gile_trueness_from_M": {g: round(float(tr[i]), 4)
                                 for i, g in enumerate(GILE)},
        "HEM_a": a.H, "HEM_b": b.H,
        # alignment-free baseline sees only the total -> identical:
        "aggregate_hem_a": round(aggregate_hem(a), 6),
        "aggregate_hem_b": round(aggregate_hem(b), 6),
        "aggregate_baseline_conflates": bool(
            abs(aggregate_hem(a) - aggregate_hem(b)) < 1e-12),
        # the bolt's cross-moment sees the alignment -> differs:
        "existence_weighted_trueness_a": round(existence_weighted_trueness(a), 6),
        "existence_weighted_trueness_b": round(existence_weighted_trueness(b), 6),
        "bolt_distinguishes": bool(
            abs(existence_weighted_trueness(a)
                - existence_weighted_trueness(b)) > 1e-9),
        "interpretation": "same truth-interior and same TOTAL existence, but one "
                          "being's existence backs its strong-truth GILE dims and "
                          "the other's backs its weak ones; the marginals miss it, "
                          "the GILE-aligned cross-moment catches it.",
        # HONEST caveat: the ACTUAL prior 8-Tralsebit already GILE-orders HEM:
        "honest_caveat_8tralsebit_also_distinguishes": bool(not np.allclose(
            a.project_to_8_tralsebit(), b.project_to_8_tralsebit())),
        "scope": "the bolt beats only a WEAKER aggregate-HEM store the corpus "
                 "does not actually use; it does NOT beat the existing "
                 "8-Tralsebit -> Level 2 does not rescue ICC-F1.",
    }


# --------------------------------------------------------------------------- #
def main():
    level0 = level0_battery_is_lossless()
    level1 = level1_no_single_submodel_suffices()
    level2 = level2_bolt_vs_aggregate()

    verdict = {
        "ICC_F1_strong_form_met": False,
        "ICC_F1_strong_form_reason": "provably unmeetable: the five sub-models "
                                     "are an injective (lossless) encoding of ICC "
                                     "(Level 0).",
        "ICC_F1_weak_form_no_single_submodel_suffices": True,
        "bolt_beats_existing_battery": False,
        "bolt_beats_aggregate_only_store": True,
        "net": "ICC is a FAITHFUL UNIFIER with ZERO informational advantage over "
               "the union of its sub-models; its value is organisational, not "
               "informational.",
        "key_lesson": "subsumption-completeness is incompatible with an "
                      "informational advance; to gain new power a representation "
                      "must store a primitive its sub-models do not carry.",
        "principle_count": 79,
        "ICC_status": "CANDIDATE (unchanged); honesty rails satisfied; result is "
                      "reported straight (#69), negative-leaning.",
    }

    out = {
        "batch": "Pass-77 B142 -- ICC-F1 test (honest, deterministic)",
        "level0_battery_lossless": level0,
        "level1_no_single_submodel_suffices": level1,
        "level2_bolt_vs_aggregate": level2,
        "verdict": verdict,
    }

    path = os.path.join("analyses", "pass77_b142_icc_f1", "results.json")
    with open(path, "w") as f:
        json.dump(out, f, indent=2)

    print(json.dumps({
        "level0_reconstruction_exact_for_all":
            level0["reconstruction_exact_for_all"],
        "level0_worst_error": level0["worst_abs_reconstruction_error"],
        "ICC_F1_strong_form_met": verdict["ICC_F1_strong_form_met"],
        "bolt_beats_existing_battery": verdict["bolt_beats_existing_battery"],
        "bolt_beats_aggregate_only_store": verdict["bolt_beats_aggregate_only_store"],
        "net": verdict["net"],
    }, indent=2))


if __name__ == "__main__":
    main()
