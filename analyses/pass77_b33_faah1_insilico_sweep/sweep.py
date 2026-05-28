"""
Pass-77-B33 — Phase-1 FAAH-1 In-Silico Knockdown Parameter Sweep
=================================================================

Literature-grounded surrogate model of the FAAH-1 -> elevated AEA/2-AG ->
NPR-19 -> behavioral-output pathway in C. elegans. Produces the in-silico
phenotype matrix specified in Pass-77-B32 Phase 1.

HONEST #69 (declared at top):
    This is a SURROGATE MODEL, not literal OpenWorm c302/Sibernetic execution.
    The full c302 NeuroML simulation requires jNeuroML/Java + Sibernetic SPH
    + per-neuron NPR-19 expression mapping from CeNGEN, which is Phase-1b
    workstation-grade work. The surrogate captures the directionality and
    approximate magnitudes from primary literature:

      - Pastuhov et al. 2016 Nat Commun 7:13651
            2-AG/NPR-19 INHIBITS Gqα-PKC-JNK signalling
            → elevated NPR-19 tone REDUCES ASH-mediated aversive responses
      - Oakes et al. 2017 J. Neurosci 37:2859
            cannabinoids alter monoaminergic-modulated feeding/locomotion;
            effects abolished in npr-19 mutants
      - Lehtonen et al. 2008 J. Lipid Res. 49:2456
            endogenous AEA/2-AG quantification in C. elegans
      - CeNGEN single-cell expression atlas (Hammarlund 2018+)
            npr-19 expression in pharyngeal + sensory + interneurons

    Falsifier F1 (pre-reg B32 §3.1): if surrogate produces NO signature
    across all 8 primitives at any knockdown level, model too coarse.
    Falsifier F2 (pre-reg B32 §3.2): wet-lab correlation must reach
    r ≥ 0.20 (P2-target r ≥ 0.50). Wet-lab is Phase 2.

Outputs:
    results.csv        — per-(knockdown, behavior, seed) raw rows
    summary.csv        — per-(knockdown, behavior) mean ± sd + Hedges' g vs WT
    pre_reg_check.txt  — P1 verdict + F1 verdict
"""

from __future__ import annotations
import csv
import math
import os
from pathlib import Path

import numpy as np

OUTDIR = Path(__file__).parent
SEED_ROOT = 20260527

# --- Literature-grounded effect specification ---
# For each behavior: (sign, max_effect_fraction_at_full_kd, biological_noise_sd_fraction, source_anchor)
# Sign: -1 = knockdown reduces; +1 = knockdown increases.
# max_effect_fraction: predicted maximum fractional change vs WT at kd=0.95.
# noise_sd: biological sd as fraction of WT baseline; standard C. elegans behavioral noise ~10-20%.
BEHAVIORS = {
    "locomotion_speed":         dict(sign=-1, max_eff=0.15, noise=0.12, anchor="Oakes2017"),
    "reversal_rate":            dict(sign=-1, max_eff=0.25, noise=0.18, anchor="Pastuhov2016"),
    "omega_turn_rate":          dict(sign=-1, max_eff=0.20, noise=0.18, anchor="Pastuhov2016"),
    "foraging_bout_duration":   dict(sign=+1, max_eff=0.15, noise=0.15, anchor="Oakes2017"),
    "chemotaxis_index":         dict(sign=-1, max_eff=0.10, noise=0.10, anchor="Oakes2017"),
    "thermotaxis_index":        dict(sign=-1, max_eff=0.05, noise=0.10, anchor="general"),
    "osmotic_aversion_response":dict(sign=-1, max_eff=0.30, noise=0.15, anchor="Pastuhov2016*"),  # P1 target
    "mechano_aversion_response":dict(sign=-1, max_eff=0.20, noise=0.15, anchor="Pastuhov2016"),
}

# WT baseline (arbitrary normalized units; surrogate-internal)
WT_BASELINE = 1.0

# FAAH-1 knockdown levels (B32 §3.1)
KNOCKDOWN_LEVELS = [0.0, 0.10, 0.30, 0.50, 0.80, 0.95]

# Replicate seeds per (kd, behavior)
N_SEEDS = 100

# Hill-function dose-response: AEA elevation increases nonlinearly with FAAH-1 loss.
# Calibrated so that kd=0.50 produces ~60% of full effect (sigmoid midpoint near kd=0.40),
# matching the empirical observation that partial FAAH knockdown still elevates AEA substantially
# (mammalian FAAH inhibitor PK/PD studies; Habib 2019 Cameron 1.7× from heterozygous-effective).
HILL_K = 0.40   # midpoint
HILL_N = 2.0    # cooperativity


def dose_response(kd: float) -> float:
    """Return fraction-of-max-effect at given FAAH-1 knockdown level."""
    if kd <= 0:
        return 0.0
    return (kd ** HILL_N) / (kd ** HILL_N + HILL_K ** HILL_N)


def hedges_g(a: np.ndarray, b: np.ndarray) -> float:
    """Hedges' g effect size (bias-corrected Cohen's d)."""
    n1, n2 = len(a), len(b)
    if n1 < 2 or n2 < 2:
        return float("nan")
    s1, s2 = a.std(ddof=1), b.std(ddof=1)
    sp = math.sqrt(((n1 - 1) * s1 ** 2 + (n2 - 1) * s2 ** 2) / (n1 + n2 - 2))
    if sp == 0:
        return float("nan")
    d = (a.mean() - b.mean()) / sp
    J = 1 - 3 / (4 * (n1 + n2) - 9)
    return d * J


def run_sweep():
    rng = np.random.default_rng(SEED_ROOT)
    rows = []
    for behavior, spec in BEHAVIORS.items():
        sign = spec["sign"]
        max_eff = spec["max_eff"]
        noise = spec["noise"]
        for kd in KNOCKDOWN_LEVELS:
            dr = dose_response(kd)
            mean_shift = sign * max_eff * dr  # fractional shift from WT
            mu = WT_BASELINE * (1.0 + mean_shift)
            sigma = WT_BASELINE * noise
            samples = rng.normal(loc=mu, scale=sigma, size=N_SEEDS)
            for seed_idx, value in enumerate(samples):
                rows.append(dict(
                    behavior=behavior,
                    knockdown_level=kd,
                    seed=seed_idx,
                    value=float(value),
                    anchor=spec["anchor"],
                ))
    return rows


def summarize(rows):
    """Per-(behavior, kd) mean/sd + Hedges' g vs WT."""
    summary = []
    by_bk = {}
    for r in rows:
        key = (r["behavior"], r["knockdown_level"])
        by_bk.setdefault(key, []).append(r["value"])

    for behavior in BEHAVIORS:
        wt = np.array(by_bk[(behavior, 0.0)])
        for kd in KNOCKDOWN_LEVELS:
            vals = np.array(by_bk[(behavior, kd)])
            g = hedges_g(vals, wt) if kd > 0 else 0.0
            summary.append(dict(
                behavior=behavior,
                knockdown_level=kd,
                n=len(vals),
                mean=float(vals.mean()),
                sd=float(vals.std(ddof=1)),
                pct_of_WT=float(vals.mean() / wt.mean()),
                hedges_g_vs_WT=float(g),
            ))
    return summary


def pre_reg_check(summary):
    """
    P1: at kd >= 0.50, osmotic_aversion_response < 70% of WT AND |g| >= 0.5.
    F1: if NO behavior shows |g| >= 0.2 at ANY kd level, model too coarse.
    """
    lines = []
    lines.append("=" * 72)
    lines.append("Pass-77-B33 — Pre-Registered Falsifier Checks")
    lines.append("=" * 72)

    # P1
    p1_rows = [s for s in summary
               if s["behavior"] == "osmotic_aversion_response"
               and s["knockdown_level"] >= 0.50]
    p1_pass = all(s["pct_of_WT"] < 0.70 and abs(s["hedges_g_vs_WT"]) >= 0.5
                  for s in p1_rows)
    lines.append("")
    lines.append(f"P1 (osmotic-aversion < 70% WT AND |g| >= 0.5 at kd >= 0.50):")
    for s in p1_rows:
        lines.append(f"  kd={s['knockdown_level']:.2f}  "
                     f"mean={s['mean']:.3f}  pct_WT={s['pct_of_WT']:.3f}  "
                     f"|g|={abs(s['hedges_g_vs_WT']):.3f}")
    lines.append(f"  P1 VERDICT: {'PASS' if p1_pass else 'FAIL'}")

    # F1
    max_abs_g = max(abs(s["hedges_g_vs_WT"]) for s in summary if s["knockdown_level"] > 0)
    f1_signature_present = max_abs_g >= 0.2
    lines.append("")
    lines.append(f"F1 (some signature present, |g| >= 0.2 at any kd):")
    lines.append(f"  max |g| across all (behavior, kd>0) cells = {max_abs_g:.3f}")
    lines.append(f"  F1 VERDICT: {'NOT REFUTED' if f1_signature_present else 'REFUTED'}")

    # Per-behavior top-line
    lines.append("")
    lines.append("Per-behavior max-effect at kd=0.95:")
    for s in [x for x in summary if x["knockdown_level"] == 0.95]:
        lines.append(f"  {s['behavior']:30s}  pct_WT={s['pct_of_WT']:.3f}  "
                     f"|g|={abs(s['hedges_g_vs_WT']):.3f}")

    return "\n".join(lines), p1_pass, f1_signature_present


def main():
    print("[B33] Running FAAH-1 in-silico knockdown sweep ...")
    print(f"      {len(BEHAVIORS)} behaviors × {len(KNOCKDOWN_LEVELS)} kd levels × {N_SEEDS} seeds "
          f"= {len(BEHAVIORS)*len(KNOCKDOWN_LEVELS)*N_SEEDS} simulated worm-runs")

    rows = run_sweep()
    summary = summarize(rows)
    report, p1_pass, f1_ok = pre_reg_check(summary)

    # results.csv
    with (OUTDIR / "results.csv").open("w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=["behavior", "knockdown_level", "seed", "value", "anchor"])
        w.writeheader()
        w.writerows(rows)

    # summary.csv
    with (OUTDIR / "summary.csv").open("w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=["behavior", "knockdown_level", "n",
                                          "mean", "sd", "pct_of_WT", "hedges_g_vs_WT"])
        w.writeheader()
        w.writerows(summary)

    # pre_reg_check.txt
    (OUTDIR / "pre_reg_check.txt").write_text(report + "\n")

    print()
    print(report)
    print()
    print(f"[B33] Outputs written to {OUTDIR}/")
    print(f"      results.csv ({len(rows)} rows)")
    print(f"      summary.csv ({len(summary)} rows)")
    print(f"      pre_reg_check.txt")
    return 0 if (p1_pass and f1_ok) else 1


if __name__ == "__main__":
    raise SystemExit(main())
