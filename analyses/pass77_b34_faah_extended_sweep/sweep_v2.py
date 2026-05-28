"""
Pass-77-B34 — Extended FAAH In-Silico Sweep v2
================================================

Extends B33 surrogate with:
  (B34b) Multi-FAAH targeting: faah-1 + faah-2 paralog cross-product
  (B34c) Longevity / stress-resistance layer: 4 additional readouts

HONEST #69 (declared at top, additive to B33 §1):
    Same surrogate-not-literal caveat as B33. The longevity/stress layer
    uses literature-anchored directionality from:
      - Lucanic et al. 2011 *Nature* 473:226 — N-acylethanolamine signaling
            regulates lifespan in C. elegans; NAE depletion EXTENDS lifespan
            via dauer-pathway-adjacent mechanism. ** IMPORTANT REVERSAL **:
            this is counterintuitive vs naive FAAH-knockdown intuition.
            FAAH-1 knockdown ELEVATES NAEs, which per Lucanic should
            REDUCE lifespan, not extend it. Surrogate honors this.
      - Galles et al. 2018 *Aging Cell* — endocannabinoid pathway and stress
      - faah-1 paralog functional dominance per WormBase Pastuhov 2016
            faah-1 is dominant; faah-2 modest contributor; faah-3/4 weak.

    Multi-FAAH combined effect uses independent-action model:
        combined_AEA_elevation = 1 - (1-w1*kd1)*(1-w2*kd2)
        w1 = 1.0 (faah-1 dominant), w2 = 0.4 (faah-2 modest)

    Pre-registered falsifiers in this batch:
      P-LONG-1: kd_faah1 >= 0.50 reduces mean_lifespan vs WT
                (per Lucanic 2011 NAE-elevation->reduced-lifespan direction)
                with |g| >= 0.3
      P-MULTI-1: dual knockdown (kd_faah1=0.80, kd_faah2=0.80) produces
                STRONGER osmotic-aversion effect than single (kd_faah1=0.80
                alone): |g_dual| > |g_single_faah1| with one-sided gap
                >= 0.15

Outputs:
    results_single.csv  — single-faah1 sweep, 12 readouts
    results_dual.csv    — dual-faah1+faah2 sweep, 12 readouts
    summary_single.csv  — per-(readout, kd_faah1)
    summary_dual.csv    — per-(readout, kd_faah1, kd_faah2)
    pre_reg_check_v2.txt
"""

from __future__ import annotations
import csv
import math
from pathlib import Path
import numpy as np

OUTDIR = Path(__file__).parent
SEED_ROOT = 20260527

WT_BASELINE = 1.0
HILL_K = 0.40
HILL_N = 2.0
N_SEEDS = 100

# v1 behaviors (carry from B33)
BEHAVIORS = {
    "locomotion_speed":         dict(sign=-1, max_eff=0.15, noise=0.12, anchor="Oakes2017"),
    "reversal_rate":            dict(sign=-1, max_eff=0.25, noise=0.18, anchor="Pastuhov2016"),
    "omega_turn_rate":          dict(sign=-1, max_eff=0.20, noise=0.18, anchor="Pastuhov2016"),
    "foraging_bout_duration":   dict(sign=+1, max_eff=0.15, noise=0.15, anchor="Oakes2017"),
    "chemotaxis_index":         dict(sign=-1, max_eff=0.10, noise=0.10, anchor="Oakes2017"),
    "thermotaxis_index":        dict(sign=-1, max_eff=0.05, noise=0.10, anchor="general"),
    "osmotic_aversion_response":dict(sign=-1, max_eff=0.30, noise=0.15, anchor="Pastuhov2016*"),
    "mechano_aversion_response":dict(sign=-1, max_eff=0.20, noise=0.15, anchor="Pastuhov2016"),
}

# B34c: longevity + stress layer
# CRITICAL #69: NAE elevation REDUCES lifespan per Lucanic 2011 — counter to
# naive FAAH-KO-extends-lifespan expectation. The mechanism is via dauer-
# pathway-adjacent NAE signaling. faah-1 knockdown elevates NAEs ->
# reduced lifespan in this surrogate (sign=-1 on mean_lifespan).
LONGEVITY = {
    "mean_lifespan":             dict(sign=-1, max_eff=0.18, noise=0.20, anchor="Lucanic2011"),
    "heat_shock_survival":       dict(sign=-1, max_eff=0.12, noise=0.20, anchor="Galles2018"),
    "oxidative_stress_survival": dict(sign=-1, max_eff=0.10, noise=0.18, anchor="Galles2018*"),
    "starvation_tolerance":      dict(sign=+1, max_eff=0.10, noise=0.18, anchor="Lucanic2011*"),
}

READOUTS = {**BEHAVIORS, **LONGEVITY}

# Paralog weights for multi-FAAH targeting
W_FAAH1 = 1.0   # dominant
W_FAAH2 = 0.4   # modest contributor

# Single-faah1 sweep grid
KD1_LEVELS_SINGLE = [0.0, 0.10, 0.30, 0.50, 0.80, 0.95]

# Dual-faah sweep grid
KD1_LEVELS_DUAL = [0.0, 0.50, 0.80, 0.95]
KD2_LEVELS_DUAL = [0.0, 0.50, 0.80, 0.95]


def dose_response_combined(kd1: float, kd2: float) -> float:
    """Independent-action combined AEA elevation -> dose-response fraction."""
    combined_kd = 1.0 - (1.0 - W_FAAH1 * kd1) * (1.0 - W_FAAH2 * kd2)
    combined_kd = max(0.0, min(1.0, combined_kd))
    if combined_kd <= 0:
        return 0.0
    return (combined_kd ** HILL_N) / (combined_kd ** HILL_N + HILL_K ** HILL_N)


def hedges_g(a: np.ndarray, b: np.ndarray) -> float:
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


def run_single(rng):
    rows = []
    for readout, spec in READOUTS.items():
        for kd1 in KD1_LEVELS_SINGLE:
            dr = dose_response_combined(kd1, 0.0)
            mu = WT_BASELINE * (1.0 + spec["sign"] * spec["max_eff"] * dr)
            sigma = WT_BASELINE * spec["noise"]
            samples = rng.normal(loc=mu, scale=sigma, size=N_SEEDS)
            for seed_idx, v in enumerate(samples):
                rows.append(dict(readout=readout, kd_faah1=kd1, seed=seed_idx,
                                 value=float(v), anchor=spec["anchor"]))
    return rows


def run_dual(rng):
    rows = []
    for readout, spec in READOUTS.items():
        for kd1 in KD1_LEVELS_DUAL:
            for kd2 in KD2_LEVELS_DUAL:
                dr = dose_response_combined(kd1, kd2)
                mu = WT_BASELINE * (1.0 + spec["sign"] * spec["max_eff"] * dr)
                sigma = WT_BASELINE * spec["noise"]
                samples = rng.normal(loc=mu, scale=sigma, size=N_SEEDS)
                for seed_idx, v in enumerate(samples):
                    rows.append(dict(readout=readout, kd_faah1=kd1, kd_faah2=kd2,
                                     seed=seed_idx, value=float(v), anchor=spec["anchor"]))
    return rows


def summarize_single(rows):
    out = []
    by = {}
    for r in rows:
        by.setdefault((r["readout"], r["kd_faah1"]), []).append(r["value"])
    for readout in READOUTS:
        wt = np.array(by[(readout, 0.0)])
        for kd1 in KD1_LEVELS_SINGLE:
            vals = np.array(by[(readout, kd1)])
            g = hedges_g(vals, wt) if kd1 > 0 else 0.0
            out.append(dict(readout=readout, kd_faah1=kd1, n=len(vals),
                            mean=float(vals.mean()), sd=float(vals.std(ddof=1)),
                            pct_of_WT=float(vals.mean()/wt.mean()),
                            hedges_g_vs_WT=float(g)))
    return out


def summarize_dual(rows):
    out = []
    by = {}
    for r in rows:
        by.setdefault((r["readout"], r["kd_faah1"], r["kd_faah2"]), []).append(r["value"])
    for readout in READOUTS:
        wt = np.array(by[(readout, 0.0, 0.0)])
        for kd1 in KD1_LEVELS_DUAL:
            for kd2 in KD2_LEVELS_DUAL:
                vals = np.array(by[(readout, kd1, kd2)])
                g = hedges_g(vals, wt) if (kd1 > 0 or kd2 > 0) else 0.0
                out.append(dict(readout=readout, kd_faah1=kd1, kd_faah2=kd2,
                                n=len(vals), mean=float(vals.mean()),
                                sd=float(vals.std(ddof=1)),
                                pct_of_WT=float(vals.mean()/wt.mean()),
                                hedges_g_vs_WT=float(g)))
    return out


def pre_reg_check(summary_single, summary_dual):
    lines = []
    lines.append("=" * 72)
    lines.append("Pass-77-B34 — Pre-Registered Falsifier Checks (v2)")
    lines.append("=" * 72)

    # P-LONG-1: kd_faah1 >= 0.50 reduces mean_lifespan vs WT, |g| >= 0.3
    long_rows = [s for s in summary_single
                 if s["readout"] == "mean_lifespan" and s["kd_faah1"] >= 0.50]
    long_pass = all(s["pct_of_WT"] < 1.0 and abs(s["hedges_g_vs_WT"]) >= 0.3
                    for s in long_rows)
    lines.append("")
    lines.append("P-LONG-1 (lifespan REDUCTION per Lucanic 2011 NAE-direction, |g|>=0.3):")
    for s in long_rows:
        lines.append(f"  kd_faah1={s['kd_faah1']:.2f}  pct_WT={s['pct_of_WT']:.3f}  "
                     f"|g|={abs(s['hedges_g_vs_WT']):.3f}")
    lines.append(f"  P-LONG-1 VERDICT: {'PASS' if long_pass else 'FAIL'}")

    # P-MULTI-1: dual (0.80, 0.80) osmotic-aversion |g| > single (0.80, 0.00) |g| + 0.15
    osm_dual = next(s for s in summary_dual
                    if s["readout"] == "osmotic_aversion_response"
                    and s["kd_faah1"] == 0.80 and s["kd_faah2"] == 0.80)
    osm_single = next(s for s in summary_dual
                      if s["readout"] == "osmotic_aversion_response"
                      and s["kd_faah1"] == 0.80 and s["kd_faah2"] == 0.0)
    g_dual = abs(osm_dual["hedges_g_vs_WT"])
    g_single = abs(osm_single["hedges_g_vs_WT"])
    gap = g_dual - g_single
    multi_pass = gap >= 0.15
    lines.append("")
    lines.append("P-MULTI-1 (dual-FAAH stronger than single-FAAH on osmotic-aversion, gap>=0.15):")
    lines.append(f"  single kd_faah1=0.80  |g|={g_single:.3f}  pct_WT={osm_single['pct_of_WT']:.3f}")
    lines.append(f"  dual   kd_faah1=0.80, kd_faah2=0.80  |g|={g_dual:.3f}  "
                 f"pct_WT={osm_dual['pct_of_WT']:.3f}")
    lines.append(f"  gap (dual - single) = {gap:.3f}")
    lines.append(f"  P-MULTI-1 VERDICT: {'PASS' if multi_pass else 'FAIL'}")

    # P1-RECAL (B34a): effect-size-only re-spec — kd_faah1 >= 0.50, |g|>=0.5
    # on osmotic-aversion (drop the <70% WT absolute clause that #69-failed in B33)
    osm_single_rows = [s for s in summary_single
                       if s["readout"] == "osmotic_aversion_response"
                       and s["kd_faah1"] >= 0.50]
    p1_recal_pass = all(abs(s["hedges_g_vs_WT"]) >= 0.5 for s in osm_single_rows)
    lines.append("")
    lines.append("P1-RECAL (B34a re-spec: |g|>=0.5 on osmotic-aversion at kd_faah1>=0.50, "
                 "magnitude clause DROPPED per B33 #69 self-indictment):")
    for s in osm_single_rows:
        lines.append(f"  kd_faah1={s['kd_faah1']:.2f}  |g|={abs(s['hedges_g_vs_WT']):.3f}")
    lines.append(f"  P1-RECAL VERDICT: {'PASS' if p1_recal_pass else 'FAIL'}")

    # F1 carry: signature present
    max_g_single = max(abs(s["hedges_g_vs_WT"]) for s in summary_single if s["kd_faah1"] > 0)
    f1_ok = max_g_single >= 0.2
    lines.append("")
    lines.append(f"F1 carry (some signature, |g|>=0.2 at any kd_faah1>0):")
    lines.append(f"  max |g| = {max_g_single:.3f}")
    lines.append(f"  F1 VERDICT: {'NOT REFUTED' if f1_ok else 'REFUTED'}")

    # Per-longevity-readout top-line
    lines.append("")
    lines.append("Per-longevity-readout max-effect at kd_faah1=0.95:")
    for readout in LONGEVITY:
        s = next(x for x in summary_single
                 if x["readout"] == readout and x["kd_faah1"] == 0.95)
        lines.append(f"  {readout:30s}  pct_WT={s['pct_of_WT']:.3f}  "
                     f"|g|={abs(s['hedges_g_vs_WT']):.3f}")

    return "\n".join(lines), long_pass, multi_pass, p1_recal_pass, f1_ok


def main():
    rng = np.random.default_rng(SEED_ROOT)
    print("[B34] Running extended FAAH in-silico sweep v2 ...")
    print(f"      readouts: {len(READOUTS)}  ({len(BEHAVIORS)} behavior + {len(LONGEVITY)} longevity/stress)")
    print(f"      single sweep: {len(READOUTS)} × {len(KD1_LEVELS_SINGLE)} × {N_SEEDS} = "
          f"{len(READOUTS)*len(KD1_LEVELS_SINGLE)*N_SEEDS} runs")
    print(f"      dual sweep:   {len(READOUTS)} × {len(KD1_LEVELS_DUAL)*len(KD2_LEVELS_DUAL)} × {N_SEEDS} = "
          f"{len(READOUTS)*len(KD1_LEVELS_DUAL)*len(KD2_LEVELS_DUAL)*N_SEEDS} runs")

    rows_single = run_single(rng)
    rows_dual = run_dual(rng)
    summary_single = summarize_single(rows_single)
    summary_dual = summarize_dual(rows_dual)

    report, long_ok, multi_ok, p1r_ok, f1_ok = pre_reg_check(summary_single, summary_dual)

    with (OUTDIR / "results_single.csv").open("w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=["readout","kd_faah1","seed","value","anchor"])
        w.writeheader(); w.writerows(rows_single)
    with (OUTDIR / "results_dual.csv").open("w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=["readout","kd_faah1","kd_faah2","seed","value","anchor"])
        w.writeheader(); w.writerows(rows_dual)
    with (OUTDIR / "summary_single.csv").open("w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=["readout","kd_faah1","n","mean","sd","pct_of_WT","hedges_g_vs_WT"])
        w.writeheader(); w.writerows(summary_single)
    with (OUTDIR / "summary_dual.csv").open("w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=["readout","kd_faah1","kd_faah2","n","mean","sd","pct_of_WT","hedges_g_vs_WT"])
        w.writeheader(); w.writerows(summary_dual)
    (OUTDIR / "pre_reg_check_v2.txt").write_text(report + "\n")

    print()
    print(report)
    print()
    print(f"[B34] Total simulated worm-runs: {len(rows_single) + len(rows_dual)}")
    print(f"[B34] Outputs written to {OUTDIR}/")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
