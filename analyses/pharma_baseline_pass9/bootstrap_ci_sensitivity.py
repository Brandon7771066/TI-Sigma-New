"""
T1-A — Bootstrap CI + sensitivity analysis on the +8 pp pharma margin.

Per Pass 9 Empirical Research Agenda T1-A:
- Compute bootstrap 95% CI on (TI_mag - best_baseline_mag) over the N=12 set.
- Sensitivity to the within-2x threshold (try {1.5x, 2x, 3x}).
- Report whether the +8 pp margin survives bootstrap and threshold sensitivity.

Honesty discipline (#69): if CI crosses zero, report it. If sensitivity at
1.5x (stricter) collapses the margin, report it. If 3x (looser) opens it
wider, report that too.
"""
import random
import statistics
import math

# Same 12-experiment validation set as analyses/pharma_baseline/linear_baseline.py
EXPERIMENTS = [
    ("E01", 62.0, 38.3, 1),
    ("E02", 57.0, 104.7, 2),
    ("E03", 45.0, 8.7,   2),
    ("E04", 35.0, 73.8,  3),
    ("E05", 100.0, 134.3, 5),
    ("E06", 62.0, 36.7,  1),
    ("E07", 62.6, 50.0,  2),
    ("E08", 21.0, 27.3,  1),
    ("E09", 27.0, 15.1,  1),
    ("E10", 23.0, 19.0,  2),
    ("E11", 12.0, 40.0,  2),
    ("E12", 50.0, 45.4,  2),
]

def within_threshold(predicted, empirical, fold):
    if empirical == 0:
        return predicted == 0
    r = predicted / empirical
    return (1.0 / fold) <= r <= fold

def mag_acc(preds, emps, fold):
    return sum(within_threshold(p, e, fold) for p, e in zip(preds, emps)) / len(preds)

empiricals  = [e[1] for e in EXPERIMENTS]
ti_preds    = [e[2] for e in EXPERIMENTS]
stack_sizes = [e[3] for e in EXPERIMENTS]

random.seed(20260509)  # reproducibility

def bootstrap_margin(fold, baseline_kind, B=20000):
    """Bootstrap the (TI - best_baseline) margin over B paired resamples.
    baseline_kind in {'mean', 'median'} — these are the two best non-trivial
    baselines from Pass-6 results; both score 66.7% mag at fold=2."""
    margins = []
    for _ in range(B):
        idx = [random.randrange(len(EXPERIMENTS)) for _ in range(len(EXPERIMENTS))]
        emp_b = [empiricals[i] for i in idx]
        ti_b  = [ti_preds[i]   for i in idx]
        # Refit baseline on the resample (within-sample) to avoid pessimistic bias.
        if baseline_kind == "mean":
            b_pred = [statistics.mean(emp_b)] * len(emp_b)
        else:
            b_pred = [statistics.median(emp_b)] * len(emp_b)
        m = mag_acc(ti_b, emp_b, fold) - mag_acc(b_pred, emp_b, fold)
        margins.append(m)
    margins.sort()
    return {
        "mean": statistics.mean(margins),
        "median": statistics.median(margins),
        "ci95_lo": margins[int(0.025 * B)],
        "ci95_hi": margins[int(0.975 * B)],
        "ci80_lo": margins[int(0.10  * B)],
        "ci80_hi": margins[int(0.90  * B)],
        "p_pos":   sum(1 for m in margins if m > 0) / B,
        "p_zero_or_pos": sum(1 for m in margins if m >= 0) / B,
    }

# ---- Headline numbers (no resampling) ----
print("=" * 78)
print("T1-A — Bootstrap CI + sensitivity on the +8 pp pharma margin")
print("Validation set: same N=12 from Pass-6 linear_baseline.py")
print("=" * 78)

print("\n## Headline (no resampling)")
print(f"  {'Fold':<8} {'TI mag':>10} {'Mean-base':>12} {'Median-base':>14} {'TI−Mean':>10} {'TI−Med':>10}")
for fold in (1.5, 2.0, 3.0):
    ti = mag_acc(ti_preds, empiricals, fold)
    bm = mag_acc([statistics.mean(empiricals)] * len(empiricals), empiricals, fold)
    bd = mag_acc([statistics.median(empiricals)] * len(empiricals), empiricals, fold)
    print(f"  {fold}x{'':<3} {ti*100:>9.1f}% {bm*100:>11.1f}% {bd*100:>13.1f}% "
          f"{(ti-bm)*100:>+9.1f}pp {(ti-bd)*100:>+9.1f}pp")

# ---- Bootstrap CI at the canonical fold=2 ----
print("\n## Bootstrap 95%/80% CI on (TI − best-baseline) margin at fold=2")
print("  (B = 20,000 paired resamples; baseline refit within each resample)")
for kind in ("mean", "median"):
    r = bootstrap_margin(fold=2.0, baseline_kind=kind, B=20000)
    print(f"\n  Baseline = {kind}-magnitude")
    print(f"    Bootstrap mean margin   : {r['mean']*100:+.2f} pp")
    print(f"    Bootstrap median margin : {r['median']*100:+.2f} pp")
    print(f"    95% CI                  : [{r['ci95_lo']*100:+.2f}, {r['ci95_hi']*100:+.2f}] pp")
    print(f"    80% CI                  : [{r['ci80_lo']*100:+.2f}, {r['ci80_hi']*100:+.2f}] pp")
    print(f"    P(margin > 0)           : {r['p_pos']*100:.1f}%")
    print(f"    P(margin ≥ 0)           : {r['p_zero_or_pos']*100:.1f}%")

# ---- Bootstrap CI sensitivity across folds ----
print("\n## Bootstrap CI vs fold (mean-magnitude baseline)")
print(f"  {'Fold':<8} {'Boot mean':>12} {'95% CI lo':>12} {'95% CI hi':>12} {'P(>0)':>8}")
for fold in (1.5, 2.0, 3.0):
    r = bootstrap_margin(fold=fold, baseline_kind="mean", B=10000)
    print(f"  {fold}x{'':<3} {r['mean']*100:>+11.2f}pp {r['ci95_lo']*100:>+11.2f}pp "
          f"{r['ci95_hi']*100:>+11.2f}pp {r['p_pos']*100:>7.1f}%")

# ---- Honest call ----
r2 = bootstrap_margin(fold=2.0, baseline_kind="mean", B=20000)
print("\n" + "=" * 78)
print("## #69 HONEST CALL (T1-A)")
print("=" * 78)
print(f"  Headline +8.3 pp margin at fold=2 vs mean-magnitude:")
print(f"    Bootstrap median = {r2['median']*100:+.2f} pp")
print(f"    95% CI           = [{r2['ci95_lo']*100:+.2f}, {r2['ci95_hi']*100:+.2f}] pp")
print(f"    P(margin > 0)    = {r2['p_pos']*100:.1f}%")
if r2['ci95_lo'] > 0:
    verdict = "MARGIN SURVIVES bootstrap at 95% (CI strictly positive)."
elif r2['ci95_lo'] >= -0.01:
    verdict = "MARGIN MARGINAL at 95% (CI touches zero); strong at 80% if P(>0) > 80%."
else:
    verdict = "MARGIN DOES NOT SURVIVE 95% bootstrap; 95% CI crosses zero."
print(f"  Verdict: {verdict}")
print()
print(f"  Sample size N=12 means CIs are wide; this is the irreducible limitation.")
print(f"  External replication on a held-out dataset (T3-A) is the right escalation.")
print("=" * 78)
