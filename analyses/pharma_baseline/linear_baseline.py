"""
F-1 Linear-Baseline Computation for TI Sigma Pharma Validation
==============================================================

Per Brandon's Pass-5 ruling (May 8 2026, Decision 2 = Option A):
compute an honest linear baseline against the 12-experiment
validation set in pharma_simulator_validation_report.md and
report the actual margin TI Sigma achieves over it.

Per #69, also report the trivial floor baselines:
- Random-direction baseline (50% directional)
- Majority-class baseline (100% directional, BECAUSE all 12 empirical
  effects in this validation set happen to be positive)
- Mean-magnitude baseline (no fitting; predict mean effect for every exp)
- Median-magnitude baseline (no fitting; predict median effect for every exp)
- Stack-size linear regression (1 feature; leave-one-out CV)
"""

import statistics

# Per pharma_simulator_validation_report.md, the 12 experiments + TI predictions
# ti_pred and empirical are in % of baseline change form.
EXPERIMENTS = [
    # (id, empirical_pct, ti_predicted_pct, n_stack_ingredients)
    ("E01", 62.0, 38.3, 1),   # URB597 -> curcubrain
    ("E02", 57.0, 104.7, 2),  # FAAH-KO -> curcubrain + macamides
    ("E03", 45.0, 8.7,   2),  # BLA anandamide -> curcubrain + cbd
    ("E04", 35.0, 73.8,  3),  # PF-04457845 -> curcubrain + cbd + omega3
    ("E05", 100.0, 134.3, 5), # Jo Cameron -> full FAAH stack
    ("E06", 62.0, 36.7,  1),  # Saffron
    ("E07", 62.6, 50.0,  2),  # 5-HTP + B6
    ("E08", 21.0, 27.3,  1),  # Mood probiotic
    ("E09", 27.0, 15.1,  1),  # Omega3
    ("E10", 23.0, 19.0,  2),  # L-methylfolate + B6
    ("E11", 12.0, 40.0,  2),  # PQQ + CoQ10
    ("E12", 50.0, 45.4,  2),  # Ketamine + lithium
]

def within_2x(predicted: float, empirical: float) -> bool:
    if empirical == 0:
        return predicted == 0
    ratio = predicted / empirical
    return 0.5 <= ratio <= 2.0

def magnitude_accuracy(predictions, empiricals):
    hits = sum(1 for p, e in zip(predictions, empiricals) if within_2x(p, e))
    return hits, len(predictions), hits / len(predictions)

def directional_accuracy(predictions, empiricals):
    hits = sum(1 for p, e in zip(predictions, empiricals) if (p > 0) == (e > 0))
    return hits, len(predictions), hits / len(predictions)

empiricals  = [e[1] for e in EXPERIMENTS]
ti_preds    = [e[2] for e in EXPERIMENTS]
stack_sizes = [e[3] for e in EXPERIMENTS]
n_pos = sum(1 for x in empiricals if x > 0)

print("=" * 76)
print("F-1 Linear-Baseline Computation (Pass 6, May 8 2026)")
print("Validation set: 12 experiments from pharma_simulator_validation_report.md")
print("=" * 76)
print(f"  N experiments      : {len(empiricals)}")
print(f"  Empirical mean     : {statistics.mean(empiricals):.2f}%")
print(f"  Empirical median   : {statistics.median(empiricals):.2f}%")
print(f"  Empirical stdev    : {statistics.stdev(empiricals):.2f}%")
print(f"  Empirical range    : [{min(empiricals):.1f}, {max(empiricals):.1f}]%")
print(f"  Positive-direction : {n_pos}/{len(empiricals)} (100% if all positive)")
print("-" * 76)

print("\n## TI Sigma simulator (the thing being tested)")
ti_mag_h, ti_mag_n, ti_mag_a = magnitude_accuracy(ti_preds, empiricals)
ti_dir_h, ti_dir_n, ti_dir_a = directional_accuracy(ti_preds, empiricals)
print(f"  Directional : {ti_dir_h}/{ti_dir_n} = {ti_dir_a*100:.1f}%")
print(f"  Magnitude (within 2x) : {ti_mag_h}/{ti_mag_n} = {ti_mag_a*100:.1f}%")
print(f"  Mean TI/empirical ratio : {statistics.mean(p/e for p, e in zip(ti_preds, empiricals)):.3f}")

print("\n## Baseline 1: Random-direction (coin flip)")
print(f"  Directional (expected) : 50% (analytic)")
print(f"  Magnitude              : N/A (random sign + mean magnitude => ~33%)")

print("\n## Baseline 2: Majority-class (always predict +)")
maj_dir_h = n_pos
print(f"  Directional : {maj_dir_h}/{len(empiricals)} = {maj_dir_h/len(empiricals)*100:.1f}%")
print(f"  *** NOTE: this dataset has 100% positive effects (selection bias toward")
print(f"      improvement-from-treatment outcomes). TI Sigma's 100% directional ties")
print(f"      this trivial floor on this validation set. ***")

print("\n## Baseline 3: Mean-magnitude (predict mean effect for every experiment)")
mean_pred = statistics.mean(empiricals)
mean_preds = [mean_pred] * len(empiricals)
b3_mag_h, _, b3_mag_a = magnitude_accuracy(mean_preds, empiricals)
print(f"  Predicted: {mean_pred:.2f}% for every experiment")
print(f"  Magnitude (within 2x) : {b3_mag_h}/{len(empiricals)} = {b3_mag_a*100:.1f}%")

print("\n## Baseline 4: Median-magnitude (predict median for every experiment)")
median_pred = statistics.median(empiricals)
median_preds = [median_pred] * len(empiricals)
b4_mag_h, _, b4_mag_a = magnitude_accuracy(median_preds, empiricals)
print(f"  Predicted: {median_pred:.2f}% for every experiment")
print(f"  Magnitude (within 2x) : {b4_mag_h}/{len(empiricals)} = {b4_mag_a*100:.1f}%")

print("\n## Baseline 5: Linear regression on stack-size (1 feature)")
print("  Hypothesis: more ingredients -> bigger effect")
print("  Method: leave-one-out CV; for each held-out experiment, fit OLS on")
print("          the other 11 experiments and predict the held-out one.")
def ols_1d(xs, ys):
    n = len(xs); xm = sum(xs)/n; ym = sum(ys)/n
    sxx = sum((x-xm)**2 for x in xs)
    sxy = sum((x-xm)*(y-ym) for x, y in zip(xs, ys))
    slope = sxy / sxx if sxx else 0.0
    intercept = ym - slope * xm
    return slope, intercept

loo_preds = []
for i in range(len(EXPERIMENTS)):
    xs = [stack_sizes[j] for j in range(len(EXPERIMENTS)) if j != i]
    ys = [empiricals[j]  for j in range(len(EXPERIMENTS)) if j != i]
    slope, intercept = ols_1d(xs, ys)
    loo_preds.append(slope * stack_sizes[i] + intercept)
b5_mag_h, _, b5_mag_a = magnitude_accuracy(loo_preds, empiricals)
b5_dir_h, _, b5_dir_a = directional_accuracy(loo_preds, empiricals)
slope_full, intercept_full = ols_1d(stack_sizes, empiricals)
print(f"  Full-data fit: effect = {slope_full:.2f} * stack_size + {intercept_full:.2f}")
print(f"  LOO Directional : {b5_dir_h}/{len(empiricals)} = {b5_dir_a*100:.1f}%")
print(f"  LOO Magnitude (within 2x) : {b5_mag_h}/{len(empiricals)} = {b5_mag_a*100:.1f}%")

print("-" * 76)
print("\n## SUMMARY TABLE")
print(f"{'Method':<45} {'Dir %':>8} {'Mag %':>8}")
print("-" * 65)
print(f"{'TI Sigma simulator (the framework)':<45} {ti_dir_a*100:>7.1f}% {ti_mag_a*100:>7.1f}%")
print(f"{'Random direction (coin flip)':<45} {'50.0%':>8} {'~33%':>8}")
print(f"{'Majority class (always +)':<45} {maj_dir_h/len(empiricals)*100:>7.1f}% {'N/A':>8}")
print(f"{'Mean-magnitude baseline':<45} {'100.0%':>8} {b3_mag_a*100:>7.1f}%")
print(f"{'Median-magnitude baseline':<45} {'100.0%':>8} {b4_mag_a*100:>7.1f}%")
print(f"{'Linear regression on stack-size (LOO)':<45} {b5_dir_a*100:>7.1f}% {b5_mag_a*100:>7.1f}%")
print("-" * 65)
print(f"\n## TI MARGIN OVER BASELINES (magnitude accuracy)")
print(f"  vs Mean-magnitude baseline    : {(ti_mag_a - b3_mag_a)*100:+.1f} pp")
print(f"  vs Median-magnitude baseline  : {(ti_mag_a - b4_mag_a)*100:+.1f} pp")
print(f"  vs Linear-regression baseline : {(ti_mag_a - b5_mag_a)*100:+.1f} pp")
print(f"\n## #69 HONEST CALL")
print(f"  The book claims '82% accuracy vs ~46% for linear models' (a +35 pp margin).")
print(f"  ACTUAL (Pass 6, this analysis):")
print(f"    - TI Sigma magnitude accuracy = {ti_mag_a*100:.1f}%")
print(f"    - Best honest baseline (mean-magnitude) = {b3_mag_a*100:.1f}%")
print(f"    - Actual margin = +{(ti_mag_a - b3_mag_a)*100:.1f} pp (NOT +35 pp)")
print(f"  The '46%' figure in the book is not reproduced by ANY simple baseline I tried.")
print(f"  Brandon should EITHER:")
print(f"    (a) tell me what specific 'linear model' was originally used to get 46%; OR")
print(f"    (b) revise the body to report the honest +{(ti_mag_a - b3_mag_a)*100:.0f} pp margin.")
print(f"  Direction is a tied 100% across all non-random baselines because all 12")
print(f"  empirical effects are positive (selection bias in this hand-curated set).")
print("=" * 76)
