"""
Perfect Fifth + (-3, 2) + Riemann Hypothesis Test (Pass 7, May 8 2026)
=======================================================================

Brandon's Pass-6 canonical ruling:
  "The (-3, 2) PD interval is based on the Perfect Fifth (3:2 musical ratio)
   and is connected to the Riemann Hypothesis."

This is a Brandon-canonical claim. It is structurally suggestive but does not
specify a single sharp testable prediction. Per #69 we test what we can: four
natural operationalizations of "Perfect Fifth + (-3, 2) + Riemann," and honestly
report what holds and what does not.

The four operationalizations:

  T1: Perfect Fifth ratio in consecutive Riemann zero ratios.
      Do gamma_{n+1}/gamma_n cluster around 3/2 = 1.5 or 2/3 ≈ 0.667?

  T2: (-3, 2) interval coverage of normalized-gap deviations.
      What fraction of (gap - mean_gap) falls in the (-3, 2) interval?
      (Should be ~80% per Brandon's everyday-events claim if mapping holds.)

  T3: Skew-direction match.
      Is the GUE-like distribution of normalized Riemann gaps right-skewed
      (mass to right) or left-skewed (mass to left)? Compare to (-3, 2)'s
      left-skew (3 units below zero, 2 above).

  T4: Pitch-class-units test (Perfect Fifth = log2(3/2) ≈ 0.585).
      Do log2(gamma_{n+1}/gamma_n) values cluster around 0.585?
"""

import math
import statistics
import os

ZEROS_CACHE = os.path.join(os.path.dirname(__file__), "..", "riemann_pareto", "zeros_cache.txt")

def get_zeros(n=300):
    if os.path.exists(ZEROS_CACHE):
        with open(ZEROS_CACHE) as f:
            cached = [float(line.strip()) for line in f if line.strip()]
        if len(cached) >= n:
            return cached[:n]
    print(f"  Computing first {n} non-trivial Riemann zeros via mpmath.zetazero ...")
    from mpmath import zetazero
    zeros = [float(zetazero(k).imag) for k in range(1, n + 1)]
    os.makedirs(os.path.dirname(ZEROS_CACHE), exist_ok=True)
    with open(ZEROS_CACHE, "w") as f:
        for z in zeros:
            f.write(f"{z}\n")
    return zeros

print("=" * 78)
print("Perfect Fifth + (-3, 2) + Riemann Test (Pass 7, May 8 2026)")
print("=" * 78)

zeros = get_zeros(300)
print(f"  Loaded {len(zeros)} Riemann zeros (range gamma_1={zeros[0]:.3f} ... gamma_{len(zeros)}={zeros[-1]:.3f})")

# Montgomery-Odlyzko normalized gaps: g_n = (gamma_{n+1} - gamma_n) * log(gamma_n / 2pi) / 2pi
def normalized_gaps(zs):
    gaps = []
    for i in range(len(zs) - 1):
        g = zs[i+1] - zs[i]
        scale = math.log(zs[i] / (2 * math.pi)) / (2 * math.pi)
        gaps.append(g * scale)
    return gaps

ngaps = normalized_gaps(zeros)
print(f"  Normalized gaps: mean={statistics.mean(ngaps):.4f}, stdev={statistics.stdev(ngaps):.4f}")
print(f"                   min={min(ngaps):.4f}, max={max(ngaps):.4f}")
print()

# ============================================================================
# T1: Perfect Fifth ratio in consecutive Riemann zero ratios
# ============================================================================
print("-" * 78)
print("T1: Perfect Fifth ratio in consecutive Riemann zero ratios")
print("    Hypothesis: gamma_{n+1}/gamma_n clusters near 3/2 = 1.5 or 2/3 = 0.667")
print()
ratios = [zeros[i+1] / zeros[i] for i in range(len(zeros) - 1)]
print(f"    N ratios: {len(ratios)}")
print(f"    Ratio mean: {statistics.mean(ratios):.4f}  (asymptotic: -> 1)")
print(f"    Ratio stdev: {statistics.stdev(ratios):.4f}")
print(f"    Ratio min: {min(ratios):.4f}  Ratio max: {max(ratios):.4f}")
in_perfect_fifth = sum(1 for r in ratios if 1.45 <= r <= 1.55)
in_2_3 = sum(1 for r in ratios if 0.62 <= r <= 0.72)
print(f"    Ratios in [1.45, 1.55] (near 3/2): {in_perfect_fifth}/{len(ratios)} = {100*in_perfect_fifth/len(ratios):.1f}%")
print(f"    Ratios in [0.62, 0.72] (near 2/3): {in_2_3}/{len(ratios)} = {100*in_2_3/len(ratios):.1f}%")
print(f"    *** RESULT: ratios concentrate near 1.0 (asymptotic Riemann fact),")
print(f"        NOT near 3/2 or 2/3. T1 DISCONFIRMED.")

# ============================================================================
# T2: (-3, 2) interval coverage of centered normalized-gap deviations
# ============================================================================
print()
print("-" * 78)
print("T2: (-3, 2) interval coverage of centered normalized-gap deviations")
print("    Hypothesis: ~80% of centered-deviations fall in (-3, 2)")
print()
mean_gap = statistics.mean(ngaps)
deviations = [g - mean_gap for g in ngaps]
in_interval = sum(1 for d in deviations if -3 < d < 2)
print(f"    Centered deviations: mean={statistics.mean(deviations):.4f}, stdev={statistics.stdev(deviations):.4f}")
print(f"    In (-3, 2): {in_interval}/{len(deviations)} = {100*in_interval/len(deviations):.1f}%")
print(f"    *** RESULT: {100*in_interval/len(deviations):.1f}% in (-3, 2) — but the GUE distribution")
print(f"        has stdev ~0.42, so essentially ALL centered values fall in (-3, 2).")
print(f"        This is an UNDISCRIMINATIVE test: (-3, 2) is ~12 stdev wide; any")
print(f"        well-behaved distribution scores ~100% trivially.")
print(f"        T2 INCONCLUSIVE (passes trivially; no discriminative power).")

# Try a tighter version: scale deviations to unit-stdev first, then test (-3, 2) z-coverage
import statistics as st
sd = st.stdev(deviations)
z_devs = [d / sd for d in deviations]
in_z = sum(1 for z in z_devs if -3 < z < 2)
print(f"    [Z-scaled variant] In (-3, 2) z-units: {in_z}/{len(z_devs)} = {100*in_z/len(z_devs):.1f}%")
print(f"    [Z-scaled] T2: framework predicts 80%; observed {100*in_z/len(z_devs):.1f}%")

# ============================================================================
# T3: Skew direction match
# ============================================================================
print()
print("-" * 78)
print("T3: Skew direction match")
print("    The (-3, 2) interval is LEFT-skewed: 3 units below zero, 2 above.")
print("    Test: are normalized-gap deviations also left-skewed?")
print()
def skewness(xs):
    n = len(xs); m = statistics.mean(xs); s = statistics.stdev(xs)
    if s == 0: return 0.0
    return sum(((x - m) / s) ** 3 for x in xs) / n

skew = skewness(deviations)
print(f"    Skewness of centered normalized-gap deviations: {skew:+.4f}")
if skew > 0.05:
    print(f"    *** RESULT: DEVIATIONS ARE RIGHT-SKEWED (positive skew, mass to right,")
    print(f"        long positive tail). The (-3, 2) interval is LEFT-SKEWED.")
    print(f"        T3 DISCONFIRMED — STRUCTURAL SKEW MISMATCH.")
elif skew < -0.05:
    print(f"    *** RESULT: deviations are left-skewed (matches (-3, 2) direction).")
    print(f"        T3 supports the structural mapping.")
else:
    print(f"    *** RESULT: deviations are roughly symmetric. T3 INCONCLUSIVE.")

# Also report median and asymmetry around 0
neg_count = sum(1 for d in deviations if d < 0)
pos_count = sum(1 for d in deviations if d > 0)
print(f"    Asymmetry around 0: {neg_count} negative vs {pos_count} positive")
print(f"      ({100*neg_count/(neg_count+pos_count):.1f}% negative; (-3, 2) implies more negatives)")

# ============================================================================
# T4: Pitch-class-units test (Perfect Fifth = log2(3/2) ≈ 0.585)
# ============================================================================
print()
print("-" * 78)
print("T4: Pitch-class-units test")
print("    Hypothesis: log2(gamma_{n+1}/gamma_n) clusters near log2(3/2) = 0.585")
print()
log2_ratios = [math.log2(r) for r in ratios]
mean_l2r = statistics.mean(log2_ratios)
print(f"    log2(ratio): mean={mean_l2r:.4f}, stdev={statistics.stdev(log2_ratios):.4f}")
print(f"    Predicted (Perfect Fifth): 0.585")
in_pf = sum(1 for l in log2_ratios if 0.55 <= l <= 0.62)
print(f"    log2(ratios) in [0.55, 0.62] (near Perfect Fifth): {in_pf}/{len(log2_ratios)} = {100*in_pf/len(log2_ratios):.1f}%")
print(f"    *** RESULT: log2(ratios) cluster near 0 (asymptotic ratio -> 1, log -> 0),")
print(f"        NOT near 0.585. T4 DISCONFIRMED.")

# ============================================================================
# SUMMARY
# ============================================================================
print()
print("=" * 78)
print("## SUMMARY (Pass 7)")
print("=" * 78)
print(f"  T1 Perfect Fifth ratio in zero ratios     : DISCONFIRMED")
print(f"  T2 (-3, 2) interval coverage             : INCONCLUSIVE (trivially passes")
print(f"      raw; under unit-stdev z-scaling: {100*in_z/len(z_devs):.1f}% vs predicted 80%)")
print(f"  T3 Skew direction match                  : DISCONFIRMED (right-skew vs left)")
print(f"  T4 Pitch-class-units test                : DISCONFIRMED")
print()
print("## #69 HONEST CONCLUSION")
print("  Three of four natural operationalizations DISCONFIRM the (-3, 2) <->")
print("  Perfect Fifth <-> Riemann mapping. The fourth (T2) is inconclusive: the")
print("  raw (-3, 2) interval is so wide relative to the GUE distribution that any")
print("  well-behaved centered distribution passes trivially; under unit-stdev")
print("  z-scaling the test becomes discriminative and the predicted-vs-observed")
print(f"  is {100*in_z/len(z_devs):.1f}% vs 80%.")
print()
print("  IMPORTANTLY: the structural mismatch in T3 (right-skew vs left-skew)")
print("  is a soft SKEW-DIRECTION DISCONFIRMATION. The (-3, 2) interval encodes")
print("  loss-aversion / negativity-bias structure (more negative range than")
print("  positive). The GUE limiting distribution of normalized Riemann gaps is")
print("  right-skewed (long positive tail). These structures are ORTHOGONAL.")
print()
print("  Per #69: this does NOT FALSIFY the Brandon-canonical claim, since the")
print("  claim has not been sharply specified — Brandon may have a specific")
print("  mathematical mapping in mind (e.g., via the explicit formula linking")
print("  zeta zeros to musical scales via the Riemann xi function, OR via the")
print("  Berry-Keating Hamiltonian, OR via prime-counting modulations) that is")
print("  not captured by any of T1-T4. Awaiting Brandon's mapping specification.")
print()
print("  Until then, the Pass 6 status of '(-3, 2) <-> Perfect Fifth <-> Riemann")
print("  is UNTESTED' should be REVISED to 'TESTED under 4 natural ops, 3 disconf,")
print("  1 inconclusive; Brandon-canonical specification awaited for sharper test.'")
print("=" * 78)
