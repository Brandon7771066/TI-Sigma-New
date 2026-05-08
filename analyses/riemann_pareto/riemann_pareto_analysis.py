"""
Riemann Zero Gap Pareto Analysis (TI Sigma Sacred Interval Validation)
=======================================================================

Tests the TI Sigma framework's prediction that the gap distribution
of the non-trivial zeros of the Riemann zeta function exhibits a
Pareto-style 80/20 concentration: the densest 20% of the gap-bin
support contains approximately 80% of the gap mass.

Methodology
-----------
1. Compute the imaginary parts of the first N non-trivial zeros of
   zeta(s) using mpmath.zetazero (Andrew Odlyzko's tables would be
   used for N >> 10000; here we use mpmath for in-session
   reproducibility).
2. Compute consecutive gaps g_k = t_{k+1} - t_k.
3. Normalize each gap by its local mean spacing (Montgomery-Odlyzko
   normalization): g_k_normalized = g_k * log(t_k / (2*pi)) / (2*pi).
4. Build a histogram of normalized gaps with B equal-width bins
   over [0, max_normalized_gap].
5. Sort the bins by mass (descending). Compute the cumulative-mass
   curve. Report the smallest fraction of bins whose cumulative
   mass first crosses 0.80.
6. Report the empirical "80/20 ratio" — the fraction of bins that
   together hold 80% of the mass.

Output
------
Prints a methodology header, the test parameters, the empirical
result, a verdict, and a short caveats section.

Reproduction
------------
$ python analyses/riemann_pareto/riemann_pareto_analysis.py
"""

import math
import time
from mpmath import zetazero, mp

def main(n_zeros: int = 300, n_bins: int = 50):
    mp.dps = 15
    print("=" * 72)
    print("Riemann Zero Gap Pareto Analysis — TI Sigma Sacred Interval Test")
    print("=" * 72)
    print(f"Parameters: N = {n_zeros} zeros, B = {n_bins} bins")
    print(f"Source    : mpmath.zetazero (in-session computation)")
    print(f"Normalize : Montgomery-Odlyzko local-mean normalization")
    print(f"Hypothesis: densest 20% of bins should hold ~80% of gap mass")
    print("-" * 72)

    t0 = time.time()
    t_imag = []
    for k in range(1, n_zeros + 1):
        z = zetazero(k)
        t_imag.append(float(z.imag))
        if k % 50 == 0:
            print(f"  computed zero {k}/{n_zeros} (t = {t_imag[-1]:.4f})")
    print(f"  zero computation time: {time.time() - t0:.1f}s")

    raw_gaps = [t_imag[k+1] - t_imag[k] for k in range(n_zeros - 1)]

    # Montgomery-Odlyzko normalization: normalized_gap = raw_gap * log(t/(2*pi)) / (2*pi)
    # so that the asymptotic mean spacing is 1.
    norm_gaps = []
    for k, g in enumerate(raw_gaps):
        t_local = t_imag[k]
        norm = g * math.log(t_local / (2 * math.pi)) / (2 * math.pi)
        norm_gaps.append(norm)

    g_max = max(norm_gaps)
    g_min = min(norm_gaps)
    g_mean = sum(norm_gaps) / len(norm_gaps)
    print(f"  normalized-gap range: [{g_min:.4f}, {g_max:.4f}], mean = {g_mean:.4f}")

    # Histogram
    bin_width = g_max / n_bins
    bin_counts = [0] * n_bins
    for ng in norm_gaps:
        idx = min(int(ng / bin_width), n_bins - 1)
        bin_counts[idx] += 1

    total = sum(bin_counts)

    # Sort bins descending by mass; find smallest fraction of bins covering 80%
    sorted_counts = sorted(bin_counts, reverse=True)
    cumulative = 0
    bins_for_80pct = 0
    for i, c in enumerate(sorted_counts):
        cumulative += c
        if cumulative / total >= 0.80:
            bins_for_80pct = i + 1
            break
    fraction_of_bins_for_80pct = bins_for_80pct / n_bins

    print("-" * 72)
    print("RESULT")
    print(f"  Bins needed for 80% of mass : {bins_for_80pct} of {n_bins}")
    print(f"  Fraction of bin-support     : {fraction_of_bins_for_80pct:.3f}")
    print(f"  TI Sigma prediction         : 0.20 (the 80/20 / Pareto target)")
    deviation = abs(fraction_of_bins_for_80pct - 0.20)
    print(f"  Absolute deviation from 0.20: {deviation:.3f}")

    if deviation <= 0.05:
        verdict = "STRONG SUPPORT (within 5 percentage points of 80/20)"
    elif deviation <= 0.10:
        verdict = "MODERATE SUPPORT (within 10 percentage points of 80/20)"
    else:
        verdict = "NOT SUPPORTED at this resolution"
    print(f"  Verdict                     : {verdict}")
    print("-" * 72)
    print("CAVEATS (#69 honesty section)")
    print("  1. N = 1000 is small relative to the original claim of 1M zeros.")
    print("     For asymptotic claims a larger N from Odlyzko or LMFDB is")
    print("     required; the shape result here is a first-pass replication.")
    print("  2. The 'Sacred Interval equivalent' interpreted here as 'top-")
    print("     density 20% of bin-support holds 80% of mass' is one of")
    print("     several reasonable operationalizations; alternative")
    print("     definitions (e.g., density-quantile vs bin-quantile) may")
    print("     give different numbers.")
    print("  3. Bin choice (here B = 50) affects the result; we report a")
    print("     sensitivity check below.")
    print("-" * 72)

    # Sensitivity check across bin counts
    print("BIN-COUNT SENSITIVITY (fraction-of-bins for 80% mass):")
    for B in [20, 30, 50, 80, 120]:
        bw = g_max / B
        bc = [0] * B
        for ng in norm_gaps:
            idx = min(int(ng / bw), B - 1)
            bc[idx] += 1
        sc = sorted(bc, reverse=True)
        cum, k80 = 0, 0
        for i, c in enumerate(sc):
            cum += c
            if cum / total >= 0.80:
                k80 = i + 1
                break
        print(f"  B = {B:4d} : {k80}/{B} bins  =>  fraction = {k80/B:.3f}")
    print("=" * 72)

if __name__ == "__main__":
    main(n_zeros=300, n_bins=50)
