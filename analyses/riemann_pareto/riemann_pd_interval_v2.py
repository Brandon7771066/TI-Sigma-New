"""
Riemann Zero Gap — Indeterminate PD Range Membership Test (v2)
==============================================================

Tests Brandon's CLARIFIED operationalization of the Sacred Interval
claim (renamed Pass 4): the "Sacred Interval" is the Indeterminate
Range of the Permissibility Distribution = (-0.666, 0.333). The
prediction is that ~20% of EVENTS fall in this interval, because
events in the Indeterminate Range are "neither positive nor negative"
(close to zero on the PD axis).

For Riemann zero gaps, we map the normalized-gap deviations to a
PD-style axis using three different normalization schemes, and report
the fraction landing in (-0.666, 0.333) for each, plus sensitivity.
"""

import math
import time
from mpmath import zetazero, mp

LO, HI = -0.666, 0.333  # The Indeterminate PD Range

def fraction_in_interval(values, lo=LO, hi=HI):
    return sum(1 for v in values if lo < v < hi) / len(values)

def main(n_zeros: int = 300):
    mp.dps = 15
    print("=" * 76)
    print("Riemann Gap — Indeterminate PD Range Membership Test (v2)")
    print("Operationalization per Brandon, May 8 2026 (Pass 4 directive)")
    print("=" * 76)
    print(f"Indeterminate PD Range : ({LO}, {HI})  [width {HI-LO:.3f}]")
    print(f"Prediction             : ~20% of events fall in this range")
    print(f"Sample                 : first {n_zeros} non-trivial zeros via mpmath")
    print("-" * 76)

    t0 = time.time()
    t_imag = []
    for k in range(1, n_zeros + 1):
        t_imag.append(float(zetazero(k).imag))
    print(f"  zero computation: {time.time()-t0:.1f}s")

    raw_gaps = [t_imag[k+1] - t_imag[k] for k in range(n_zeros - 1)]
    norm_gaps = [g * math.log(t_imag[k] / (2 * math.pi)) / (2 * math.pi)
                 for k, g in enumerate(raw_gaps)]

    deviations = [g - 1.0 for g in norm_gaps]
    max_abs = max(abs(d) for d in deviations)
    std_dev = (sum(d*d for d in deviations) / len(deviations)) ** 0.5
    mean_dev = sum(deviations) / len(deviations)

    print(f"  N usable gaps   : {len(deviations)}")
    print(f"  Deviation mean  : {mean_dev:+.4f}")
    print(f"  Deviation std   : {std_dev:.4f}")
    print(f"  Deviation range : [{min(deviations):+.4f}, {max(deviations):+.4f}]")
    print("-" * 76)

    print("OPERATIONALIZATION 1: Raw deviations (no rescaling)")
    print("  Map: d = g_norm - 1, test fraction in (-0.666, 0.333)")
    f1 = fraction_in_interval(deviations)
    print(f"  RESULT: {f1*100:.1f}% in interval  (predicted: 20%)  "
          f"deviation: {abs(f1-0.20)*100:+.1f} pp")

    print("\nOPERATIONALIZATION 2: Max-abs rescaled to PD-axis")
    print("  Map: d_scaled = (g_norm - 1) / max|d|, test fraction in (-0.666, 0.333)")
    rescaled_max = [d / max_abs for d in deviations]
    f2 = fraction_in_interval(rescaled_max)
    print(f"  RESULT: {f2*100:.1f}% in interval  (predicted: 20%)  "
          f"deviation: {abs(f2-0.20)*100:+.1f} pp")

    print("\nOPERATIONALIZATION 3: Std-rescaled (z-score-style)")
    print("  Map: d_scaled = (g_norm - 1) / std(d), test fraction in (-0.666, 0.333)")
    rescaled_std = [d / std_dev for d in deviations]
    f3 = fraction_in_interval(rescaled_std)
    print(f"  RESULT: {f3*100:.1f}% in interval  (predicted: 20%)  "
          f"deviation: {abs(f3-0.20)*100:+.1f} pp")

    print("\nOPERATIONALIZATION 4: Centered raw gap on (0, 2*mean) axis -> rescaled to [-1,+1]")
    print("  Map: d_scaled = 2*(g_norm - 1) / max(g_norm), "
          "test fraction in (-0.666, 0.333)")
    g_max = max(norm_gaps)
    rescaled_g = [2.0 * (g - 1.0) / g_max for g in norm_gaps]
    f4 = fraction_in_interval(rescaled_g)
    print(f"  RESULT: {f4*100:.1f}% in interval  (predicted: 20%)  "
          f"deviation: {abs(f4-0.20)*100:+.1f} pp")

    print("-" * 76)
    print("VERDICT BLOCK (per #69 brutal-honesty discipline)")
    results = [("raw deviations", f1), ("max-abs rescaled", f2),
               ("std rescaled", f3), ("centered+rescaled", f4)]
    closest = min(results, key=lambda r: abs(r[1] - 0.20))
    farthest = max(results, key=lambda r: abs(r[1] - 0.20))
    print(f"  Closest to 20%   : {closest[0]} -> {closest[1]*100:.1f}% "
          f"(deviation {abs(closest[1]-0.20)*100:+.1f} pp)")
    print(f"  Farthest from 20%: {farthest[0]} -> {farthest[1]*100:.1f}% "
          f"(deviation {abs(farthest[1]-0.20)*100:+.1f} pp)")

    if any(abs(r[1] - 0.20) <= 0.05 for r in results):
        print(f"  CONCLUSION: AT LEAST ONE operationalization SUPPORTS the 20% claim "
              f"within +/- 5pp.")
    elif any(abs(r[1] - 0.20) <= 0.10 for r in results):
        print(f"  CONCLUSION: AT LEAST ONE operationalization SUPPORTS the 20% claim "
              f"within +/- 10pp (moderate support).")
    else:
        print(f"  CONCLUSION: NO operationalization supports the 20% claim within "
              f"+/- 10pp. All four readings disconfirm.")
    print("-" * 76)

    print("CONTEXT: fraction in OTHER intervals (sanity checks)")
    print(f"  Raw deviations in (-0.5, +0.5)   : {fraction_in_interval(deviations, -0.5, 0.5)*100:.1f}%")
    print(f"  Raw deviations in (-0.333, +0.333): {fraction_in_interval(deviations, -0.333, 0.333)*100:.1f}%")
    print(f"  Std rescaled in (-1, +1)         : {fraction_in_interval(rescaled_std, -1, 1)*100:.1f}%  [Gauss expectation: 68%]")
    print("=" * 76)

if __name__ == "__main__":
    main(n_zeros=300)
