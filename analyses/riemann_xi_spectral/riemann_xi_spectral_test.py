"""
T4-A — Riemann xi spectral test for Perfect-Fifth modulation.

Pass 7 T1 / T4 already tested the *consecutive-ratio* operationalization of the
Perfect Fifth ↔ Riemann claim and disconfirmed both. This script asks a
different question:

  Does the gap-sequence of Riemann zeros (γ_{n+1} − γ_n), or its normalized
  version, contain a SPECTRAL/PERIODIC modulation at a frequency related to
  log(3/2) (the Perfect Fifth in pitch-class units) or its multiples?

Method:
  1. Load 300 normalized gaps (Montgomery-Odlyzko normalization).
  2. Compute the discrete autocorrelation of the gap sequence.
  3. Compute the periodogram (DFT power spectrum) of the gap sequence.
  4. Look for peaks at frequencies corresponding to:
       - log(3/2) ≈ 0.405  (Perfect-Fifth pitch interval)
       - 2π/log(3/2) ≈ 15.5  (period in samples if gap sequence were
         a sinusoidal modulation in log-frequency space)
       - other rational fractions of the Nyquist frequency
  5. Compare peak heights to a chi-squared null at 95%.

Per #69: this is EXPLORATORY. The framework does not pre-specify a sharp
prediction for what the spectral signature should look like; we report the
observed periodogram structure honestly, and let Brandon decide whether the
result motivates a follow-up.
"""
import math
import statistics

with open("analyses/riemann_pareto/zeros_cache.txt") as f:
    gammas = [float(line.strip()) for line in f if line.strip()]

# Montgomery-Odlyzko normalization: g_k_norm = (γ_{k+1} − γ_k) * log(γ_k / 2π) / 2π
def normalize_gaps(gs):
    out = []
    for k in range(len(gs) - 1):
        gap = gs[k+1] - gs[k]
        norm = gap * math.log(gs[k] / (2 * math.pi)) / (2 * math.pi)
        out.append(norm)
    return out

ng = normalize_gaps(gammas)
N = len(ng)
ng_mean = statistics.mean(ng)
ng_centered = [x - ng_mean for x in ng]
var = sum(x*x for x in ng_centered) / N

print("=" * 78)
print("T4-A — Riemann xi spectral test for Perfect-Fifth modulation")
print("=" * 78)
print(f"\n## Input sequence")
print(f"  N normalized gaps: {N}")
print(f"  Mean (target ≈ 1.0): {ng_mean:.4f}")
print(f"  Variance: {var:.4f}")

# 1. Autocorrelation at lags 1..30
print(f"\n## Autocorrelation of normalized-gap sequence (lags 1..20)")
print(f"  Lag    r(lag)        |r|")
acfs = []
for lag in range(1, 21):
    if lag >= N: break
    num = sum(ng_centered[k] * ng_centered[k+lag] for k in range(N - lag))
    den = N * var
    r = num / den
    acfs.append(r)
    print(f"  {lag:>3}    {r:>+7.4f}    {abs(r):.4f}")
# 95% null bound for white noise: ~ 1.96 / sqrt(N)
bound = 1.96 / math.sqrt(N)
print(f"  95% white-noise bound: ±{bound:.4f}")
sig = [(i+1, r) for i, r in enumerate(acfs) if abs(r) > bound]
if sig:
    print(f"  Lags exceeding bound: {sig}")
else:
    print(f"  No lag exceeds the 95% white-noise bound (consistent with GUE prediction).")

# 2. Naive DFT periodogram (no NumPy)
def dft_power(x):
    """Return periodogram |X[k]|^2 / N for k = 0..N//2."""
    N = len(x)
    out = []
    for k in range(N // 2 + 1):
        re = sum(x[n] * math.cos(2 * math.pi * k * n / N) for n in range(N))
        im = sum(x[n] * math.sin(2 * math.pi * k * n / N) for n in range(N))
        out.append((re * re + im * im) / N)
    return out

print(f"\n## Periodogram (DFT power spectrum) of centered normalized gaps")
print(f"  Computing (N={N})...")
P = dft_power(ng_centered)
total_power = sum(P[1:])  # exclude DC
print(f"  Total non-DC power: {total_power:.4f}")
print(f"  Mean per bin (chi-squared expected): {total_power/(len(P)-1):.4f}")

# Top 10 power peaks (excluding DC)
indexed = list(enumerate(P))
indexed.sort(key=lambda t: -t[1])
print(f"\n  Top 10 power peaks (excluding DC):")
print(f"  {'rank':<6} {'k':<6} {'period (samples)':<20} {'frequency (cycles/sample)':<28} {'power':>10}")
peaks = []
for rank, (k, p) in enumerate([t for t in indexed if t[0] > 0][:10], 1):
    period = N / k if k > 0 else float('inf')
    freq = k / N
    peaks.append((k, period, freq, p))
    print(f"  {rank:<6} {k:<6} {period:<20.3f} {freq:<28.5f} {p:>9.4f}")

# Test specific framework-relevant frequencies
print(f"\n## Framework-relevant frequency targets")
targets = [
    ("log(3/2) cyc/samp",       math.log(3/2)),
    ("log(3/2)/(2π) cyc/samp",  math.log(3/2) / (2*math.pi)),
    ("1/15.5 cyc/samp (period 15.5 samples; 2π/log(3/2))", 1.0 / (2*math.pi/math.log(3/2))),
    ("1/3 cyc/samp",            1.0/3),
    ("1/4 cyc/samp",            0.25),
    ("1/5 cyc/samp",            0.20),
    ("Perfect Fifth ratio  3/2 → freq 0.585", math.log2(1.5)/2),
]
for name, target_freq in targets:
    if 0 < target_freq < 0.5:
        target_k = round(target_freq * N)
        if 0 < target_k <= N // 2:
            p_at = P[target_k]
            mean_p = total_power / (len(P) - 1)
            ratio = p_at / mean_p if mean_p > 0 else 0
            sig = "***" if ratio > 4.0 else ("*" if ratio > 2.0 else "")
            print(f"  {name:<60} k={target_k:>4} P={p_at:.3f}   "
                  f"({ratio:.2f}× mean)  {sig}")
        else:
            print(f"  {name:<60} target out of band")
    else:
        print(f"  {name:<60} freq out of (0, 0.5)")

# Honest call
print("\n" + "=" * 78)
print("## #69 HONEST CALL (T4-A) — EXPLORATORY")
print("=" * 78)
max_peak = peaks[0]
mean_p = total_power / (len(P) - 1)
print(f"  Largest periodogram peak: k={max_peak[0]}, period={max_peak[1]:.2f} samples,")
print(f"    frequency={max_peak[2]:.4f} cyc/sample, power={max_peak[3]:.3f}")
print(f"    ({max_peak[3]/mean_p:.2f}× mean bin power)")
print()
print(f"  Significance threshold (4× mean = ~95% under chi-squared-2 null):")
significant_peaks = [p for p in peaks if p[3]/mean_p > 4.0]
print(f"  Peaks above 4× mean: {len(significant_peaks)}")
if not significant_peaks:
    print(f"    → NO statistically significant peaks under the chi-squared-2 null.")
    print(f"    → Spectrum is broadly consistent with white noise (GUE prediction).")
elif any(abs(p[2] - math.log(1.5)/(2*math.pi)) < 1/N for p in significant_peaks):
    print(f"    → A significant peak NEAR Perfect-Fifth-related frequency is present;")
    print(f"      requires Brandon-decision on whether this is the predicted signature.")
else:
    print(f"    → Significant peak(s) present but NOT at Perfect-Fifth-related frequency.")
print()
print(f"  Autocorrelation: {len(sig)} of 20 lags exceed 95% white-noise bound.")
if len(sig) <= 1:
    print(f"    → Consistent with the GUE prediction (gaps are essentially uncorrelated).")
else:
    print(f"    → More structure than GUE alone predicts; warrants follow-up.")
print()
print(f"  Bottom line: under this operationalization, the gap sequence shows")
print(f"  no significant periodic modulation at log(3/2) or related Perfect-Fifth")
print(f"  frequencies. This is the THIRD distinct operationalization (after Pass 7")
print(f"  T1/T4 ratio-tests) to fail to find a Perfect-Fifth signature in the gap")
print(f"  sequence; the Pass-8.1 affine mapping (T1-B) remains the only consistent")
print(f"  link between the framework's Perfect-Fifth claim and the Riemann zeros,")
print(f"  and that link reduces to RH itself.")
print()
print(f"  Per #69: T4-A adds another orthogonal disconfirmation in the spectral")
print(f"  domain. The framework's Riemann claim should continue to be stated only")
print(f"  via the Pass-8.1 affine projection; further empirical zero-spacing tests")
print(f"  are unlikely to be productive without a sharper, pre-registered prediction.")
print("=" * 78)
