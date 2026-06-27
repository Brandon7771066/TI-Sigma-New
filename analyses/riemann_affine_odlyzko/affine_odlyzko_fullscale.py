"""
Q4(a) — Riemann affine PD-map verification on the FULL open Odlyzko zero table.

Canonical (Conv A, ratified): PD(s) = 5*(sigma - 1/2) + i*gamma/gamma_1,
critical line sigma=1/2 -> Re(PD)=0.  gamma_1 ~ 14.134725...

This SCALES the prior 300-zero check (analyses/riemann_affine_verify) up to the
open 1,000,000-zero Odlyzko/LMFDB table shipped in data/riemann_zeros/.

HONESTY (#69):
  * The data file contains gamma-HEIGHTS only; every zero is taken on sigma=1/2.
    So "Re(PD)=0 for all zeros" is TRUE BY CONSTRUCTION and is NOT a test of RH.
    It confirms internal consistency of the affine embedding, nothing more.
  * The Emerick-Crossover identity (sigma=1/2 +- 1/(5*sqrt2) -> PD-real=+-1/sqrt2)
    is an ALGEBRAIC identity, data-independent; we confirm it exactly.
  * The one genuine open-DATA check is the GUE nearest-neighbour spacing law
    (Montgomery-Odlyzko). Since the PD-image is the gamma-axis rescaled by a
    constant (1/gamma_1), spacing statistics are SCALE-INVARIANT, so the PD-image
    inherits exactly the same spacing law. We reproduce it on 1e6 zeros as a
    dataset-sanity + scale-invariance confirmation. This reproduces a KNOWN
    result; it is not a new theorem and says nothing about RH.
"""
import math
import numpy as np

ZEROS_PATH = "data/riemann_zeros/first_1million_zeros.txt"

print("=" * 78)
print("Q4(a) Riemann affine PD-map on the open 1,000,000-zero Odlyzko table")
print("=" * 78)

gammas = np.loadtxt(ZEROS_PATH)
N = len(gammas)
gamma_1 = gammas[0]
print(f"loaded N = {N:,} zeros; gamma_1 = {gamma_1:.9f}")

# ---- V1 constructive (tautological) -----------------------------------------
print("\n## V1  Re(PD)=5*(sigma-1/2) with sigma=1/2 for every zero")
print(f"  Re(PD)=0 for all {N:,} zeros BY CONSTRUCTION (data are heights on the")
print("  assumed critical line). This is NOT evidence for RH (#69).")

# ---- V2 imaginary image at scale --------------------------------------------
im = gammas / gamma_1
print("\n## V2  Im(PD)=gamma/gamma_1 (a few landmarks)")
for i in (0, 1, 9, 99, 9999, 999999):
    if i < N:
        print(f"  zero #{i+1:>8,}  gamma={gammas[i]:>14.4f}  Im(PD)={im[i]:>14.5f}")

# ---- V4 Emerick-Crossover algebraic identity --------------------------------
off = 1.0 / (5 * math.sqrt(2))
pd_real = 5 * off
print("\n## V4  Emerick-Crossover identity (algebraic, data-independent)")
print(f"  sigma = 1/2 +- 1/(5*sqrt2) = 1/2 +- {off:.10f}")
print(f"  PD-real = 5 * 1/(5*sqrt2) = 1/sqrt2 = {pd_real:.10f}")
print(f"  exact match to 1/sqrt2 = {1/math.sqrt(2):.10f}: "
      f"{abs(pd_real - 1/math.sqrt(2)) < 1e-12}")

# ---- V5 GUE nearest-neighbour spacing on the unfolded zeros -----------------
# Unfolding: expected counting fn N(t) ~ (t/2pi)(ln(t/2pi)-1) + 7/8.
def riemann_count(t):
    return (t / (2 * math.pi)) * (np.log(t / (2 * math.pi)) - 1.0) + 7.0 / 8.0

w = riemann_count(gammas)            # unfolded positions, mean spacing -> 1
s = np.diff(w)                       # unfolded spacings
s = s[(s > 0) & (s < 5)]             # drop pathological endpoints
print("\n## V5  GUE nearest-neighbour spacing (open-data reproduction)")
print(f"  unfolded spacings: n={len(s):,}  mean={s.mean():.4f} (target ~1.0)  "
      f"std={s.std():.4f}")

# Compare histogram to GUE Wigner surmise and to Poisson on a coarse grid.
def gue(x):
    return (32 / math.pi**2) * x**2 * np.exp(-4 * x**2 / math.pi)
def poisson(x):
    return np.exp(-x)

edges = np.linspace(0, 3, 31)
hist, _ = np.histogram(s, bins=edges, density=True)
centers = 0.5 * (edges[:-1] + edges[1:])
gue_pred = gue(centers)
poi_pred = poisson(centers)
l1_gue = np.mean(np.abs(hist - gue_pred))
l1_poi = np.mean(np.abs(hist - poi_pred))
print(f"  mean|hist-GUE|     = {l1_gue:.4f}")
print(f"  mean|hist-Poisson| = {l1_poi:.4f}")
print(f"  -> data follows {'GUE' if l1_gue < l1_poi else 'Poisson'} "
      f"(expected: GUE, the Montgomery-Odlyzko law). Scale-invariant, so the")
print("     PD-image inherits the identical spacing law. Reproduction, not new.")

print("\nSUMMARY: affine embedding is internally consistent at 1e6 scale; Emerick")
print("crossover exact; zeros obey GUE spacing. NONE of this bears on RH (#69).")
