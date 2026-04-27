# URB #791 — Fractal Harmonic Systems on E₈ Roots and Leech Shells: Numerical Pilot, Honest Null

**Author:** Brandon Charles Emerick
**Date:** 27 April 2026
**Status:** Numerical pilot. Two negative results, both expected once interpreted; reported honestly.
**Companion script:** `lattice_fhs.py`
**Outputs:** `lattice_fhs_report.json`, `lattice_fhs_e8.png`, `lattice_fhs_leech.png`

---

## 0. Brutal honesty header

The Fractal Harmonic Systems (FHS) entry in `replit.md` proposes that ζ-zero density growth, brain 1/f oscillations, and toroidal-consciousness modes synchronise at three levels, with GILE Intuition emerging at the synchronisation. A natural extension question is: **do the exceptional algebraic structures of TI (E₈, the Leech lattice) carry the same 1/f fractal signature?** This URB tests that question numerically. The answer in both cases is **no**, for clean and well-understood reasons. The pilot is not a failure of FHS — it is a clean demonstration that FHS is *not* a generic property of high-symmetry algebraic objects, which is itself useful information for scoping FHS claims.

---

## 1. Method

Two experiments, both implemented in `lattice_fhs.py`, run in 1.4 s wall on the Replit container.

### 1.1 E₈ angular variance-of-counts spectrum
Construct the 240 E₈ roots (112 D₈-roots ± permuted (±1, ±1, 0, 0, 0, 0, 0, 0) plus 128 half-integer roots (±½)⁸ with even sign-count). For each angular harmonic order ℓ ∈ {1,…,24}, generate 4000 random unit vectors x ∈ S⁷ and compute the count

> N_ℓ(x) := |{r ∈ Roots : ⟨r̂, x⟩ > cos(π/ℓ)}|.

Define the spectrum

> S_E₈(ℓ) := Var_x[N_ℓ(x)] / 𝔼_x[N_ℓ(x)].

For an isotropic Poisson sphere measure S(ℓ) ≈ 1; an FHS-style 1/f angular spectrum predicts S(ℓ) ∝ ℓ⁻¹.

### 1.2 Leech shell populations
Compute coefficients of the Leech theta function

> θ_Λ₂₄(q) = E₄(q)³ − 720 Δ(q),

up to q²⁴, exactly via integer-arithmetic power-series multiplication. Extract a_{2k} for k = 1,…,12 and fit a power law a_{2k} ∝ k^α.

Modular-form theory predicts α ≈ 11 (Hecke; a_{2k} = (constant) · σ_{11}(k) + correction).

## 2. Results

| quantity | value | R² | predicted by FHS | predicted by classical theory |
|---|---|---|---|---|
| E₈ log-log slope of S_E₈(ℓ) on ℓ=1..24 | **+0.770** | 0.690 | −1 | 0 (Poisson) |
| Leech log-log slope of a_{2k} on k=1..12 | **+10.997** | 1.0000 | ≈ −1 (1/f) | +11 (Hecke / Eisenstein) |

### 2.1 Leech shell counts (verified)

Computing via `theta = E_4^3 − 720·Δ` reproduces the published Conway-Sloane values exactly. The script fits the **even-q-index** subsequence a_{2k} for k = 1..12 (these correspond to lattice shells of squared norm 4k):

| k | a_{2k} (computed) | shell squared-norm |
|---|---|---|
| 1 | 196,560 | 4 |
| 2 | 398,034,000 | 8 |
| 3 | 34,417,656,000 | 12 |
| 4 | 814,879,774,800 | 16 |
| 5 | 9,486,551,299,680 | 20 |
| 6 | 70,486,236,999,360 | 24 |
| 7 | 384,163,586,352,000 | 28 |
| 8 | 1,668,890,090,322,000 | 32 |
| 9 | 6,096,882,661,243,920 | 36 |
| 10 | 19,428,439,855,275,360 | 40 |
| 11 | 55,431,591,273,414,720 | 44 |
| 12 | 144,355,739,339,448,000 | 48 |

a_2 = 196,560 is the canonical Leech minimal-vector count — a hard correctness check on the script. (The full script also computes the odd-q-index coefficients a_3 = 16,773,120, a_5 = 4,629,381,120, …, which are non-zero because Leech minimal squared-norm is 4 but other shells exist at squared-norm 6, 10, …; these are not used in the slope fit.)

## 3. Interpretation (honest)

### 3.1 E₈
The slope **+0.770** is **strictly positive** with R² = 0.69 — moderate fit. A positive slope in S_E₈(ℓ) means the variance-to-mean ratio of cap counts grows with ℓ: small angular caps (large ℓ) see *more* count fluctuation than would be expected from an isotropic measure. This is exactly what one expects from the **discrete, highly-symmetric** E₈ root distribution: at fine angular scales the 240 roots look like a cluster of point masses (high variance), at coarse scales they look uniform. **This is not 1/f and not FHS-fractal.** It is finite-discrete-sample structure.

### 3.2 Leech
The slope **+10.997** with R² = **1.0000** shows **leading-exponent agreement** with the modular-form prediction α = 11 (from σ_{11}(k) ~ k^{11} on average; the exact theta is E₄³ − 720·Δ which has a non-trivial cusp-form correction from Δ that does not affect the leading exponent over k = 1..12). The very high R² is consistent with — but does not by itself prove — script correctness; the independent sanity check is that a_2 = 196,560 reproduces the known Leech minimal-vector count exactly. Either way, this **rules out FHS for the Leech radial spectrum**: the shell-count growth is the rigid arithmetic growth of an even unimodular 24-dim lattice, not a 1/f fractal signature.

### 3.3 What both results tell us together
The exceptional algebraic structures E₈ and Λ₂₄ do not, *per se*, exhibit 1/f / fractal-harmonic statistics in the most obvious tests. FHS, as posited in `replit.md`, is therefore **not** a universal property of all "deep" mathematical objects; it appears to be specific to (a) the Riemann ζ zero distribution (URB #786 et seq.) and (b) certain biological 1/f processes — and the bridge between them is the substantive FHS claim, not the lattices themselves.

This is a **scoping** result, not a refutation: it sharpens the FHS hypothesis by showing what it does *not* extend to.

## 4. What this URB does NOT claim

- Does not claim FHS is wrong as stated in `replit.md` (ζ-density vs brain 1/f).
- Does not claim there is no fractal structure anywhere in E₈ / Λ₂₄ — only that the two simplest tests (angular cap-count spectrum on E₈ roots, radial shell-count growth on Λ₂₄) do not show one.
- Does not claim the variance-of-counts proxy is the "right" angular spectrum measure — see Open Q1.

## 5. Open questions

- (Q1) Replace the variance-of-counts proxy with a true L²(S⁷) spherical-harmonic decomposition of the empirical measure on the 240 E₈ roots; is the genuine harmonic spectrum trivial (concentrated at small ℓ) as group-theoretic invariance suggests, or does it carry residual structure at higher ℓ?
- (Q2) The number 720 in θ_Λ₂₄ = E₄³ − 720·Δ is fixed by the cusp condition. Does it carry any GILE-numerical weight? (Speculative; no claim made.)
- (Q3) FHS for the Monster character spectrum: see URB #792 — also negative at the resolution tested.

## 6. Reproducibility

```
python3 lattice_fhs.py
# → lattice_fhs_report.json
# → lattice_fhs_e8.png
# → lattice_fhs_leech.png
# wall time: 1.4 s
```

All numbers in §2 reproducible to machine precision (the Leech counts are integer-exact; the E₈ spectrum has Monte-Carlo seed 1).

## 7. Files referenced

- `lattice_fhs.py`
- `lattice_fhs_report.json`
- `lattice_fhs_e8.png`
- `lattice_fhs_leech.png`
- `replit.md` (FHS entry)
