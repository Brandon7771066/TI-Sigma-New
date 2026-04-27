# URB #786: Numerical Findings on UBKI (Close-Out Path #3, Pilot)

**Title:** Pilot Empirical Investigation of the UOP-Berry–Keating Identification via Finite-Difference Diagonalisation

**Corpus Entry:** #183
**Date:** April 27, 2026
**Status:** Negative pilot result on a small tested class of regulators. Does *not* constitute exhaustive close-out of path #3, but provides strong directional evidence and a reusable harness.
**Companion code:** `riemann_ubki_numerical.py`
**Companion artifacts:** `riemann_ubki_report.json`, `riemann_ubki_comparison.png`, `riemann_ubki_spacings.png`, `riemann_zeros_cache.json`
**Reference:** `papers/RIEMANN_HYPOTHESIS_TI_PROOF_v3.md` §7.4 path #3.

---

## 1. What Was Done (Pilot Scope)

We discretised −i (∂_u + ½) on the log-coordinate grid u ∈ [−L, L] with five candidate self-adjoint structures and compared the resulting eigenvalues to the first N = 200 imaginary parts of non-trivial Riemann zeros (computed via mpmath, cached to JSON):

| Run | Boundary condition | Confinement V(u) |
|---|---|---|
| A | Periodic (parity-symmetric Ĥ_∗) | none |
| B | Periodic | ε (cosh(2u/L) − 1)  (Berry–Keating-like soft wall) |
| C | Periodic | ε \|u\|  (linear) |
| D | Periodic | ε u²  (harmonic; sanity check) |
| E | Antiperiodic | ε (cosh(2u/L) − 1) |

Pilot parameters: GRID = 1500 grid points; L = 30; ε = 5 × 10⁻⁴.

Comparison metrics:
- **RMSE (raw)** between the first 30 positive eigenvalues and the first 30 zeros.
- **RMSE (rescaled)** after a single-parameter linear rescaling γ ↦ α γ chosen so the n-th rescaled eigenvalue's Riemann–von Mangoldt count matches its index. This separates "wrong density" from "wrong individual eigenvalues" and is unique only within linear rescalings.
- **Two-sample KS statistic and p-value** on unfolded nearest-neighbour spacings (`scipy.stats.ks_2samp`), using all 199 available spacings from each side.

## 2. Results

| Run | RMSE (raw) | RMSE (resc.) | Mean rel. err. | KS D (199 spacings) | KS p |
|---|---:|---:|---:|---:|---:|
| A | 66.81 | 3.40 | 7.25 % | 0.503 | 3.3 × 10⁻²³ |
| B | 66.81 | 3.40 | 7.26 % | 0.503 | 3.3 × 10⁻²³ |
| C | 66.80 | 3.48 | 7.44 % | 0.503 | 3.3 × 10⁻²³ |
| D | 66.77 | 3.95 | 8.66 % | 0.503 | 3.3 × 10⁻²³ |
| E | 66.76 | 4.06 | 8.93 % | 0.503 | 3.3 × 10⁻²³ |

(Full per-eigenvalue data and full unfolded-spacing arrays are in `riemann_ubki_report.json`.)

KS D ≈ 0.50 with p ≈ 10⁻²³ across every variant: the unfolded-spacing distributions of these candidate spectra differ from Riemann's at extreme statistical significance. They are clearly drawn from different underlying laws.

## 3. Honest Reading

1. **The bare parity-symmetric Ĥ_∗ on a finite periodic interval has near-equally-spaced eigenvalues** (with ±k pair structure), modulo the slight global cosine-dispersion correction induced by the centered-difference discretisation. Rescaling brings the *range* into Riemann's, but cannot turn a uniform-density spectrum into a logarithmic-density one. Mean-relative-error ≈ 7 % is therefore a *floor* characterising "uniformly spaced after rescaling," not a UBKI-signal.

2. **None of the four added confinements produced any improvement.** B (cosh) is statistically indistinguishable from A; C (linear), D (harmonic), and E (antiperiodic + cosh) are slightly worse. KS p-values are uniform at ~10⁻²³ across A–E. This is consistent with the prediction that *smooth elementary V(u) cannot inject the prime-power data carried by Selberg-style trace formulas*.

3. **What this is and isn't:**
   - This is a **pilot** at one parameter setting (GRID, L, EPS) and one regulator family (smooth elementary V(u)). It does **not** exhaustively rule out all V(u) ∈ ℝ → ℝ.
   - It does provide a **strong directional signal** that the V(u) functional class is the wrong place to look for a UBKI candidate. Combined with the algebraic argument that Riemann zeros require explicit prime-power information in the operator's symbol, this points at *non-V(u)* candidate operators (Connes adelic, BBM PT-symmetric, prime-coded Toeplitz/Hankel symbols).
   - It is **not** consistent with the original v3 §7.4 specification of "first ~10⁵ zeros." Reaching that scale requires a sparse-eigensolver implementation (ARPACK / LOBPCG) in a Krylov framework, which is left as a follow-up. The current dense-diagonalisation harness is comfortable up to GRID ≈ 5000 (matrix size 25M entries).

## 4. What This Sharpens for UBKI

- **Adding a smooth position-space potential V(u) to −i ∂_u is, on the basis of this pilot, very unlikely to be the route to UBKI.** Within the tested regulator class the empirical signal is null at ~10⁻²³ p-value.
- **Effort should redirect to v3 §7.4 paths #1 and #2:** rigorous distributional trace identity (Weil's explicit formula promoted to operator-side equality on Ĥ_∗) and the Connes adelic identification (whether Ĥ_∗ coincides with the L²(ℝ_>0)-restriction of Connes' operator).
- **A proper, more exhaustive close-out of path #3** would require: (i) sparse eigensolvers reaching 10⁴–10⁵ modes; (ii) parameter sweeps in (GRID, L, EPS); (iii) non-elementary V candidates (e.g., V(u) = Σ_p Σ_k log(p)·δ(u − k log p)·smoothing — a prime-power-coded distribution). None of these is in the present pilot.

## 5. What the Script Is Still Useful For

- Cached Riemann zeros (`riemann_zeros_cache.json`) for reuse.
- The `bk_operator(...)` builder accepts arbitrary potentials or matrix overrides; future UBKI candidates (e.g. finite-rank Connes truncations or BBM-style PT-symmetric Hamiltonians) can be plugged in directly.
- The Weyl-counting and unfolded-spacing analysis routines (with proper two-sample KS via `scipy.stats.ks_2samp`) are reusable.

## 6. Status of v3 After This

v3 itself is unchanged. The conditional theorem **UBKI ⟹ RH** (Theorem 6.1 of v3) still holds. UBKI itself remains open. URB #786 contributes a *pilot negative result* on close-out path #3, with strong directional evidence that the smooth-V(u) class is wrong but without exhausting the path. Future work on path #3 should use sparse eigensolvers, larger zero counts, and non-V(u) candidate operators.

The Millennium Prize is **not** claimed.

---

*End URB #786.*
