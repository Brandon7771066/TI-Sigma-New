# Phase-1 numerical falsifier-tests — RESULTS

Harness: `run_tests.py` → `results.json`. Runtime ~8 s (primes to 10⁸).
Discipline: predictions **pre-registered in code before computing** (UGI-1 two-phase);
verdicts apply falsifiers II.8-F1 / II.9-F1. **Nothing here proves RH/GRH.**

---

## T1 — Prime races mod 3, 4, 5, 8, 12  (II.8, II.9-A)

**Pre-registered GILE/TRG-1 rule:** the "imaginary"/Tralse-signed class (quadratic
**non-residue**, χ=−1) leads the "real"/G-like class (quadratic **residue**, χ=+1).
The rule predicts **direction only** — not magnitude, not the ordering among several
non-residues.

π(10⁸)=5,761,455. Final per-class counts (mean non-residue − mean residue = S):

| q | residue (χ=+1) | non-residue (χ=−1) | S=mean(nonQR)−mean(QR) | direction predicted? |
|---|---|---|---|---|
| 3 | 1: 2,880,517 | 2: 2,880,937 | +420 | ✅ 2 leads 1 |
| 4 | 1: 2,880,504 | 3: 2,880,950 | +446 | ✅ 3 leads 1 |
| 5 | {1,4}: 1,440,298 / 1,440,186 | {2,3}: 1,440,496 / 1,440,474 | +243 | ✅ non-QR lead |
| 8 | 1: 1,439,970 | {3,5,7}: 1,440,544 / …534 / …406 | +525 | ✅ 3,5,7 lead 1 |
| 12 | 1: 1,440,021 | {5,7,11}: …483 / …496 / …453 | +456 | ✅ 5,7,11 lead 1 |

Direction confirmed at **every** modulus (non-residues collectively ahead at
100 % of log-spaced checkpoints from 10³ to 10⁸).

**VERDICT: RESONANCE, NOT RESULT.** The "non-residue leads" rule *is* Chebyshev's
bias — a known, GRH-provable number-theoretic fact — re-expressed in GILE language.
Direction is *reproduced*, not *predicted independently*, so per II.8-F1/II.9-F1 it
does not clear the bar. Two concrete things the rule fails to predict, which would
make it a result:
- **Magnitude/density** (e.g. the mod-4 Rubinstein–Sarnak log-density ≈ 0.9959) — not derivable from GILE structure here.
- **Ordering among non-residues.** Observed mod-8 order 3 > 5 > 7; observed **mod-12 order 7 > 5 > 11** (non-monotone). The GILE rule is silent on both. A genuine prediction of these orderings from i-Cell/quaternion structure *would* be a result; we have none.

So the honest status of the II.8/II.9-A prime-race lead is unchanged: **beautiful
resonance, unproven bridge.** The test correctly *refused to promote it.*

## T2 — Dirichlet-beta L(s,χ₄) and L(s,χ₃) zeros on the critical line  (II.8, II.9-A)

Using the Hurwitz-zeta forms β(s)=4⁻ˢ[ζ(s,¼)−ζ(s,¾)] and
L(s,χ₃)=3⁻ˢ[ζ(s,⅓)−ζ(s,⅔)]. Seeds found by scanning |L(½+it)| for dips, then
root-found; **5/5 located for each** L-function, every one on Re(s)=½ (max
deviation 9.4e-38):

- χ₄ (mod 4), 5/5: t ≈ 6.0209, 10.2438, 12.9881, 16.3426, 18.2920.
- χ₃ (mod 3), 5/5: t ≈ 8.0397, 11.2492, 15.7046, 18.2620, 20.4558.

**VERDICT: SANITY PASS** for both the mod-4 and mod-3 L-functions (consistent with
GRH). A consistency check on the identities used in II.8/II.9 — **not** a proof.

## T3 — Ternary Cantor string vs Riemann N(T)  (II.9-B, II.4)

Cantor string complex dimensions: D₀ = log₃2 ≈ **0.63093** on the vertical line
Re(s)=log₃2, periodic with imaginary period 2π/log3 ≈ **5.7192** (standard Lapidus
lattice result).

| T | Cantor count (linear) | Riemann N(T) | N(T)/Cantor |
|---|---|---|---|
| 50 | 17 | 8.55 | 0.50 |
| 100 | 35 | 28.13 | 0.80 |
| 500 | 175 | 268.71 | 1.54 |
| 1000 | 349 | 647.74 | 1.86 |

**VERDICT: HONEST NEGATIVE CALIBRATION.** The Cantor string is a *lattice* fractal
string — its complex-dimension count grows **linearly** in T, and its line is
Re(s)=log₃2, not ½. Riemann N(T) grows like (T/2π)log T (super-linear), and the
ratio diverges. So the ternary Cantor string **cannot model the zeta zeros**; it is
a calibration toy only. Modelling ζ would require a **non-lattice / generalized**
fractal string. This is exactly the calibration II.9-B asked for — and it tells us
the simple ternary object is the wrong shape.

## T4 — Operator eigenvalues vs zeta zeros  (II.3, II.2)

First ten ζ zeros (Im): 14.1347, 21.0220, 25.0109, 30.4249, 32.9351, 37.5862,
40.9187, 43.3271, 48.0052, 49.7738.

**VERDICT: HONEST NON-RESULT — TEST CANNOT BE RUN.** replit.md names this the
"cheapest decisive test" (TWA/Berry–Keating operator's first-10 eigenvalues vs
these zeros). But **no concrete self-adjoint operator whose spectrum equals the
zeta zeros is specified anywhere in the corpus** — constructing one *is* the open
Hilbert–Pólya problem (Berry–Keating xp is heuristic and does not yield these
numbers). Producing such an operator here would be claiming a proof of RH, which
#69 forbids. Logged as a non-result: the target operator does not yet exist.

---

## Overall

The Phase-1 tests confirm that **the underlying mathematics in §§II.8–II.9 is real
and correctly stated** (zeros on the line; the Hurwitz-zeta identities; the Cantor
dimensions). They also show the **falsifiers working as intended**: the prime-race
"prediction" is a relabelled known fact (resonance), the ternary Cantor object is
the wrong shape to model ζ (negative calibration), and the headline operator test
**cannot** be run without claiming RH (non-result). No lead was promoted; none was
falsified into deletion; each now carries a sharper, evidence-backed status. This is
#69 honesty operating exactly as designed — and it preserves the spine: the UOP does
not shortcut RH/NS.
