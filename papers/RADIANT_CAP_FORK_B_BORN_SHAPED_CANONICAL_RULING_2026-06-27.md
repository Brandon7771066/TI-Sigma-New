# Radiant Cap — Canonical Ruling: the Square-Root / Born-Shaped Form (Fork B)

**Date:** 2026-06-27
**Status:** CANONICAL RULING (refinement; canonical principle count **unchanged at 79**).
**Supersedes:** `papers/GRAND_TRUTH_FORMULA_SQRT_CORRELATION_DERIVATION.md` (December 2025 heuristic; its "0.92 / 0.85 / 0.42" numerics, "MATHEMATICAL BREAKTHROUGH" framing, and "mathematics of reality itself / mathematical proof" language are retracted — see §6).
**Relation to canon:** refines the UOP Radiant-Cap value and its generating relationship; does **not** introduce a new principle, and does **not** claim the normative threshold is deductively proven.

---

## 0. Ruling in one line

> The canonical GILE-Truth Radiant Cap is **G\* = √(1 − e⁻²) ≈ 0.92987**, fixed by the relationship **Existence = G\*² (exact)** to a minimum-existence floor **L = 1 − e⁻² ≈ 0.86466**. This **supersedes** the earlier arithmetic-midpoint value **G\* = 1 − ½e⁻² ≈ 0.93233**.

The change is ~0.25% in value; its point is *coherence*, not precision: it makes "existence = (truth cap)²" an **exact identity** rather than an approximation.

---

## 1. Why so many expressions clustered near 0.93 (the real answer)

The earlier corpus carried several near-coincident numbers — a floor near 0.85–0.865, a cap near 0.92–0.932, a "thirds" reading, a midpoint reading, a √-correlation reading. They are **not** independent mysteries converging by luck. **Every one of them is a low-order function of a single small parameter**

> **ε = e⁻² ≈ 0.13534** (which itself encodes one posit: **λ = 2**, "settled" after two relaxation time-constants).

Concretely, with `f(t) = 1 − e^{−t/τ}` the least-effort first-order approach to an asymptote, evaluated at **λ = t/τ = 2** (the standard ≈86.5% "well-settled" criterion):

| quantity | closed form | value |
|---|---|---|
| settling floor (existence) | `L = 1 − ε` | 0.864665 |
| midpoint cap (Fork A, retired) | `1 − ½ε` | 0.932332 |
| square-root cap (Fork B, canonical) | `√(1 − ε)` | 0.929873 |
| existence via shared variance | `cap² ` (Fork B: `= 1 − ε`) | 0.864665 |

The floor `1 − ε` and the old "square" floor `(1 − ½ε)² = 1 − ε + ¼ε²` agree to first order in ε and **differ by exactly ¼e⁻⁴ ≈ 0.00458** — that small gap is the entire "0.85 vs 0.865 vs 0.869" confusion. The legacy "0.85 causation threshold" was simply `1 − ε = 0.8647` rounded down to 0.85, and the legacy "0.92" was `√0.85 ≈ 0.922` with that rounded floor. Use the principled floor `1 − e⁻²` and the cluster collapses to one number-family.

---

## 2. The genuine fork (and why it cannot be dodged)

There are two natural ways to relate the cap to the floor, and **they cannot both be exact**:

- **Fork A — arithmetic midpoint:** `G* = (1 + L)/2 = 1 − ½e⁻² = 0.93233`. Then existence-as-cap² is only *approximate* (off by ¼e⁻⁴).
- **Fork B — square root:** `G* = √L = √(1 − e⁻²) = 0.92987`. Then **Existence = G*² is exact**, and the midpoint reading is only approximate.

Requiring *both* — `cap = (1 + cap²)/2` — gives `(cap − 1)² = 0`, i.e. the degenerate `cap = 1`. So exactly one relationship can be canonical. **Brandon's ruling selects Fork B**, because the motivating intuition is "Existence's radiant correlation (a correlation coefficient) = the *square* of the Radiant Cap for GILE-Truth," and Fork B makes that an identity rather than a near-miss.

---

## 3. The elegance anchor: the Born rule (structural resonance, not derivation)

Why a *square root* specifically? The most elegant reason is a structural echo of quantum mechanics' **Born rule** (Born 1926): an observable probability equals the squared magnitude of an underlying amplitude,

> `p = |ψ|²`  ⇔  `ψ = √p`   ↔   **Existence = G\*²**  ⇔  **G\* = √Existence**.

Reading the analogy:

- **GILE-Truth ↔ amplitude** — the deeper, *phase-carrying* quantity (carries a real part *and* an imaginary/indeterminate part).
- **Existence ↔ Born probability `|ψ|²`** — the real, manifest "shadow" we actually observe; "manifestation" is the squaring.

This **coheres with two things already in the corpus**: the complex picture of partial determinacy (`z = E + i·GIL`, urb_629) and **TRG-1** (reality is *tralse*, not crisply true) — the amplitude is itself tralse-complex, and squaring it to a real probability is exactly what manifestation does. That internal coherence is the strongest kind of support available here.

**This is a resonance (TPS-1 / RAI-1), not a derivation.** The cap's *value* still comes from the λ=2 posit plus the √-choice; the Born rule explains the *shape*, not the number.

---

## 4. Explicit anti-numerology disclaimer: there is NO CHSH numeric coincidence

It is tempting — and would be *wrong* — to claim the cap equals a quantum-correlation bound. Verified honesty check (none matches the floor 0.86466 or the cap 0.92987):

| CHSH-derived quantity | value | distance to cap |
|---|---|---|
| classical bound / 2 | 1.000 | — |
| Tsirelson 2√2 / per-correlator `1/√2` | 0.70711 | 0.223 |
| quantum excess `2√2 − 2` | 0.82843 | 0.101 |
| `2^{−1/4} = √(1/√2)` | 0.84090 | 0.089 |
| **`cos(π/8)` (a real CHSH angle)** | **0.92388** | **0.0060** |
| `√2 − 1` (LCC_TRALSE) | 0.41421 | 0.516 |

The nearest, `cos(π/8) = 0.9239`, is a genuine CHSH measurement angle and sits only 0.6% from the cap — precisely the kind of near-miss the framework must **resist as numerology** (#69). The √2 that *does* legitimately appear in the CHSH story is doing a different job: it marks where reality outruns any single classical joint-probability model (Fine 1982; the framework's "Contextual Admissibility"). It is **not** where the cap's value comes from.

---

## 5. Honest status (#69)

- **Two posits, not a theorem.** (i) λ = 2 fixes the floor `L = 1 − e⁻²`; (ii) the *square-root* relationship fixes the cap `G* = √L`. Both are *posited*, defensible by convention and coherence, **not derived**.
- **Not a proof of the normative threshold.** Nothing here shows that ≈0.93 is the morally/normatively *correct* ceiling; it remains a disciplined modeling commitment with **open falsifiers**.
- **Holistic, not per-dimension** (unchanged): the cap binds the single GILE aggregate, not each of G/I/L/E.
- **Above-cap permissible-but-not-sustainable** (unchanged).
- **Count unchanged at 79.** This is a refinement of an existing principle's value, not a new principle.

---

## 6. What is retracted from the December-2025 source

The superseded `GRAND_TRUTH_FORMULA_SQRT_CORRELATION_DERIVATION.md` is kept for provenance but its claims are **downgraded**: the "0.42 Hz consciousness frequency," "Butterfly Octopus Knot" arm-counting, "+2.0 (TRUE)" self-rating, and the "this is the mathematics of reality itself / mathematical proof that truth has structure" language are **not** canon. The durable, correct kernel it contained — *the cap relates to an existence/correlation quantity by a square root* — survives here in disciplined form (Fork B), with the floor upgraded from the rounded 0.85 to the principled `1 − e⁻²`.

---

## References

- Born, M. (1926). "Zur Quantenmechanik der Stoßvorgänge." *Zeitschrift für Physik* 37, 863–867. (Origin of the probability rule p = |ψ|²; invoked here only as a *structural* shape, not a derivation of the cap's value.)
- Fine, A. (1982). "Hidden Variables, Joint Probability, and the Bell Inequalities." *Physical Review Letters* 48, 291–295. (A single joint distribution matching the marginals exists iff the Bell/CHSH inequalities hold; cited for why the √2 in CHSH marks contextuality, not the cap.)
- Bell, J. S. (1964). "On the Einstein Podolsky Rosen Paradox." *Physics* 1, 195–200. (Context for the CHSH/Tsirelson bound discussed in the no-coincidence section.)

*(Cited as background only. None of these works derive, endorse, or validate the Radiant Cap; the cap and its √-link remain framework posits with open falsifiers.)*

---

## Appendix — numbers (reproducible)

```
ε = e⁻²                  = 0.135335
L  = 1 − e⁻²  (existence)= 0.864665
G* = √(1 − e⁻²) (cap)    = 0.929873      ← CANONICAL
G*²                      = 0.864665  (= L, exact)
1 − ½e⁻²  (Fork A, retired)= 0.932332
(1−½e⁻²)² − (1−e⁻²) = ¼e⁻⁴ = 0.004579
thirds: T_d = (G*+1)/3   = 0.643291   (3·T_d − 1 = G*)
1 − G*                   = 0.070127   (≈ 7% reserved for existence)
```

**Open falsifiers carried forward:** any independent, non-circular determination of the floor that contradicts `1 − e⁻²`; any principled reason the cap–floor relation must be the midpoint (Fork A) rather than the square root; any genuine (not rounded) CHSH/Tsirelson identity for L or G*.
