# Pass-77 B155 — Provenance of the Three LCC Rungs and Structural-Jump Tests Against Phase Transitions (2026-06-30)

**Date:** 2026-06-30
**Status:** CANDIDATE-development + status-refinement batch. Canonical principle count **unchanged at 79**. Contains one **status demotion** (the `0.6` resonance rung → *provisional/retrofit*) and outcomes for the B154 falsifiers `LCC-OBS-F1/F2/F3`. No new principle is ratified; no count change.
**Kind:** Corpus archaeology (provenance) + method-validation simulations (necessary-not-sufficient, NO human data) + honest bridging to CHSH/Tsirelson. Real citations only.
**Builds on:** `papers/PASS_77_B154_LCC_THRESHOLD_LADDER_VS_OBSERVATIONAL_COMPLEX_SYSTEMS_THEORY_2026-06-30.md`.
**Author ask (verbatim sense):** *"Confirm or falsify the structural jumps of each threshold from your proposed tests. Root 2 and the CHSH threshold ARE confirmed constants — the question is HOW and IF they truly predict phase transitions in complex systems. And what is the basis for `0.6`, where did it originally come from? Continue the conventional bridging, including Kuramoto."*
**Harness:** `analyses/lcc_complex_systems_obs/run_structural_jump_tests.py` (`config_sha d7712fb41859`), output `structural_jump_tests.json`.

---

## 0. One-paragraph ruling

Two of the three rungs are **confirmed mathematical constants** (the author is right): the onset `√2−1 = tan(π/8)` is exact, and the ceiling `cos²(π/8) = (2+√2)/4` is exact (the Tsirelson optimal-measurement probability). The middle rung `0.6` is **not** in that class: it originated as a *posited* "resonance-physics" axiom with **"no derivation of values"** and was only later **retrofitted** to `(√2+1)/4 = cos²(π/8)·cos(π/4)` — an algebraically *derivative* quantity (the existence ceiling projected 45° onto the classical axis), flagged by its own source paper as possibly "sophisticated pattern-matching." So `0.6` is **demoted to provisional/retrofit** and becomes the prime retirement candidate. On the empirical question — do `√2−1` and `cos²(π/8)`, though exact, *predict phase-transition locations in classical complex systems?* — the structural-jump tests say **mostly no, with one honest caveat**: (T1) a continuous (second-order) Kuramoto transition has its **only** non-analyticity at the onset `r≈0`, at no rung; (T2) an explosive (first-order) transition **jumps `r: 0.27→0.70`, clearing the onset and resonance rungs and landing between the resonance and ceiling rungs — on no rung** (and the related desync edge varies `0.77–0.87` across seeds in T2b, underscoring that such endpoints are run/system-specific, not fixed constants); (T2b, pre-registered) the explosive *desync* edge clusters in a **broad 0.84–0.86 band** that *brackets* `cos²(π/8)` but is **closer to `2^(−1/4)=0.841`** and is system-specific — *consistent-with but underdetermined*, not support; (T3) directional-inference reliability **degrades progressively and collapses as `R→1`** (the genuine LCC-ceiling mechanism, confirmed), but its collapse point is system-specific (`R≈0.97` by the test's `frac<0.9` criterion), **not** pinned to `0.854`. The constants' real home as a transition boundary is the **CHSH/Bell correlation space** (classical-achievable vs quantum-achievable), not classical synchronization — so "IF they predict classical transitions" stays OPEN and "HOW" has **no established mechanism**.

---

## 1. Provenance of the three rungs — answering "where did `0.6` come from?"

| Rung | Value | Status of the *constant* | Provenance |
|---|---|---|---|
| **Onset** | `√2−1 ≈ 0.4142` | **Confirmed exact** — `tan(π/8) = √2−1` (also the CHSH *fractional advantage* `(2√2−2)/2`). | Genuine math/quantum constant. |
| **Resonance** | `≈ 0.6` → `(√2+1)/4 ≈ 0.6036` | **NOT independently confirmed** — see below. | **Posited then retrofitted.** |
| **Ceiling** | `cos²(π/8) ≈ 0.8536` | **Confirmed exact** — `(2+√2)/4`, the Tsirelson optimal-measurement probability. | Genuine math/quantum constant. |

**The honest history of `0.6`** (corpus archaeology):
1. **Original = a posited axiom, explicitly underived.** The earliest appearance is in the "Resonance Physics" axioms: *"Resonance thresholds: 0.42 (survival), 0.6 (LCC), 0.91 (CCC)"* — and the corpus's own self-audit marks this **"Self-Evident? ❌ No · Needs: Derivation of values"** (`papers/TI_AXIOMS_COMPLETE.md`, R3; cf. R2 "all photons carry resonance values 0.42 to 0.91"). So `0.6` entered as a **hand-set / empirically-tuned resonance value**, not a derived one.
2. **Later = a retrofit to a √2-family form.** `papers/CHSH_EXISTENCE_THRESHOLD_COSINE_PI8_EXACT_VALUES.md` (§12.4) matches the pre-existing `0.6` to `(√2+1)/4 = 0.603553…` (within **0.59%**), explicitly noting it **`= cos²(π/8) × cos(π/4)`** — i.e. *"the existence threshold multiplied by √2/2 — existence projected onto the classical axis."* The same paper is admirably honest about the move: *"Status: Hypothesis. The Fibonacci-cosine structure is striking but not derived from first principles… Whether this reflects deep mathematical structure or sophisticated pattern-matching remains open."*
3. **Therefore `0.6` is the weakest rung on three counts:** (a) it began **posited**, not derived; (b) its √2-family form is a **post-hoc retrofit** to a 0.6% numerical coincidence (the B55 two-significant-figure rule means a 0.6% match is *not* discriminating — `0.6036` and several nearby algebraic values are all "within rounding"); (c) the form is **algebraically derivative** (`= ceiling × cos45°`), so it carries **no independent information** beyond the ceiling it is built from.

**Ruling (status refinement, not a count change):** the `0.6 / (√2+1)/4` resonance rung is **demoted to PROVISIONAL/RETROFIT**. It may be *retained as a working recruitment heuristic* (the LCC-Virus seed/propagate convention `R ≥ 0.6` is operationally useful) but it is **stripped of any "derived constant" standing** until it earns an *independent* basis (new falsifier `LCC-PROV-F1`, §6). This sits squarely under the existing anti-numerology rail **HAN-1**: a 0.6%-level retrofit of a posited value is **graded near-zero EVD-1 evidence**, kept illustrative, never load-bearing.

> The same caution extends to the broader "Fibonacci-cosine" table (`cos²(π/5)=φ²/4≈0.6545` for a 0.65 threshold, etc.): elegant, explicitly **unproven**, and post-hoc. Treat as HAN-1-suspect numerology — a generative *hint*, not a result.

---

## 2. The category point (carried from B154, and decisive here)

A **phase transition** is a non-analyticity of an **order parameter** at a critical value of a **control parameter**. The LCC states its rungs on the **order-parameter / correlation axis** `r∈[0,1]` (B154: map LCC `R` ↔ Kuramoto order parameter `r`, *not* the coupling knob `K`). So "is `√2−1` a structural point?" means: **is there a non-analyticity of `r` at `r=0.414` (a *secondary* structural feature on the order-parameter axis)?** The tests below answer this directly for the two canonical transition universality classes (continuous and explosive) and for the directional-inference collapse.

---

## 3. Structural-jump tests (method-validation sims; `config_sha d7712fb41859`)

**T1 — continuous (second-order) Kuramoto** (all-to-all, Lorentzian frequencies, `K_c = 2γ = 1.0`, adiabatic sweep).
Result: `r` rises **continuously** from `r(K=0)≈0.04` to `r(K=4)≈0.89`; the steepest slope `dr/dK` sits at `r≈0.36` (`K≈1.13`), and the largest single-step change is a smooth `0.30`, **not** a discontinuity. **The only non-analyticity is the onset, at `r≈0`.** → **No rung is a structural point of a continuous transition.** `√2−1`, `0.6`, `0.854` are simply values the order parameter passes through on the way up (the B154 anti-vacuity point, now confirmed in a genuine transition).

**T2 — explosive (first-order) Kuramoto** (Barabási–Albert `N=400, m=3`, `ω_i = k_i` frequency–degree correlation, the canonical explosive setup, Gómez-Gardeñes et al. 2011).
Result: a **discontinuous forward jump** `r: 0.272 → 0.702` (size `0.43`) at `K≈1.6`, with **hysteresis** (backward jump size `0.76`). → **The jump clears the onset (`0.414`) and resonance (`0.604`) rungs and lands at `r≈0.70`, between the resonance and ceiling rungs — on no rung.** The endpoints are **run/system-specific** (set by topology, the frequency law, seed, and settling), not fixed constants — cf. the T2b seed sweep, where the related desync edge ranges `0.769–0.866`. A first-order transition does **not** "onset at `0.414`" or "land at `0.6`". → **`LCC-OBS-F2` (structural onset at `√2−1`) is FALSIFIED** for both transition classes.

**T2b — pre-registered ceiling-replication test.** *Before looking, the LCC-ceiling claim predicts the explosive desync (backward-branch) edge should sit near `cos²(π/8)=0.8536`.* Across **8 random seeds** the desync edge `r` was:
`[0.859, 0.835, 0.858, 0.852, 0.849, 0.866, 0.849, 0.769]` → **mean 0.842, std 0.029**, 6/8 within ±2% of the target.
**Honest reading (not support):** the edge clusters in a **broad 0.84–0.86 band** with one clear outlier, and the **mean `0.842` is actually ~10× closer to `2^(−1/4)=0.8409`** (`|Δ|≈0.001`) **than to `cos²(π/8)=0.8536`** (`|Δ|≈0.012`). A high-0.8s desync edge is partly **generic** (synchronized branches lose stability at high `r`), and the band overlaps *several* candidate constants, so it **cannot discriminate** `cos²(π/8)` from `2^(−1/4)` or a plain system-specific value. Verdict: **consistent-with but underdetermined** — a mild EVD-1 resonance worth a real-data follow-up, **explicitly not promoted**. `LCC-OBS-F3` (value replication on ≥2 *independent real datasets*) **remains the gate** and is **not** met by a single simulated family.

**T3 — directional-inference window** (VAR(1) with a fixed true link `y→x` plus a shared common driver `ρ` swept `0→0.985` to push `corr(x,y)→1`; net Granger via residual-variance ratio, 40 bootstraps/level).
Result: directional inference is **fully reliable at low/mid `R`** (`frac_correct_sign = 1.0` for `R ≤ 0.88`; reliability-`z` ≈ 4–7 at low `R`, already decaying to `≈2.2` by `R≈0.88`) and then **collapses as `R→1`** — `frac_correct_sign` falls `1.0 (R≤0.88) → 0.925 (R=0.93) → 0.775 (R=0.97)`, while the regression **condition number explodes `2.4 → 17.8`** and the net-Granger magnitude decays `0.027 → 0.0006`. → **The B154 prediction — directional inference degrades and collapses near `R→1` — is CONFIRMED as a mechanism (`LCC-OBS-F1` mechanism arm holds).** But the **collapse point is system-specific** (`R≈0.97` by the explicit `frac_correct_sign < 0.9` criterion; degradation visible from `R≈0.84`) and is **not** pinned to `cos²(π/8)=0.854`. → `LCC-OBS-F1`'s *value* arm (collapse precisely at the ceiling) is **NOT** supported; its *shape* arm (non-monotone reliability, collapse near full sync) **is**.

---

## 4. Bridging to conventional theory: where `√2−1` and `cos²(π/8)` genuinely ARE transition points

The author's premise is correct and worth stating precisely. `√2−1` and `cos²(π/8)` *are* exact constants **and** they *do* mark a real phase transition — **in the space of correlations**, not in classical synchronization:

- The **CHSH/Bell boundary** separates correlations achievable by local hidden variables (`S ≤ 2`) from those achievable by quantum mechanics (`S ≤ 2√2`, the **Tsirelson bound**; Tsirelson 1980), with super-quantum "PR-box" correlations beyond (`S = 4`; Popescu & Rohrlich 1994). This is a genuine **transition in the achievable-correlation set** as one moves classical → quantum → no-signalling.
- On that boundary, `cos²(π/8) = (2+√2)/4` is the **optimal measurement probability** and `√2−1 = tan(π/8)` is the **fractional advantage** `(2√2−2)/2` of quantum over classical. These are the constants the LCC borrows.

**So the honest answer to "HOW and IF they predict phase transitions":**
- **IF (in classical complex systems):** on current simulated evidence, **no** — classical Kuramoto transitions (continuous and explosive) place their non-analyticities at system-specific locations that **do not coincide** with the rungs (T1, T2), and the one near-match (T2b) is underdetermined.
- **IF (in correlation/quantum-correlation space):** **yes** — they are exactly the Tsirelson-boundary constants. That is a real transition, in a different domain.
- **HOW a classical sync transition could land on them:** there is **no established mechanism**. It would require either (a) the classical order parameter to *be* a Bell-type correlation, or (b) a derived map from synchronization dynamics to the CHSH geometry — **neither demonstrated**. Absent that, the rung↔sync alignment stays a **graded resonance** (HAN-1), and the constants' confirmed status lives in the quantum-correlation domain only.

---

## 5. Per-rung verdict

| Rung | Constant status | Classical-transition prediction | Net ruling |
|---|---|---|---|
| **Onset `√2−1`** | **Confirmed exact** (`tan(π/8)`; CHSH advantage) | **Unsupported** — no structural point at `r=0.414` (T1, T2); `LCC-OBS-F2` **falsified** | Keep as a *correlation-domain* constant; drop the "classical sync onset" reading. |
| **Resonance `0.6`** | **Not independent** — posited + retrofit `(√2+1)/4 = ceiling·cos45°` | not separately tested (no independent basis to test) | **DEMOTED to provisional/retrofit**; retain only as an operational recruitment heuristic; `LCC-PROV-F1` open. |
| **Ceiling `cos²(π/8)`** | **Confirmed exact** (Tsirelson optimal prob.) | desync-edge **bracketed but underdetermined** (T2b); `R→1` collapse **mechanism confirmed**, value not (T3) | Keep as a *correlation-domain* constant; the *mechanism* (inference collapse near full sync) is the real, transferable result; the *value-at-ceiling* claim needs real-data `LCC-OBS-F3`. |

---

## 6. Falsifier outcomes and new falsifiers

- **`LCC-OBS-F1` (inference window) — PARTIALLY CONFIRMED.** *Shape* arm (non-monotone reliability; collapse near `R→1`; condition-number blow-up) holds (T3). *Value* arm (collapse exactly at `cos²(π/8)`) **not** supported — onset is system-specific. Future real-data version stands.
- **`LCC-OBS-F2` (structural onset at `√2−1`) — FALSIFIED** in both continuous and explosive Kuramoto (no non-analyticity at any rung; T1, T2).
- **`LCC-OBS-F3` (value replication) — NOT MET (gate intact).** A single simulated family (T2b) is consistent-but-underdetermined and cannot discriminate `cos²(π/8)` from `2^(−1/4)`; the requirement of **≥2 independent real datasets** stands.
- **NEW `LCC-PROV-F1` (the `0.6` provenance test).** The resonance rung must earn an **independent, non-retrofit** derivation (a basis that does not reduce to "`ceiling × cos45°`" or a sub-1% numerical coincidence) **or be retired** from the constant ladder. Until then `0.6` is an operational heuristic only.
- **NEW `LCC-XDOM-F1` (cross-domain mechanism).** Any claim that the CHSH constants `√2−1` / `cos²(π/8)` predict a *classical* phase transition must exhibit a **derived map** from the classical order parameter to the CHSH correlation geometry; a value-coincidence alone (T2b-style) does **not** count.

---

## 7. Honest limitations

- All four tests are **method-validation simulations** (necessary-not-sufficient): they probe whether the *structure* the LCC asserts can even appear in canonical models, **not** whether it holds in real brains. **No human data** was used.
- **Kuramoto is one family.** "Classical complex systems" is broader (excitable media, criticality/avalanches, percolation); the rungs could in principle surface elsewhere. T1/T2/T2b refute the *universal* sync reading, not every conceivable system — hence the real-data `LCC-OBS-F3` gate.
- The constants' **quantum-correlation status is asserted from established CHSH/Tsirelson theory**, not re-derived here.
- **No live literature retrieval** (Perplexity returned `401`); citations are restricted to landmark works (author-year + journal/DOI where standard), and the *absence* of a universal classical threshold is reported as the finding.
- **Count unchanged at 79**; this batch refines a candidate instrument's *status* and resolves three of its falsifiers — it adds and retires no principle.

---

## 8. References (real)

- Acebrón, J.A., Bonilla, L.L., Pérez Vicente, C.J., Ritort, F., Spigler, R. (2005). The Kuramoto model. *Rev. Mod. Phys.* 77, 137.
- Bell, J.S. (1964). On the Einstein–Podolsky–Rosen paradox. *Physics Physique Fizika* 1, 195–200.
- Boccaletti, S., et al. (2016). Explosive transitions in complex networks. *Physics Reports* 660, 1–94.
- Clauser, J.F., Horne, M.A., Shimony, A., Holt, R.A. (1969). Proposed experiment to test local hidden-variable theories. *Phys. Rev. Lett.* 23, 880–884.
- Gómez-Gardeñes, J., Gómez, S., Arenas, A., Moreno, Y. (2011). Explosive synchronization transitions in scale-free networks. *Phys. Rev. Lett.* 106, 128701.
- Granger, C.W.J. (1969). Investigating causal relations by econometric models and cross-spectral methods. *Econometrica* 37, 424–438.
- Kuramoto, Y. (1984). *Chemical Oscillations, Waves, and Turbulence.* Springer.
- Popescu, S., Rohrlich, D. (1994). Quantum nonlocality as an axiom. *Foundations of Physics* 24, 379–385.
- Schreiber, T. (2000). Measuring information transfer. *Phys. Rev. Lett.* 85, 461–464.
- Strogatz, S.H. (2000). From Kuramoto to Crawford. *Physica D* 143, 1–20.
- Tsirelson, B.S. (1980). Quantum generalizations of Bell's inequality. *Letters in Mathematical Physics* 4, 93–100.

*(Within-corpus anchors: `papers/TI_AXIOMS_COMPLETE.md` R2/R3 for the posited-`0.6` provenance; `papers/CHSH_EXISTENCE_THRESHOLD_COSINE_PI8_EXACT_VALUES.md` §12.4 + App. B for the retrofit and the `2^(−1/4)` candidate; `papers/LCC_COMPOSITION_AND_TRUTH_EXISTENCE_PILLAR_SEPARATION_CANONICAL_RULING_2026-06-27.md` for the canonical ladder.)*
