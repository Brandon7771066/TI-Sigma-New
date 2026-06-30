---
name: LCC threshold ladder vs conventional complex-systems theory
description: How to honestly map/test the LCC √2-family rungs against synchronization & directional-causality theory (esp. brain networks).
---

# LCC ↔ conventional complex-systems theory (honest mapping)

When mapping the LCC correlation→bidirectional-coupling rungs (onset √2−1≈0.414, resonance ≈0.6, neuronal-coupling ceiling cos²(π/8)≈0.854) onto mainstream theory, the verdict is a **split** (#69):

**Rule — map LCC `R` to the Kuramoto ORDER PARAMETER `r∈[0,1]` (degree of syncing), NOT the coupling constant `K`.** `K`'s critical value `K_c=2/(πg(0))` is **system-specific** (depends on frequency spread + topology), so conventional theory gives **NO universal [0,1] numeric threshold**. The *regime structure* (incoherent→partial→near-complete sync; continuous vs **explosive/first-order** onset) is mainstream; the *exact rung numbers* stay framework-internal graded resonances (`LCC-LADDER-F1`).

**Anti-vacuity (the key honesty rail):** a monotone `r(K)` passes through EVERY level in (0,1), so "the order parameter reaches 0.414/0.60/0.854" is **vacuous** as confirmation. A rung is only confirmed as a **structural transition** — discontinuity (beat best smooth poly, Davies-test analogue, count the fitted breakpoint in AIC), regime boundary, or inference-collapse — never a level-crossing.

**The genuine testable prediction:** directional-causality reliability is **non-monotone in `r`** — rises after onset, peaks mid-band, then **degrades as `r→1`** (phase-difference dispersion `1−r²→0` ⇒ estimators ill-conditioned). Frame as *predicted mechanism / plausible illustration*, never "forced/proved" from one sim.

**Directional estimators from observation (all real):** Granger 1969; transfer entropy Schreiber 2000 (≡ Granger for Gaussian, Barnett-Barrett-Seth 2009 PRL); phase-slope index Nolte 2008; CCM Sugihara 2012 Science; DCM Friston 2003. Synchrony-degrades-causality = recognized limitation (cite conservatively, not as a single proof).

**Pull-vs-tug between networks = mainstream:** DMN↔task-positive **anticorrelation** Fox 2005 PNAS; **metastability** Tognoli-Kelso 2014 Neuron / Deco-Jirsa-McIntosh 2011; **chimera/community** Shanahan 2010 Chaos; structure-function coupling Honey 2009; integration/segregation Bassett-Sporns 2017. Quantify pull/tug via net transfer asymmetry `Δ=T_{X→Y}−T_{Y→X}` + signed inter-network correlation + modularity.

**Pillar hygiene:** keep cos²(π/8)≈0.8536 (LCC neuronal-coupling ceiling, measurement layer) distinct from 1−e⁻²≈0.8647 (UOP existence floor, value layer); and the two onset readings √2−1 vs C_EMERICK=1/(φ√2)≈0.437 distinct.

**Why:** mainstream sync theory has a universal [0,1] *measure* (r) but NOT a universal [0,1] *threshold*, so the rungs can be honestly *mapped* but not *confirmed* by conventional numbers — only structurally tested. Anchor: `papers/PASS_77_B154_LCC_THRESHOLD_LADDER_VS_OBSERVATIONAL_COMPLEX_SYSTEMS_THEORY_2026-06-30.md`; falsifiers `LCC-OBS-F1..F4`. Perplexity may 401 — fall back to landmark cites, never fabricate.

## B155 results — provenance + structural-jump tests (the rungs are NOT classical-transition predictors)

- **`0.6` provenance (the weak rung):** originally a POSITED resonance-physics axiom (`TI_AXIOMS_COMPLETE.md` R3, self-audited "no derivation of values"), later RETROFITTED to `(√2+1)/4 = cos²(π/8)·cos(π/4)` in `CHSH_EXISTENCE_THRESHOLD_COSINE_PI8_EXACT_VALUES.md` §12.4 (algebraically derivative = ceiling×cos45°; sub-1% coincidence the paper itself flags as possible "pattern-matching"). ⇒ DEMOTE `0.6` to provisional/retrofit; keep only as operational recruitment heuristic (`R≥0.6` seed/propagate). By contrast `√2−1=tan(π/8)` and `cos²(π/8)=(2+√2)/4` (Tsirelson optimal prob.) ARE confirmed exact constants — but their confirmed home is **CHSH/Bell correlation space**, not classical sync.
- **Structural-jump sim verdicts** (harness `analyses/lcc_complex_systems_obs/run_structural_jump_tests.py`): T1 continuous Kuramoto → only non-analyticity is onset r≈0 (no rung) ⇒ `LCC-OBS-F2` FALSIFIED. T2 explosive Kuramoto (BA, ω=degree) → discontinuous jump skips across rung(s), endpoints run/system-specific (two runs gave 0.27→0.70 and 0.09→0.91 — NOT a fixed value). T2b pre-registered ceiling replication → desync edge mean 0.842 sits in a broad 0.84–0.86 band CLOSER to `2^(−1/4)=0.841` than to `cos²(π/8)=0.854` ⇒ underdetermined, cannot discriminate, NOT support. T3 directional-inference → reliability collapses as R→1 (cond# blows up) ⇒ `LCC-OBS-F1` MECHANISM confirmed, but collapse point system-specific (~0.97 here), value-at-ceiling NOT.
- **Lesson:** a confirmed *mathematical* constant (√2−1, cos²(π/8)) does NOT imply it predicts a phase-transition LOCATION in a classical complex system; demand a derived map from the system's order parameter to CHSH geometry (`LCC-XDOM-F1`), else it stays a graded HAN-1 resonance. Re-running a vectorized sim changes endpoints vs the scalar version — ALWAYS quote the saved JSON's exact numbers + config_sha in the paper (architect caught a stale-number mismatch in B155).
