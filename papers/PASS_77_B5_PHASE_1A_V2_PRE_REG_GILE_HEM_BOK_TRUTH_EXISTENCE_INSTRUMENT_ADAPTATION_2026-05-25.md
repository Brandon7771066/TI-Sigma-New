# Pass-77 Batch-5 — Phase-1A-v2 PRE-REG: GILE-HEM (BOK) Truth-vs-Existence instrument supersedes L×E, applied to same DANDI:000003 rat hippocampal LFP

**Date:** 2026-05-25
**Pass / Batch:** 77 / B5 (pre-reg lock)
**Status:** PRE-REG LOCKED — falsifiers + thresholds frozen BEFORE execution.
**Predecessor:** `papers/PASS_77_B4_PHASE_1A_RODENT_MOOD_TRAJECTORY_REFUTED_2026-05-25.md` (L×E REFUTED on both falsifiers).
**Brandon directive (verbatim, 2026-05-25):** *"Go ahead with adapting the instrument for the rodent using the updated GILE-HEM (BOK) Truth vs Existence Model since that superseded the L*E model! Let's not accept the refutation yet!"*
**Anti-cheat compliance:** per B4 §5, this paper specifies the adapted instrument BEFORE any code is run or data is opened. The runner code will be committed in this same batch with a frozen-hash, and any deviation in the executed run must be disclosed in the B5 results paper.

---

## 1. Why a new instrument was warranted (B4 honest #69 carry-forward)

Pass-77-B4 demonstrated, on real DANDI:000003 sub-YutaMouse41 rat hippocampal LFP, that the canonical TLC-1 mood-instrument M_r = L × E **refutes on both pre-reg falsifiers** with the specific failure signature of **multiplicative cancellation** (η²=0.000 on awake-vs-NREM, the easiest test in mammalian electrophysiology). The diagnosis: L (gamma-PLV) and E (theta/delta ratio) have opposing sleep-state signatures in within-HPC LFP, so their product cancels.

The TI Sigma corpus has since Pass-67 (GTT-1 canonical #27) and Pass-68-B1 (UOP phase-transition mathematical confirm) maintained an **additive, asymmetric-cap** alternative composition of truth-and-existence components:

```
J(G, H) = f(G) + g(H)
where
  f(G) = log(1 + G)                            for G ≤ G* = 0.93   ("truth contribution, free below cap")
  f(G) = log(1 + 0.93) - α (G - 0.93)²         for G > G* = 0.93   ("quadratic penalty above cap; truth too far has cost")
  g(H) = log(1 + H)                            ("existence contribution, monotone unbounded-but-saturating")
  α    = 10.0                                  (canonical Pass-68-B1 parameter)
```

This model **structurally cannot cancel** the way L×E did, because:
- (a) The composition is additive (f+g), not multiplicative (L·E), so opposing component movements produce non-zero net Δ
- (b) The G axis is privileged with an asymmetric cap (no symmetric cap on H), so over-coherence is *penalized* — a mood-instrument that includes a penalty for excess synchrony has direct physiological correspondence (epileptiform-like over-coherence = pathological, not maximally healthy)
- (c) The log transforms compress saturation regions, reducing dependence on arbitrary normalization constants like the 3.0 saturation B4 used for E

This is therefore not a goalpost-shift; it is a structurally different composition canonical-already-in-corpus, applied to the same substrate with the same data slice and the same pre-reg thresholds.

---

## 2. Instrument specification (Phase-1A-v2, FROZEN)

### 2.1 Component mappings — rodent LFP → (G, H)

Per Brandon-corrected B3 §3.2 (canonical L = mean gamma-PLV across hippocampal channel pairs; canonical E = rodent theta/delta ratio per `eeg_bci_system.py`).

| Symbol | Definition | Computation | Range |
|---|---|---|---|
| **G_t** | GILE-truth proxy: cross-channel phase-coherence in the gamma band | mean PLV(30–80 Hz) across all C(MAX_CHANNELS, 2) channel pairs within 2 s window | [0, 1] (PLV is bounded) |
| **H_t** | HEM-existence proxy: balance of fast (theta) over slow (delta) activity = "alert presence vs withdrawn slow-wave" | H = θ/(θ + δ) where θ = mean PSD power 6–10 Hz, δ = mean PSD power 1–4 Hz | [0, 1] (bounded ratio, no arbitrary saturation constant) |

**Difference from B4:** B4 used `E = min(1, theta/delta / 3.0)`, an arbitrary-constant saturation. v2 uses the canonical fast-fraction ratio θ/(θ+δ), naturally bounded, no free parameters.

### 2.2 Composition

```
G_t  = mean_pairs PLV_γ(s_t)                                 # truth axis
H_t  = θ_power(s_t) / (θ_power(s_t) + δ_power(s_t))          # existence axis
J_t  = f(G_t) + g(H_t)                                       # Pass-68 canonical
```

with f, g, α per §1 above.

### 2.3 Constants frozen

| Symbol | Value | Source |
|---|---|---|
| GAMMA band | 30–80 Hz | B4 carry, eeg_bci_system.py |
| THETA band | 6–10 Hz | B4 carry, eeg_bci_system.py |
| DELTA band | 1–4 Hz | B4 carry, eeg_bci_system.py |
| WINDOW_SEC | 2.0 | B4 carry |
| G_STAR | 0.93 | Pass-68-B1 canonical |
| α | 10.0 | Pass-68-B1 canonical default |
| MAX_CHANNELS | 4 | B4 carry |

**Bands are NOT being adapted in this batch.** Brandon directive selected branch (A) but did not authorize band-redefinition. The split-gamma-low/high option from B4 §5 (A) is held for a *separate* future pre-reg, to avoid confounding "additive-composition wins" with "rodent-specific-bands win".

---

## 3. Falsifiers (FROZEN, same as B4)

Per Pass-37 frozen-rubric precedent, falsifier thresholds are identical to B4 to permit direct A/B comparison. Only the metric on which they are evaluated changes: **J_t replaces M_r**.

### F-PHASE1A-1-v2: J reacts to PulseStim events

- **Test:** Welch's t-test of J_t(post) − J_t(pre) for 2 s pre/post windows centered on each PulseStim event timestamp
- **Statistic:** Cohen's d on Δ = J_post − J_pre
- **CI:** 95 % bootstrap (10 000 resamples, BCa) on mean(Δ)
- **PASS:** |d| > 0.30 AND 95 % CI excludes 0
- **INCONCLUSIVE:** 0.15 ≤ |d| ≤ 0.30 OR CI straddles 0 but mean(Δ) > 0
- **REFUTED:** |d| < 0.15 AND CI strictly contains 0

### F-PHASE1A-2-v2: J discriminates sleep states

- **Test:** Kruskal-Wallis H over {J_t : t ∈ state_k} for k ∈ {awake, nrem, transit, rem} within window
- **Statistic:** η²_H = (H − k + 1)/(N − k) where N = total windows, k = n_states
- **PASS:** η²_H > 0.06 (medium effect) AND p < 0.01
- **INCONCLUSIVE:** 0.01 ≤ η²_H ≤ 0.06 OR p ≥ 0.01
- **REFUTED:** η²_H < 0.01

### Anti-cheat declarations

1. No threshold adjustment is permitted between this pre-reg paper and B5 results.
2. If the B5 run discovers a coding bug requiring re-execution, the re-execution must be disclosed in the results paper with the bug, the fix, and the diff.
3. Even if Phase-1A-v2 PASSES both falsifiers on this dataset, the canonical claim per B4 §5 stands: **independent-dataset replication is required** before the adapted instrument can carry Phase-1B inference weight. A first-pass PASS on the same DANDI:000003 makes the instrument *candidate* only.
4. If Phase-1A-v2 REFUTES both falsifiers, then the additive-asymmetric-cap composition is also refuted for within-HPC rat LFP, and the next branch options become (A-deeper: cross-region or band-split) or (B: change substrate to affective-paradigm dataset) or (C: skip to human substrate).

---

## 4. Data slice (FROZEN, same as B4)

| Window | Used for | Source |
|---|---|---|
| 0–600 s | F-PHASE1A-1-v2 primary (n=871 PulseStim events available) | DANDI:000003 sub-YutaMouse41 stream |
| 4400–5000 s | F-PHASE1A-2-v2 primary (awake + nrem segments) | same |

No new data is being fetched. v2 re-uses the byte-identical LFP slices read in B4, so any v2-vs-B4 difference is purely instrument-driven.

---

## 5. Cross-references to canonical principles being applied

- **GTT-1** (canonical #27, Pass-67-B4): GILE True-Tralseness is the only un-maximizable-without-cost variable. v2's G* = 0.93 cap is its direct empirical instantiation.
- **UOP phase-transition model** (Pass-68-B1): J(G, H) = f(G) + g(H) mathematical specification; 4/4 Brandon predictions confirmed at model level.
- **TPI-1-F3** (Pass-70-B3): asymmetric specification (cap unique to G) is the canonical f-spec; symmetric specification was tested at model level and judged a mathematical tautology.
- **TLC-1** (canonical #40, Pass-74-B4): canonical mood-amplifier composition. v2 is positioned as a *generalization* of TLC-1 — when α → 0 and the log transforms linearize, J ≈ G + H (additive baseline); the B4 L×E composition is recovered by a different functional choice (multiplicative). The corpus does not retire TLC-1; v2 is a candidate variant for the rodent substrate specifically.
- **Pass-37 frozen-rubric precedent**: adapted-instrument runs must declare their pre-reg before execution; this paper is that declaration.
- **DBF-1 Discovery-Before-Framework candidate** (B3-surfaced): the L→G + E→H mapping is the framework-after-discovery move (B4 discovered cancellation; v2 maps the existing data into the canonical framework that doesn't cancel).
- **ASYMMETRIC #69**: both the refutation outcome from B4 and any PASS/REFUTE outcome from v2 will be reported in the headline; no spin.

---

## 6. Compute / cost / risk

- Streaming reuses same DANDI:000003 file; estimated 2 × ~50 s background streaming windows (PulseStim + states).
- LFP read is byte-identical to B4 so no incremental compute beyond the instrument step itself.
- $0 budget honored (no API calls, no compute spend).
- Risk: if J still shows ≈ 0 effect-size, the rodent-HPC substrate is wrong (not the composition), and branch (B) becomes the next-batch directive.

---

## 7. Decision tree post-B5 results

```
B5 result                                  → Pass-77-B6 direction
══════════════════════════════════════════════════════════════════
F1-v2 PASS  AND F2-v2 PASS                → Replicate on independent DANDIset (B-substrate-or-A-deeper) BEFORE
                                            claiming instrument-validated. Brandon-blocked dataset choice.
F1-v2 PASS  AND F2-v2 REFUTED             → Partial-win. State-discrimination still failing → branch (A-deeper)
                                            cross-region or band-split adaptation needed.
F1-v2 REFUTED AND F2-v2 PASS              → Stim-reaction-null is real (electrical ≠ affective per B4 §3.1 (i));
                                            state-discrimination success validates v2 partially. Move to
                                            affective-paradigm dataset (branch B).
F1-v2 REFUTED AND F2-v2 REFUTED           → Composition + substrate both wrong → branch (B) or branch (C).
                                            Brandon-blocked direction.
F1-v2 INCONCLUSIVE on either              → Run on independent dataset (B) for tie-break; no instrument
                                            adoption claim from inconclusive data.
```

---

## 8. Pre-reg lock signature

- This paper is committed BEFORE the runner_v2.py is executed.
- The runner_v2.py is committed in the same batch with hash recorded post-commit.
- B5 results paper will cite this paper as its pre-reg source and disclose all deviations.

End of pre-reg paper. Proceeding to runner_v2 implementation.
