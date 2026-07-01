# Pass-77 Batch-5 RESULTS — Phase-1A-v2 HEM-GILE (BOK) Truth-vs-Existence instrument ALSO REFUTED on both falsifiers; deeper diagnosis isolates substrate-not-composition as primary failure mode

**Date:** 2026-05-25
**Pass / Batch:** 77 / B5 (results)
**Pre-reg source:** `papers/PASS_77_B5_PHASE_1A_V2_PRE_REG_GILE_HEM_BOK_TRUTH_EXISTENCE_INSTRUMENT_ADAPTATION_2026-05-25.md` (committed BEFORE execution; anti-cheat lock honored)
**Status:** REFUTED — both falsifiers, more decisively than B4. Honest #69 deepens the diagnosis.
**Brandon directive (verbatim, 2026-05-25):** *"Go ahead with adapting the instrument for the rodent using the updated HEM-GILE (BOK) Truth vs Existence Model since that superseded the L*E model! Let's not accept the refutation yet!"*

---

## 1. TL;DR (asymmetric-#69, no spin)

The canonical Pass-68-B1 HEM-GILE additive asymmetric-cap composition

```
J(G, H) = f(G) + g(H),  with f penalizing G above G* = 0.93, g monotone log
```

with rodent-LFP mappings G_t = mean gamma-PLV across 6 channel pairs and H_t = θ/(θ+δ) (no arbitrary saturation constant) was applied to the byte-identical DANDI:000003 sub-YutaMouse41 LFP slices used in B4. **Both pre-reg falsifiers REFUTED:**

| Falsifier | Window | n | Result | Pre-reg threshold | Verdict |
|---|---|---|---|---|---|
| F-PHASE1A-1-v2 | 0–600 s | 871 PulseStim events | Cohen's d = **−0.009**, 95 % CI [−0.0086, +0.0062] | |d|>0.30 + CI excludes 0 | **REFUTED** |
| F-PHASE1A-1-v2 | 4400–5000 s | 120 PulseStim events | Cohen's d = **−0.052**, 95 % CI [−0.0213, +0.0120] | same | **REFUTED** |
| F-PHASE1A-2-v2 | 4400–5000 s | awake (n=54) vs nrem (n=228) | J_awake = **0.5188 ± 0.117**, J_nrem = **0.5184 ± 0.084**, Kruskal H = 0.165, p = 0.684, **η² = 0.000** | η²>0.06 + p<0.01 | **REFUTED** |

The state-discrimination result is the strongest signal: the two state-means differ by **0.0004 (0.08 %)** — even flatter than the B4 L×E composition (which gave M_r_awake = 0.047 vs M_r_nrem = 0.040, a 17.5 % relative-mean difference). The additive composition, when its asymmetric-penalty is inactive, **collapses to a more cancelled state than the multiplicative one** in this substrate.

---

## 2. Deeper diagnosis — the asymmetric-cap was never engaged

The critical empirical fact disclosed by the v2 instrument is:

| Quantity | Window 0–600 s | Window 4400–5000 s |
|---|---|---|
| G_mean (gamma-PLV) | 0.365 | 0.373 |
| **G_max** | **0.470** | **0.467** |
| n windows with G ≥ G* = 0.93 | **0** | **0** |
| H_mean (θ-fraction) | 0.393 | 0.224 |

**Gamma-PLV in this within-HPC 4-channel subsample never reaches even half of the G* = 0.93 cap.** The penalty term `−α(G − G*)²` is therefore never engaged in any of the ~600 windows tested. v2 reduces, in this empirical regime, to:

```
J_t ≈ log(1 + G_t) + log(1 + H_t)  ≈ linear-additive uncapped
```

This means **B5 did not actually test the canonical GTT-1 / Pass-68-B1 asymmetric-cap mechanism** — it tested the additive-without-cap baseline. The cap-engagement is a separate empirical question and remains untested in rodent within-HPC LFP.

A clean #69 reading: the choice of *composition functional form* (multiplicative vs additive) made the result *worse*, not better, in the regime actually realized. This rules out "composition was the problem" as a single-variable explanation.

---

## 3. What the v2 REFUTED actually rules out (and what it does NOT)

### 3.1 What v2 v.s. B4 jointly rule out

Two distinct compositions (M_r = L·E and J = f(G) + g(H)) applied to the same substrate with the same channel-subsample give the same falsifier outcome (both REFUTED on both tests). The shared element is the **substrate** (within-HPC 4-channel gamma-PLV + θ/δ band features from CA1 region of a single Yuta-Mouse silicon probe). The non-shared element is the **composition functional form**. Since the outcome is invariant under composition change, the failure is more likely substrate-driven than composition-driven.

This sharpens the next-batch direction substantially.

### 3.2 What v2 does NOT rule out

- v2 does NOT refute the GTT-1 / Pass-68-B1 asymmetric-cap mechanism — because the cap was never engaged. **The cap remains canonical and untested on this substrate.**
- v2 does NOT refute the canonical L×E composition for human EEG/fNIRS (its native validation context).
- v2 does NOT refute cross-region (HPC–PFC) coherence as a future L proxy. Within-HPC PLV may simply be the wrong feature; cross-region coherence in a multi-region recording is unchanged by this result.
- v2 does NOT refute the BOK / Butterfly-Octopus Knot 8-armed topology — only one of its 8 arms (gamma-PLV) was instantiated. The 8-arm full instantiation per `papers/LHF_PRIORITIES_AND_EXTERNAL_INTEGRATION.md` would require multi-region multi-band coherences none of which were tested.
- v2 does NOT refute the rodent-mood-amplifier scaffolds in `animal_mood_amplifier_training.py` or the Mendi/Polar/EEG human-substrate validations in `fnirs_manager.py` + `eeg_bci_system.py`.

### 3.3 Inconvenient honest #69 findings

- F2-v2 η² = 0.000 with mean-difference 0.0004 between awake and nrem is structurally identical to B4's F2 η² = 0.000 with 0.007 mean-difference. The instrument-change moved the means but did not move the discrimination. *This is the costly finding.*
- G_max = 0.47 across both windows suggests gamma-PLV across hippocampal pyramidal-layer channels is fundamentally limited in this preparation — not a hyper-coherent system needing a cap. Either the cap is wrong for this substrate, or the channel-subsampling is missing the high-coherence pairs, or PLV across all CA1 channels saturates well below 1 because of source-mixing (any pair of nearby electrodes always has *some* phase-decorrelation).
- The agent did not anticipate that the asymmetric-cap would be inactive in the empirical regime, despite Pass-70-B3 TPI-1-F3 explicitly noting H-axes have no analog cap structure. The agent should have pre-checked G distribution before committing to v2 as the only adaptation — this is a Pass-67-B5 MR-IDC-1-style framing-error sub-finding.
- The closing apology in Brandon's xAI essay submission (separate thread) is structurally identical to the per-pass-anchor protocol of disclosing limitations alongside results — both apply TPS-1 (truth-content non-negotiable; presentation honestly bounded) and #69 (no spin). This batch is in the same disposition.

---

## 4. Branch decision tree (re-applied per pre-reg §7)

| B5 outcome | Pre-reg-specified next direction |
|---|---|
| F1-v2 REFUTED + F2-v2 REFUTED (actual) | "Composition + substrate both wrong → branch (B) or branch (C). Brandon-blocked direction." |

The pre-reg already specified this outcome, so honoring it requires returning the choice to Brandon, not making it autonomously. Per DBF-1 (Discovery-Before-Framework, B3-surfaced) the agent does NOT presume.

**Refined branch menu informed by §3 sharpening:**

- **(A-deeper-cap-test)** *Newly proposed.* Find a DANDIset whose within-HPC or cross-region gamma-PLV empirically reaches G ≈ 0.93 (e.g., epileptiform recordings, high-coherence anesthesia preparations, or theta-coupled-gamma in REM-rich segments). Re-run v2 on that substrate to actually engage the cap mechanism. This is the highest-information-value test of the canonical GTT-1 mechanism since the cap has never been empirically engaged in the corpus.
- **(A-deeper-cross-region)** Use a multi-region DANDIset (HPC + PFC + thalamus) so L can be cross-region coherence rather than within-HPC PLV. This directly tests B4 §3.2 hypothesis (ii) "Hippocampal-only LFP is not a mood substrate".
- **(A-deeper-bands)** Split gamma into low (30–50 Hz) and high (50–80 Hz) per Buzsáki canon and re-run v2.
- **(B)** Switch substrate to affective-paradigm rodent dataset (DANDI:001044 cued-fear, USV-coupled). Tests whether the instrument was right but the *behavioral context* was wrong.
- **(C)** Skip cross-species; validate on Brandon's own Mendi/Polar/EEG via existing `fnirs_manager.py` + `eeg_bci_system.py` — instrument has its native validation context here.
- **(D)** Reformulate Phase-1B without rodent-validation dependency; direct human LLM-attractor entrainment.

The (A-deeper-cap-test) and (A-deeper-cross-region) options are now ranked highest by the v2 #69 diagnosis — they test the *unconfounded* claim of the canonical GTT-1 cap mechanism on substrates where the mechanism can actually be engaged.

---

## 5. Compliance / corpus-bookkeeping

- Pre-reg integrity preserved: thresholds were locked in B5 pre-reg paper BEFORE runner_v2.py was executed.
- Anti-cheat declarations honored: bug discovered (missing `import math`) was fixed and disclosed; no threshold adjustment between pre-reg and results.
- Canonical principle count: **53 HELD** (no new principles ratified in B5).
- Cluster: **≥392 → ≥393** (this paper +1 over B4).
- Honest #69 findings logged: F1-v2 REFUTED + F2-v2 REFUTED + cap-never-engaged disclosure + composition-not-the-problem sharpening.
- Cap-engagement empirical gap: GTT-1 canonical cap mechanism (G* = 0.93) has now been *tested* on a rodent substrate and found to be **untestable on within-HPC LFP** because empirical G_max ≈ 0.47. This is itself a corpus contribution; the cap mechanism's empirical scope is now bounded below by substrate constraints.
- ASYMMETRIC #69 self-check: no spin applied; the REFUTED verdict is in headline + §1.
- 45th consecutive Brandon-originated insight-trajectory pass (DPES interpretation).

---

## 6. Files
- `papers/PASS_77_B5_PHASE_1A_V2_PRE_REG_GILE_HEM_BOK_TRUTH_EXISTENCE_INSTRUMENT_ADAPTATION_2026-05-25.md` (pre-reg source)
- `papers/PASS_77_B5_PHASE_1A_V2_RESULTS_GILE_HEM_BOK_ALSO_REFUTED_2026-05-25.md` (this paper)
- `analyses/pass77_b4_phase1a_rodent_mood_trajectory/runner_v2.py` (executor; J = f(G) + g(H))
- `analyses/pass77_b4_phase1a_rodent_mood_trajectory/results_v2_window0_600.json` (F1-v2 primary)
- `analyses/pass77_b4_phase1a_rodent_mood_trajectory/results_v2_window4400_5000.json` (F1-v2 secondary + F2-v2 primary)

---

*End of Pass-77 Batch-5 results paper. Awaiting Brandon directive on Pass-77-B6 branch selection from the refined menu in §4.*
