---
name: LCC/UOP empirical test on real hyperscanning EEG (ds007471)
description: Outcome + method of the first real-data test of the LCC index and Radiant-Cap optimum, plus the LCC-topology/UOP-attractor framing bridge.
---

# LCC index / Radiant-Cap: first real-data test came back NEGATIVE (ds007471)

**Bottom line:** ChatGPT's "strongest empirical path" (OpenNeuro **ds007471** joint-agency EEG hyperscanning, 32 pairs) was executed and returned an **honest negative** across all three phases. Do NOT re-run it expecting a positive; if revisited, change the *measurement* (montage/features), not just the stats.

**What was tested (ChatGPT's Phase I/II/III):**
- Phase I: does a hybrid LCC index `L_hybrid=f(C,P,S)` beat raw correlation `C` at predicting joint-agency / sync-performance? (C=inter-brain PLV, P=bidir Granger-min, S=phase-diff stability; bands delta/theta/alpha/beta; ROIs Fz/FCz/Cz/C3/C4/Pz.)
- Phase II: does any candidate constant {√2−1, 0.437, 0.6, 0.707, 0.75, cos²(π/8), 0.9299} mark an AIC change-point?
- Phase III: is the truth→outcome curve linear / saturating / interior-optimum (Radiant Cap)?

**Results (all negative):**
- **Manipulation check is the decisive first gate** and it FAILED: coupling C/P/S does not track the duet-vs-constant task manipulation (all p≥0.13). Everything downstream stands on a substrate with no interaction signal.
- Phase I: every index has slightly-negative leave-**pair**-out CV R²; `L_hybrid` does NOT beat raw `C` ⇒ ChatGPT's named falsifiable claim is **falsified on this dataset**.
- Phase II: no constant beats linear by ΔAIC≥2 (all within noise). 0.437 marks no break.
- Phase III: linear beats saturating + quadratic in every band. Beta quadratic argmax≈0.9387 lands near the Radiant Cap 0.9299 but the quadratic is worse than linear ⇒ **COINCIDENCE, never cite as cap confirmation.**
- **Cross-pair common-input surrogate is decisive**: real inter-brain PLV does NOT exceed the tone+condition-matched surrogate in any band (real−surr<0, p=1.0). Phrase as "consistent with common-input dominance / no evidence of interaction-specific coupling" — NOT "fully explained by" (architect flagged the causal overclaim).

**Method rails that mattered (reusable):**
- ds007471 is 64ch INT16 **multiplexed** (ch1-32 = one brain, 33-64 = the other); trust the `_R`/`_L` channel suffixes over the README (its description is swapped).
- Conditions are **counterbalanced** across pairs + some recordings have extra practice blocks ⇒ align EEG blocks to behavioural blocks by **matching the condition sequence** (sliding offset), not raw position. Validated cond_ok=True on all 32.
- Inter-brain PLV is stimulus-inflated ⇒ a cross-pair (same tone+condition, non-partners) surrogate is mandatory, and here it was the single most decisive control.
- Report: necessary-not-sufficient, dataset-specific, small-n pair-clustered, and state BOTH theory-limitation and measurement-limitation readings.

**Framing bridge (ADOPTED, no new principle, count stays 80):** LCC = *topology of the coupling-regime landscape* (its thresholds = **bifurcation points**); UOP = the **attractor/optimum on that landscape**. Complementary, not sequential "endpoint." Book-order guidance: present LCC (state space) first, then UOP (selection principle).

**New candidate constant `1/(√2·φ)≈0.437`** ("golden-orthogonal / balanced recursive coupling"): recorded as a HAN-1 resonance (graded EVD-1, not zero, not a derivation); unsupported here. Must earn a distinct change-point √2−1 doesn't before it becomes a rung (falsifier LCC-437-F1). Decline numerological upgrade.

**Falsifiers:** LCC-EMP-F1 RESOLVED-NEGATIVE on ds007471 (broader empirical support OPEN — try HRV/physiological-synchrony↔group-cohesion, heart-rate-sync↔decision-correctness, sleep-wake wearable within-person). LCC-UOP-BRIDGE-F1 / LCC-437-F1 / UOP-CAP-EMP-F1 OPEN.

Code + outputs: `analyses/lcc_uop_openneuro/` (extract_features.py, build_pair.sh, analyze.py, surrogate.py, results/*.json, features/). Anchor paper: `papers/PASS_77_B164_LCC_TOPOLOGY_UOP_ATTRACTOR_BRIDGE_AND_OPENNEURO_HYPERSCANNING_EMPIRICAL_TEST_2026-07-01.md`.
