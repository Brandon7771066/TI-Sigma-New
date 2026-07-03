# PASS 77 · B178 — OET (Organizational Emergence Theorem) first executed empirical test: whole-vs-sum-of-parts prediction on real dual-EEG

**Date:** 2026-07-03
**Status:** empirical test executed · HONEST NEGATIVE / INCONCLUSIVE · no new principle (count **80**)
**Falsifiers touched:** OET-F1, OET-F2 (both remain **OPEN** — see "What this does and does not resolve")
**Code:** `analyses/lcc_oet/oet_test.py` → `analyses/lcc_oet/results/oet_results.json`
**Data:** OpenNeuro **ds007471** dual-EEG hyperscanning (32 interacting pairs, 1278 aligned trials) — the same real dataset used in B164.

---

## 0. What was promised

B177 introduced **OET (Organizational Emergence Theorem, CANDIDATE)**: above a coupling threshold τ,

> `Error(𝒪) < Σᵢ Error(𝒞ᵢ)`

— a **whole**-organization model predicts the near future better than the **sum** of independent per-cluster ("part") models, and (the *only* new delta OET claims) the whole-beats-parts gain is **indexed by the LCC coupling crossing τ**. B177 explicitly offered "OET's `Error(𝒪)<ΣError` on existing data" as the first concrete step. This paper runs it.

**Credit, stated up front (EVD-1, no undercredit / no overclaim).** That a whole can predict better than the summed parts — synergy / macro-beats-micro — is **established**, not ours: Hoel, Albantakis & Tononi (PNAS 2013, causal emergence); Williams & Beer (2010, partial information decomposition / synergy); joint-Granger / transfer-entropy > 0 (Granger 1969; Schreiber 2000). The **only** thing OET adds is the **LCC-threshold-indexing** of that gain. So the test that matters for OET is *not* "does the whole ever beat the parts" (known to happen in synergistic systems) but "**does the gain appear, and is it gated by coupling crossing an LCC constant, on a real mood-relevant system**."

---

## 1. Design

Two brains = two **causal clusters** `𝒞_R, 𝒞_L` (per-trial ROI-mean band signals, 125 Hz, cached from B164's feature extractor). Per trial, per band (**theta**, **beta** — motor/attention bands most relevant to joint action):

- **PART model `𝒞ᵢ`:** AR(5) — predict brain *i*'s next sample from *i*'s **own** past only.
- **WHOLE model `𝒪`:** VAR(5) — predict each brain's next sample from **both** brains' past.
- **Out-of-sample throughout:** fit on the first 60 % of the trial, score one-step-ahead MSE on the last 40 %; z-scored on the train split so MSE is comparable across trials. (OOS is essential — an in-sample VAR *always* fits ≥ the AR by construction, which would rig the inequality.)
- `Error(𝒪) = MSE_R(joint) + MSE_L(joint)`; `Σ Error(𝒞ᵢ) = MSE_R(own) + MSE_L(own)`.
- `Δ = ΣError(𝒞) − Error(𝒪)` (`Δ > 0` ⇔ the OET inequality holds).
- Coupling `C` = inter-brain PLV (the LCC measure), per trial.

**Decisive #69 confound control.** Both brains hear the **same** tone sequence, so a joint model can beat the parts purely from **common auditory input**, with zero organizational coupling. So raw `Δ>0` is necessary-not-sufficient. We therefore recompute `Δ` on **cross-pair surrogates** (brain-R of pair A + brain-L of pair B, matched on tone+condition, never partners; the same null machinery as B164's `surrogate.py`). The interaction-specific effect is `Δ_real − Δ_surrogate`; only that survives the confound.

**LCC-threshold-indexing (the actual novelty):** (a) `corr(Δ, C)`; (b) at each candidate constant τ ∈ {0.414, 0.437, 0.6, 0.707, 0.854, 0.930}, contrast `Δ` for trials with `C ≥ τ` vs `C < τ`.

---

## 2. Results (n = 1278 trials, 32 pairs)

| band | C̄ (coupling) | Δ_real (norm. MSE) | frac trials Δ>0 | Δ_surrogate | interaction `Δ_real−Δ_surr` | p(real>surr) | corr(Δ,C) |
|------|------|------|------|------|------|------|------|
| **theta** | 0.093 | **+1×10⁻⁶** (≈0) | 0.749 | +1×10⁻⁶ | **0.0** | 0.34 (n.s.) | −0.035 |
| **beta**  | 0.044 | **−4.95×10⁻⁴** (worse) | 0.197 | −5.57×10⁻⁴ | +6.2×10⁻⁵ | 0.0018 | +0.019 |

**Threshold-indexing: UNTESTABLE.** Inter-brain PLV never approaches the candidate constants — C̄ ≈ 0.04–0.09, and **zero** of 1278 trials reach even the lowest τ = 0.414 in either band. So the `C≥τ` cell is empty for every candidate; the one claim OET actually adds **cannot be evaluated on this dataset**. `corr(Δ,C)` is ≈ 0 in both bands regardless.

---

## 3. Honest reading (#69, both directions)

1. **The raw OET inequality is not supported here.** In **theta** the whole beats the parts by a *negligible* +10⁻⁶ (reliably positive but practically zero); in **beta** the whole is **reliably worse** than the parts out-of-sample (Δ = −5×10⁻⁴, holds in only 20 % of trials, p(Δ≤0)=1.0) — adding the partner brain's past *hurts* one-step prediction (overfitting a channel that carries little cross-predictive information). A joint two-brain model does **not** beat two independent single-brain models at near-future prediction on this data.
2. **The interaction-specific effect is null-to-negligible.** Theta: `Δ_real − Δ_surr = 0` (p = 0.34, not significant). Beta: real is a hair less-negative than surrogate (+6×10⁻⁵, p = 0.0018) — statistically detectable but *practically negligible* and still leaves the whole **worse** than the parts. This is **not** OET support; it is consistent with B164's finding of common-input dominance and no interaction-specific coupling.
3. **The novelty is untested, not refuted.** Because coupling sits at the floor (≪ 0.414), the LCC-threshold-indexing — OET's sole original claim — **could not be tested**. This is a "cannot-run-the-decisive-part" outcome (like the Hilbert–Pólya operator test in the millennium working note), *not* a resolution. **OET-F1** (whole beats parts above τ) and **OET-F2** (the gain is coupling-indexed, not a fixed offset) both remain **OPEN**.
4. **Established macro-beats-micro is not contradicted.** Hoel 2013 / Williams & Beer 2010 hold in systems with genuine synergy; this dataset simply carries near-floor inter-brain coupling *at the ROI-mean band granularity measured here*. Two readings, both stated: **measurement-limitation** (ROI-mean single-trace PLV is a coarse coupling probe; finer multivariate coupling might reach τ) and **theory-limitation** (joint musical action at this granularity may not produce organizational emergence at all). We do not privilege either.

---

## 4. What this does and does not resolve

- **Does:** provides the first *executed* OET test and a reusable, confound-controlled harness (`analyses/lcc_oet/`). Establishes that, on ds007471, the **raw** whole-vs-parts inequality fails OOS and inter-brain coupling never reaches any LCC candidate constant.
- **Does not:** resolve OET. The indexing claim is untestable at this coupling floor. OET-F1/OET-F2 stay OPEN; the honest status is "**first test inconclusive for the novelty, negative for the raw inequality**," which is exactly the kind of new-risky-prediction outcome B177 required to keep the causation-broadening non-goalpost-moving (LCC-UNFALS-F1): OET *did* issue a falsifiable prediction and it *did* fail on its raw form here.
- **Next decisive test:** a system where inter-cluster coupling actually reaches the τ regime (e.g. a strongly-coupled physiological or task system, or a finer multivariate coupling estimator on hyperscanning data), so `C≥τ` is populated and the indexing claim can be evaluated rather than skipped.

**Count unchanged: 80.** No principle added or ratified; this is an empirical test of an existing candidate.

---

## References (real)
- Hoel EP, Albantakis L, Tononi G. "Quantifying causal emergence shows that macro can beat micro." *PNAS* 110(49):19790–19795 (2013).
- Williams PL, Beer RD. "Nonnegative decomposition of multivariate information." *arXiv:1004.2515* (2010).
- Granger CWJ. "Investigating causal relations by econometric models and cross-spectral methods." *Econometrica* 37(3):424–438 (1969).
- Schreiber T. "Measuring information transfer." *Phys. Rev. Lett.* 85(2):461–464 (2000).
- OpenNeuro ds007471 (dual-EEG joint-action hyperscanning).
