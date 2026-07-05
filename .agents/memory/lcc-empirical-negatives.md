---
name: LCC empirical tests (gate-first) — running record + how to run the next one
description: What the real-data gate-first tests of the LCC index / Radiant Cap have actually shown, and the durable method rules for the next dataset.
---

# LCC/UOP gate-first empirical tests

**Decision rule (pre-committed).** Pipeline = `group-signal gate → surrogate gate → LCC index (CV) → threshold → UOP/cap`. Every coupling metric must be **surrogate-corrected** (`ΔC = C_real − C_matched_surrogate`). **Do NOT test constants (√2−1, 0.437, cos²(π/8), radiant_cap √(1−e⁻²)) or the cap until all three pass:** (1) group-signal present, (2) real beats surrogate AND the *surrogate-corrected* signal still separates the outcome, (3) `L_hybrid` beats raw `C` in CV. Otherwise record an honest negative and move on.

## Outcome so far: three independent real-data negatives
- **OpenNeuro dual-EEG hyperscanning** — negative on every phase; inter-brain coupling consistent with common-input, not interaction-specific. (Detail: `lcc-uop-hyperscanning-empirical-test.md`.)
- **Depresjon actigraphy** (within-person circadian rhythm coupling → depression) — *partial* negative: a real actigraphy→depression signal exists (group-signal gate passes), but the surrogate-corrected coupling does NOT track depression and the hybrid index is *worse* than raw features. Constants gated out. Code: `analyses/lcc_depresjon/`.
- **User↔chatbot dialogue** (hh-rlhf + mt_bench, B189) — clean null: C+RAS≈C_only, hybrid ≤ chance. **New twist: the synthetic method-validation itself FAILED** (RAS misses ground-truth reciprocal coupling p=0.16 yet fires on common-input p<0.001) ⇒ the null is *explained* by the instrument, not merely observed. mt_bench too short (2 turns/speaker) to test at all. (Detail: `lcc-dialogue-tests.md`.)

## Durable lessons (not derivable from code)
- **The LCC hybrid AGGREGATION is a liability, not a feature.** On both datasets raw single features (or a plain multi-feature model) beat the `Λ=α·Σwᵢxᵢ+(1−α)·∏xᵢ^wᵢ` scalar — the aggregation can even invert the signal. Any future "L beats raw C" claim must clear this bar first.
- **Surrogate-correction is the killer, not signal absence.** Real temporal structure is trivially above chance; the honest test is whether the *beyond-linear / beyond-common-input* part (ΔC) tracks the outcome. It hasn't. Always report the surrogate-CORRECTED group separation, never just "real > null."
- **Separate the substrate positive from the LCC negative (#69).** A dataset can carry a genuine, literature-consistent effect (e.g. actigraphy→depression) while still being a clean negative for the LCC index/constants. State both; conflate neither.
- **The Radiant Cap has never had an admissible confirmatory test** — gated out every time. Any concave curve found in ungated data (interior-optimum argmax near the cap) is an artifact to DECLINE, not evidence.
- **`1/(√2φ)≈0.437`** (HAN-1 "golden-orthogonal") remains a resonance with zero admissible tests.
- **Method guards that mattered:** fit ALL preprocessing (min/max normalization, scalers, the index construction) on train folds only — no whole-sample normalization before CV. Make the gate's pass-criterion in code literally match the written protocol (both surrogate reality checks AND the corrected group-separation).

## Practical / infra
- **Depresjon download:** `https://datasets.simula.no/downloads/depresjon.zip` (NOT `/depresjon/...zip`). Simula serves a broken cert chain (missing local issuer) → `curl -k` is acceptable for this public dataset. Extracts to `data/data/` (`scores.csv` + `condition/*.csv` ×23 + `control/*.csv` ×32; per-minute activity). `scores.csv`: afftype 1=BPII/2=unipolar/3=BPI; madrs1/madrs2 = MADRS start/end; controls have blank scores.
- **Env:** statsmodels NOT installed — numpy/scipy/sklearn only (AR via `np.linalg.lstsq`, AUC via sklearn). Background nohup does not survive tool calls; run within the timeout.
- **Next-run priority (still OPEN):** physiological-synchrony→group-cohesion (ECG/IBI, ΔC vs matched surrogate — strongest prior); heart-rate-sync→decision-correctness (closest to GILE-Truth); a DANDI/NWB dataset with an explicit intervention/state-transition (gives LCC the pre/post regime structure the within-person tests lacked). Need a verified-open mirror for the Tomashin/Gordon synchrony corpora — not directly downloadable as of this writing.
