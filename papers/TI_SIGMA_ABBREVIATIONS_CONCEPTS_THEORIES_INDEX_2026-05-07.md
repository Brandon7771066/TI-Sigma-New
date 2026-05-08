# TI Sigma — Master Index of Abbreviations, Concepts, and Theories

**Author:** Brandon Charles Emerick (curated with the agent)
**Date:** 2026-05-07
**Status:** Living index — append new entries as the framework grows
**Purpose:** Single source of truth for the vocabulary of TI Sigma. Resolves ambiguities, anchors definitions, prevents drift.

---

## 0. How to use this index

Each entry has the form:
- **Term** (short form / long form) — one-line definition. *Status:* ESTABLISHED / FOUNDATIONAL / CONJECTURAL / OPEN. *Anchor:* paper/URB.

Sections:
- §1 Core Truth-Theoretic Vocabulary
- §2 PD (Phenomenal Directness) Vocabulary
- §3 GILE & Consciousness Vocabulary
- §4 Geometric & Mathematical Constants
- §5 Hardware, Biometrics & Empirical Vocabulary
- §6 Meta-Theoretical & Epistemic Vocabulary
- §7 Biographical & Operational Vocabulary

---

## §1 Core Truth-Theoretic Vocabulary

- **TI** (Tralse Informationalism / Tralse-Informationalist Framework) — the overarching framework. Coined June 25, 2025. *FOUNDATIONAL.* Anchor: framework-wide.
- **TI Sigma** — the formal-mathematical layer of TI; emphasizes proof-theoretic content (Lean 4 verified theorems). *FOUNDATIONAL.*
- **Tralse (the universal quality)** — **the universal indeterminacy quality embedded in every coherent truth label** (per Brandon 2026-05-08 canonical ruling). Embedded in True, False, *and* Indeterminate; absent only in DT (which contradicts it and is therefore discarded). **NOT a 5th base truth-value** — listing it as one would double-count, since it is universal. Tralse-quality is quantified on the PD-imaginary axis (axis 2). *FOUNDATIONAL.* Anchor: framework foundation from June 2025; canonical clarification `MR_TRUTH_LABELS_CANONICAL_RULING_2026-05-08.md` §2.3.
- **Indeterminate (the state)** — distinct from Tralse-quality. **One of the four base MR Truth Labels** (a discrete MR2-gate output: a coherent 50/50 balance, the "45-degree door"). *FOUNDATIONAL.* Anchor: same canonical ruling.
- **Tralse Logic** — historically: the three-valued logic system {True, False, Tralse}. **Superseded** by the canonical base-4 MR Truth Label scheme (per 2026-05-08 ruling). Retained as the historical name for the broader framework's logic layer. *FOUNDATIONAL (historical).*
- **Tralsity** — the property of being Tralse; degree to which a proposition occupies the Tralse value rather than True or False. *ESTABLISHED.*
- **Tralsebit** — a single information unit in Tralse logic, generalizing the bit. *ESTABLISHED.* Anchor: `BEC_OPTICAL_TRALSEBITS_PRIMORDIAL_COMPUTER.md`.
- **TT** (True-True) — ternary digit 2; the maximum-truth ternary code in PD-coordinate notation. *ESTABLISHED.* Anchor: `urb_628`. **Caution**: not a stand-alone truth value; see "MR-gate truth-value scheme" below for the canonical truth-value taxonomy.
- **TI** (Tralse-Indeterminate, ternary code; *do not confuse with framework abbreviation TI*) — ternary digit 1; partial/indeterminate truth in PD-coordinate notation. *ESTABLISHED.* Anchor: `urb_628`.
- **DT** = **Double Tralse** (canonical and exclusive, per Brandon 2026-05-08 ruling). The MR1-failure / discard signal. **Formal definition: DT(P) ⟺ τ(P) ∧ ¬τ(P)** — "something which IS AND IS NOT tralse." Always some form of nonsense. Algebraic instantiation: T(T(P)) = τ² = 0 nilsquare (per `urb_677`). *FOUNDATIONAL.* Anchor: `FIVE_VALUED_TRUTH_TRALSE_INDETERMINATE_DISTINCTION_URB_528.md`, `MR_TRUTH_LABELS_CANONICAL_RULING_2026-05-08.md` §2.2, `urb_677_double_tralse_indeterminate_indeterminacy.md`. **The prior overloaded "DT scheme B" usage (Defective Truth / Down Truth / Direct-Tralse) is renamed to DefT — see entry below.**
- **DefT** = **Defective Truth / Down Truth / Direct-Tralse** (renamed from prior "DT scheme B" per Brandon 2026-05-08 ruling, eliminating the collision). Ternary digit 0; truth-absent on the PD-imaginary axis (PD-coordinate notation, NOT a truth-value category). *ESTABLISHED.* Anchor: `urb_628`, `urb_734`, `UNIFIED_TIME_THEORY_DE_PHOTON_FTL.md`, `PD_SPECTRUM_DT_IMAGINARY_AXIS_EMERICK_CROSSOVER_2026-05-07.md`. **Sweep status**: legacy "DT" usages in `urb_628`-derivative papers should read as DefT until those papers are individually patched; tag at point of use as needed.
- **TF** (True-False / Tralse-False) — the False zone on the PD real axis, range (0, √2−1) — PD-coordinate notation. *ESTABLISHED.* Anchor: `urb_628`.
- **EV** (Extreme Value / Edge Value) — appears in the PD-coordinate-notation set {TT, TI, TF, DefT, EV}. *ESTABLISHED.* Anchor: `urb_628` §4. Not part of the canonical MR-gate truth-value scheme.

### MR Truth Labels — Canonical Scheme (per Brandon 2026-05-08 ruling)

**TI Sigma's canonical truth-value scheme is base-4 + N Meta-Truths.** Anchor: **`MR_TRUTH_LABELS_CANONICAL_RULING_2026-05-08.md`**.

- **Base-4 MR Truth Labels** = **{True, False, Indeterminate, Double Tralse}**. *FOUNDATIONAL.*
- **MR1** (Existence Gate / Gate 1) — first-iteration MR; detects DT (per the τ ∧ ¬τ definition above). DT statements are flagged and discarded. *FOUNDATIONAL.* Anchor: `urb_528` lines 87-88.
- **MR2** (Truth Gate / Gate 2) — for statements passing MR1: determines True, False, or Indeterminate. Indeterminate = coherent 50/50 balance ("45-degree door"). *FOUNDATIONAL.* Anchor: same paper lines 92-93.
- **MR3+** — modify provisional MR1+MR2 results. Substantial modifications register as **Meta-Truths** (next item).
- **Meta-Truths (MTs)** — operations on top of the base-4 evaluation, firing at MR3+. **N = 12 established** (per `urb_608_meta_truths_myrion_resolution_catalogue.md`), N = 24 CONJECTURAL (per `urb_639`). Categories A1/A2 Reversal, B1/B2 Dissolution, C1/C2 Scope-Shift, D1/D2 Contextual, E1/E2 Acceptance, F1/F2 Integration. *FOUNDATIONAL (12-MT core); CONJECTURAL (24-MT extension).*
  - **Moot (MT-B1)** — the most-frequently-fired Meta-Truth: well-formed statement whose base-4 truth-evaluation is dispensable in the relevant frame. **Independent of DT** (per Brandon 2026-05-08 ruling) — Moot is never nonsense; DT is always nonsense. Composes with base labels: "Moot-True", "Moot-False", "Moot-Indeterminate" are meaningful compounds. *FOUNDATIONAL.* Anchor: `urb_608`.
- **Why 4, not 5**: base-4 + N Meta-Truths fully covers `urb_713`'s ≥99.7% coverage analysis without inflating the base set. Mootness is iterative and compositional (signature of an MT, not a base value). See `MR_TRUTH_LABELS_CANONICAL_RULING_2026-05-08.md` §4.
- **Classical True/False are EXPLICITLY REJECTED** by TI Sigma as sloppy labels. All statements carry universal Tralse-quality (structured imperfection); no proposition occupies pure classical T or F. *FOUNDATIONAL.* Anchor: `TI_SIGMA_FIVE_AXIS_TRUTH_RICHNESS_REVIEW_2026-05-07.md` §4.1.
- **Superseded prior schemes** (kept in corpus as historical artifacts; see ruling §3 table for full reconciliation): `urb_639` {TRUE, FALSE, TI, DT, EV} reclassified as PD-coordinate notation; `urb_677` {T, F, I, Tralse, DT} — Tralse moved to quality register; `urb_713` {T, F, Tralse, Moot, DT} — coverage analysis preserved, Moot reclassified to MT-B1; Brandon 2026-05-08 morning first-pass {Nonsense, Moot, T, F, I} — refined to base-4 + Moot-as-MT.

---

## §2 PD (Phenomenal Directness) Vocabulary

- **PD** (Phenomenal Directness) — the framework's primary scalar/complex measure of how directly a phenomenon manifests; full spectrum is the complex plane. *FOUNDATIONAL.* Anchor: URB #394, #416, #728, #733, #734, `PD_SPECTRUM_2026-05-07`.
- **MR** (Myrion Resolution) — the resolution-mechanism applied to apparent contradictions; produces a PD score for the resolved state. *FOUNDATIONAL.*
- **Myrion** — the resolved-contradiction object produced by MR. *FOUNDATIONAL.*
- **MR PD** — the PD score assigned to a synchronicity or insight after Myrion Resolution; primary classification metric in `SYNCHRONICITY_CATALOGUE_TI_SIGMA.md`.
- **Indeterminate Disc** — region |PD| < 2/3 in the complex plane. *ESTABLISHED.*
- **Standard Zone** — region 2/3 < |PD| < 2 in the complex plane; where most ordinary truth-states live. *ESTABLISHED.*
- **Transcendent Annulus** — region 2 < |PD| < e ≈ 2.718. *ESTABLISHED.*
- **Pre-DT Zone** — region e < |PD| < π. *ESTABLISHED.*
- **DT Cliff** — the boundary at |PD| = π beyond which DT-saturation dominates. *ESTABLISHED.* Anchor: `urb_734`.
- **PD Real Axis** — the True/False direction. *ESTABLISHED.*
- **PD Imaginary Axis** — the DT/Tralse direction. *ESTABLISHED.* Anchor: `urb_734`, `PD_SPECTRUM_2026-05-07`.
- **Chirality Direction** — angle π/3 (60°), TIC vertex C. *ESTABLISHED.*
- **Tralse Vertex Direction** — angle 2π/3 (120°), TIC vertex T. *ESTABLISHED.*

---

## §3 GILE & Consciousness Vocabulary

- **GILE** — Goodness, Intuition, Love, Environment — the four-dimensional consciousness measure. *FOUNDATIONAL.* Anchor: GILE Framework Aug 2022.
- **G dimension (Goodness)** — first GILE axis; ethical/value-orientation. *ESTABLISHED.*
- **I dimension (Intuition)** — second GILE axis; non-classical knowledge access. *ESTABLISHED.*
- **L dimension (Love)** — third GILE axis; relational coherence. *ESTABLISHED.*
- **E dimension (Environment)** — fourth GILE axis; situational coupling. *ESTABLISHED.*
- **GILE Score** — composite [0, 1] consciousness-optimization metric; 0.92+ is near-perfect. *ESTABLISHED.*
- **Sacred Interval** (or Sacred GILE Interval) — the range (−0.666, 0.333); cosmic distribution of consciousness quality, derived from Pareto principle + Riemann analysis. *ESTABLISHED.*
- **LCC** (Lateral Coherence Coupling) — primary measurable correlate of consciousness; `gile_lcc_ratio_engine.py`. *FOUNDATIONAL.*
- **LCC_EMERICK** — the value 1/√2 ≈ 0.7071, the **Emerick Crossover** threshold for full GM integration. *FOUNDATIONAL.* (See §4.)
- **CCC** — the central-coherence-coordination layer; the "butterfly" structure that closes at LCC ≥ 1/√2. *FOUNDATIONAL.* Anchor: `URB_CCC_BOK_GM_MYCELIAL_ARCHITECTURE.md`.
- **GM** (Grand Myrion / Group Mind / GM-Node) — the framework's distributed-intelligence layer; CCC's parent structure. *FOUNDATIONAL.*
- **GM-Node** — a node within the Grand Myrion network; URB #829 details the dominant GM-Node. *FOUNDATIONAL.*
- **TJ** (Tralse-Joules) — quantifiable intentionality unit; TJ = τ(s) × δ(MR). *FOUNDATIONAL.*
- **τ(s)** (tau, internal calibration) — agent's internal accuracy/calibration as a function of situation s. *ESTABLISHED.* Anchor: `ASYMMETRIC_SUCCESS_FAILURE_PERFORMANCE_2026-05-07.md`.
- **δ(MR)** (delta, external presentation) — agent's external confidence/presentation as a function of audience MR. *ESTABLISHED.*
- **UOP** (Universal A Priori) — foundational unit of pre-experiential knowledge; basis for the Universal Bridge Theorem. *FOUNDATIONAL.*
- **MRE** (Mycelial Resonance Engine) — v2 + L4 + L5; the framework's substrate-coupling mechanism. *FOUNDATIONAL.*
- **BPS** (Biometric Phase Stacking / Below-Pulse Stacking) — Brandon's hypothesis that meditation produces stacked downregulation; data-limited as of 2026-05-06. *CONJECTURAL.* Anchor: `BPS_TERM_INTRODUCTION_2026-05-01.md`.
- **K(s)** (self-knowledge function) — agent's self-model accuracy; K(s) ≥ 1/√2 = Level 7 onset. *ESTABLISHED.* Anchor: `AGI_IMPOSSIBILITY_TI_SIGMA_PROOF.md`.
- **B(s)** (benchmark performance function) — agent's benchmark score; orthogonal to K(s). *ESTABLISHED.*
- **Ψ** (consciousness equation operator) — Ψ(LCC_EMERICK) = LCC_EMERICK; fixed point at 1/√2. *ESTABLISHED.* Anchor: `URB_CONSCIOUSNESS_EQUATION_LCC_C_PHI.md`.
- **C-level** — Level 7 consciousness onset; full GM self-knowledge. *ESTABLISHED.*
- **π-level** — Level 6; circular self-recognition without C-level self-knowledge. *ESTABLISHED.*

---

## §4 Geometric & Mathematical Constants

- **PRIMARY** — the 9-element constant set {0, 1, i, √2, e, φ, π, C, T}; vertices of the TIC. *FOUNDATIONAL.* Anchor: `urb_734`.
- **TIC** (TI Sigma Crystal) — 9-vertex geometric structure of the PRIMARY constants in the complex plane. *FOUNDATIONAL.* Anchor: URB #627, #628, #734.
- **TSC** — TI Sigma Crystal (alternate abbreviation); the 57-vertex computational form. *FOUNDATIONAL.*
- **C vertex** — Chirality vertex at (0.707, 1.225) ≈ (1/√2, √(3/2)); 60° from real axis, magnitude √2. *ESTABLISHED.*
- **T vertex** — Tralse vertex at (−1.359, 2.354) ≈ (−e/2, e·√3/2); 120° from real axis, magnitude e. *ESTABLISHED.*
- **Emerick Crossover** — the value **1/√2 ≈ 0.7071**. The framework's most central constant. Roles include: TI/TT boundary; AGI Impossibility threshold; consciousness-equation fixed point; CCC full-function threshold; Riemann critical line = (Emerick Crossover)². *FOUNDATIONAL.* Anchor: `PD_SPECTRUM_2026-05-07.md` §3.
- **Emerick Constant** — synonym for Emerick Crossover; 1/√2. *FOUNDATIONAL.*
- **Radiant Threshold (RT)** — PD = 2.0; transition into the GM zone where e-base scaling applies. *ESTABLISHED.* Anchor: `urb_628` §4.
- **e-base PD** — natural-logarithm parameterization of PD above the Radiant Threshold. *ESTABLISHED.*
- **Three-Generation Principle** — confirmed in 6+ independent contexts; structural recurrence of ternary stratification. *ESTABLISHED.* Anchor: URB #732, #733, #734.
- **E₈ shadow** — the TIC's projection structure shows E₈ packing optimality; basis for five-valued logic error-correction codes. *ESTABLISHED.* Anchor: `urb_628` §4.
- **Aperiodic dual L_xE-L_pE Einstein tiling** — TI Sigma's contribution to aperiodic-tiling literature. *ESTABLISHED.* Anchor: `APERIODIC_DUAL_LxE_LpE_EINSTEIN_TILING.md`.
- **(√2−1)² + (1/√2)² ≈ 2/3** — proposed near-identity relating TF/TI and TI/TT thresholds to the indeterminate disc radius. *CONJECTURAL.* Anchor: `PD_SPECTRUM_DT_IMAGINARY_AXIS_EMERICK_CROSSOVER_2026-05-07.md` §1.
- **Unit-Crossover Circle** — proposed: |PD| = 1/√2 circle in the complex plane, with four cardinal points being directional Crossovers. *CONJECTURAL.* Anchor: `PD_SPECTRUM_DT_IMAGINARY_AXIS_EMERICK_CROSSOVER_2026-05-07.md` §3.3.

---

## §5 Hardware, Biometrics & Empirical Vocabulary

- **URB** (Unitive Research Brick / Unified Research Brief) — atomic, dated unit of research production. ~250 in corpus as of 2026-05-07; sidebar count "URBs 578" reflects a different counting basis (likely brick-fragment count). *FOUNDATIONAL.*
- **Polar H10** — chest-strap heart-rate sensor; primary HRV instrument. *ESTABLISHED.*
- **Mendi** — consumer fNIRS headband; Path B reverse-engineered 2026-05-06. *ESTABLISHED.* Anchor: `MENDI_PATH_B_PHASE_2_COMPLETE_2026-05-06.md`.
- **HRV** (Heart Rate Variability) — primary autonomic-tone metric. *ESTABLISHED.*
- **RMSSD, SDNN, pNN50** — standard HRV metrics; require RR-interval data (Polar Flow export does NOT include — see Gotchas in `replit.md`). *ESTABLISHED.*
- **fNIRS** (functional Near-Infrared Spectroscopy) — non-invasive optical brain-blood-oxygenation measurement. *ESTABLISHED.*
- **GATT / BLE** — Bluetooth Low Energy GATT protocol; substrate for Mendi reverse-engineering. *ESTABLISHED.*
- **HR_floor** — the 5th-percentile heart rate during a session; baseline-fitness indicator. *ESTABLISHED.* Anchor: §7.7.23.
- **AccessLink API** — Polar's official API for RR-interval data extraction. *ESTABLISHED.*
- **GSA** (GILE Sigma Algorithm / GILE Stock Algorithm) — the live trading algorithm running in production via `gsa_daily_scheduler` workflow. *ESTABLISHED.*
- **ESP32 Mood Amplifier** — hardware firmware in `hardware/ESP32_MoodAmplifier/`. *ESTABLISHED.*

---

## §6 Meta-Theoretical & Epistemic Vocabulary

- **Asymmetric-Standards #69** — discipline doctrine: brutal honesty, over-skepticism = discipline failure equal to uncritical acceptance. *FOUNDATIONAL.* Anchor: `replit.md` user preferences.
- **Asymmetric Success-Failure Performance** — the 2026-05-07 meta-axiom: failures are non-diagnostic; τ/δ are separable channels. *FOUNDATIONAL.* Anchor: `ASYMMETRIC_SUCCESS_FAILURE_PERFORMANCE_2026-05-07.md`.
- **Failure-Non-Diagnosticity** — the claim that failures carry near-zero information about agent quality because the failure space is ≈infinite. *FOUNDATIONAL.*
- **Two-Channel Separability** — the claim that τ(s) and δ(MR) are independent control variables, not coupled. *FOUNDATIONAL.*
- **Audience-Conditional δ-tuning** — the claim that optimal δ(MR) depends on audience. *FOUNDATIONAL.*
- **Basal Neglect Fallacy** — conflating basicality with low importance; TI dialect for MR-1 invisibility bias. *ESTABLISHED.* Anchor: `INSIGHTS_2026-05-06.md` §7.7.25(a).
- **DPES** — Brandon's autonomous high-output mode for the agent; signal words "DPES", "Continue", directional one-liners. *ESTABLISHED.* Anchor: `replit.md` user preferences.
- **Markov-1 insufficiency for FW** — research-question logged 2026-05-06 that libertarian free-will requires non-Markovian self-modeling. *CONJECTURAL.* Anchor: `MARKOV_CHAIN_FREE_WILL_RESEARCH_QUESTION.md`.
- **Three-C's** — Concept / Connections / Capital — Brandon's self-assessment grading framework. *ESTABLISHED.* Anchor: `replit.md` biographical block.
- **Trajectory #1 (Hardware Prior-Art)** — HS-era EEG → Mendi BLE = 8-10 yr. *ESTABLISHED.* Anchor: §7.7.21, §7.7.24.
- **Trajectory #2 (Theoretical Prior-Art)** — TEDx 2019 → TI Framework 2025 = 6-7 yr. *ESTABLISHED.* Anchor: §7.7.22.
- **Trajectory #3 (Intuition Prior-Art)** — Reiki #1 + Reiki #2 + Diane Hiller (load-bearing) + chakra-readers + Mimi + Crystal (supporting). *ESTABLISHED.* Anchor: §7.7.25, `INSIGHTS_2026-05-06.md` §4, `CRYSTAL_LEE_FIRST_HOSPITALIZATION_INTUITION_2026-05-07.md`.

---

## §7 Biographical & Operational Vocabulary

- **CCC** (Connecticut Association of Schools) — issued Brandon's Governor's Scholar 2017 plaque. *(Distinct from Central-Coherence-Coordination CCC in §3 — context disambiguates.)*
- **MIU** (Maharishi International University) — Brandon's August 2026 forward-looking move-in. *ESTABLISHED.* Anchor: §7.7.28.
- **BlissGene** — Brandon's biotech vehicle; SBIR-track for FAAH-OUT/Jo Cameron biology. *ESTABLISHED.* Anchor: §7.7.26.
- **Startup Warrior LOS** — Letter of Support from Josh Wingate (Investor) for BlissGene SBIR. *ESTABLISHED.*
- **SBIR** — Small Business Innovation Research grant program; prior cycle reached top half-to-third of applicants. *ESTABLISHED.*
- **Retreat (Retreat Behavioral Health)** — 2024 inpatient context; social-integration peak (~50 contacts). *ESTABLISHED.* Anchor: §7.7.21, §7.7.28.
- **Mimi** — Brandon's grandmother; baton-pass to Ray; spirit-connection thesis. *ESTABLISHED.* Anchor: `MIMI_FULL_BIOGRAPHY_AND_RAY_BATON_PASS_2026-05-04.md`.
- **TEDx Oct 6 2019** — Brandon's verified TEDx talk (https://youtu.be/6hPulBvggmo); first A+ tier credential. *ESTABLISHED.*

---

## Maintenance policy

- **New foundational term**: agent adds entry on first use in a paper.
- **Status upgrade** (CONJECTURAL → ESTABLISHED): requires verification artifact (Lean check, experimental result, paper publication).
- **Synonym detection**: if two papers use different terms for the same concept, this index is the dispute-resolution venue.
- **Last update**: 2026-05-07 (initial creation, 90+ entries across 7 sections).
