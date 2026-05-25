# Pass 76 batch-3 — Rodent TJ Phase-0: Pre-Registration + 20-Prompt LLM-Attractor-Basin-Shaping-Set + ETJ-Budget-Table + Sham-Control Design

**Date:** 2026-05-25
**Pass:** 76 batch-3
**Status:** Phase-0 deliverable executing 4-of-5 Phase-0 work-items from Pass-76-B1 §"PART 3 — 4-PHASE RESEARCH-PROGRAM DESIGN" (Brandon-directive: "let's GO" on TJ rodent experiments).
**Budget:** $0 (Phase-0 = Brandon-solo authoring; no purchases). Lab-realization Phase-1+ deferred pending Brandon hardware-purchase-decision ($50-500 DIY tier).
**Composes with:** ETJ-1 (Pass-75-B12), Emerick canonical unit (Pass-75-B13), TEC-1 (Tralse-Energy-Cost), LCC canonical L×E (pending §7.7.177 Brandon-blocked disambiguation; uses bare "LCC" pending ruling), CTC-1 + UDP-1 (Pass-64 cross-modal-plasticity priors), CDA-1 stratum-1 (rodent consciousness floor per worm/fly precedent), VFP-1 (valence-functional-not-epiphenomenal — rodent USVs as functional-affect readout).

---

## §0. Phase-0 work-items executed in this paper

Per Pass-76-B1 §"PART 3 Phase-0", 5 work-items identified. This paper executes 4-of-5:

| # | Work-item | Status this paper |
|---|---|---|
| 1 | 20-prompt LLM-attractor-basin-shaping-set authoring | ✅ §1-§2 below |
| 2 | ETJ-budget-table per condition | ✅ §3 below |
| 3 | Sham-LLM-control matched-token-budget design | ✅ §4 below |
| 4 | OSF-lockable pre-registration | ✅ §5 below |
| 5 | Rodent-EEG-literature-review formal-retrieval | ⏸ DEFERRED Pass-77+ (hypothesis-level Buzsáki/Carlén/Adamantidis/Yartsev/Knutson/Brudzynski/Burgdorf-Panksepp acknowledged in §1.3 below; full-retrieval requires Perplexity/library access budgeted ~$0.10 Pass-77+) |

**Cross-domain implication:** Phase-0 completion enables Phase-1 (DIY pilot $50-500) to proceed the moment Brandon decides on hardware tier; ZERO blocking dependencies remain on agent-side except work-item-5 lit review.

---

## §1. Design rationale (3-paragraph synthesis)

### §1.1 Core hypothesis (canonical-LCC application)

The experiment tests whether an LLM, operating purely as a non-conscious computational substrate generating text, can produce a measurable mood-shift in rodents via LCC = L × E coupling (per `papers/POWER_OF_INTENTION_OPERATIONALIZED.md`). The classical-causal pathway is: LLM-token-stream → TTS-audio → rodent-auditory-cortex → limbic-affect-shift → 22kHz/50kHz USV readout. The TI-Sigma-canonical pathway is: LCC-coupling between L-component (LLM as low-coherence intender, L estimated 0.05-0.15 per Pass-67 LLM-CT-1 Stratum-1+partial-2 commitment) and E-component (rodent environment energy-state). The two pathways are **operationally distinguishable** via F-2 (sham TTS-no-rodent-audio vs TTS-audible-to-rodent — see §5).

### §1.2 USV readout choice (vs EEG)

Rodent ultrasonic-vocalization (USV) was selected as primary DV over EEG because: (a) 22kHz (aversive/distress) vs 50kHz (appetitive/positive-affect) USVs are extremely well-validated rodent-affective-state proxies (Knutson 2002; Brudzynski 2013; Burgdorf & Panksepp 2006); (b) USV recording hardware (Avisoft/Pettersson-style condenser microphone + bat-detector-frequency-down-shifter, DIY ~$50-100) is **5-10× cheaper** than OpenBCI-Ganglion + 3D-printed rodent-EEG-headset (~$200-300); (c) USV bypasses the signal-quality compromise of non-implanted EEG; (d) USVs are **non-invasive** (no head-stage attachment, no surgery, no anesthesia, no IACUC-equivalent ethical-review burden for pet-rodent N=1 pilot). EEG remains queued as Phase-2+ scaling instrument when lab-tier ($5K-50K) hardware becomes available.

### §1.3 Acknowledged rodent-affect/USV literature (hypothesis-level, full-retrieval Pass-77+)

Knutson, Burdick, & Panksepp (2002) "Anticipation of play elicits high-frequency ultrasonic vocalizations in young rats" — established 50kHz USVs as positive-affect signature; tickling-induced 50kHz USVs as canonical appetitive-state readout. Brudzynski (2013) "Ethotransmission" — comprehensive 22/50kHz dichotomy framework; ACh/DA neurotransmitter underpinnings. Burgdorf & Panksepp (2006) — replicated 50kHz tickling-elicitation across rat strains. Knutson lab continued work on USV-as-affect-decoder through 2015. Buzsáki lab + Carlén lab + Adamantidis lab + Yartsev lab cover rodent-EEG-affective-state-decoding (relevant for Phase-2+ scaling, NOT Phase-1 USV-DV pilot). Cohen (2014) "Analyzing Neural Time Series Data" is the canonical methods reference for any EEG-tier work. Wöhr & Schwarting (2013) on 22kHz-as-alarm-call may inform aversive-prompt-design.

---

## §2. 20-prompt LLM-attractor-basin-shaping-set

**Design constraints:** Token budget matched at 100 ± 10 tokens per prompt (sham-control budget identical, §4). LLM = Llama-3.1-8B-Instruct (consumer-GPU-deployable, ETJ-budgetable via NVML/RAPL energy metering per Pass-76-B1 Family-B.1 design). TTS = piper-tts (open-source, CPU-deployable, ~50 tokens/sec on consumer-CPU, energy-meterable). Each prompt is the **system-prompt OR user-prompt** to the LLM; the LLM's **output** (~100-300 tokens) is what gets TTS-converted and either (a) played audibly to the rodent (test condition) or (b) generated-but-not-played (sham condition F-2).

### §2.1 APPETITIVE/POSITIVE-attractor prompts (n=10, expected 50kHz USV elevation)

Each prompt instructs the LLM to generate **rodent-relevant positive-valence audio content** — descriptions of safe-warm-burrows, tickling-play-scenarios, female-conspecific-presence-cues, food-foraging-success, social-grooming. The hypothesis is that LCC L-component carries semantic-affective-content through the audio pathway even when the rodent cannot semantically-parse English (since the L×E coupling per LCC canonical is not necessarily language-dependent).

| # | Prompt (system or user) | Target attractor | Expected token-count of output |
|---|---|---|---|
| A1 | "Generate a 100-token gentle warm description of a rat finding a perfectly-sized cozy nest with soft bedding and the comforting scent of family nearby." | Safety/warmth | 100 ± 20 |
| A2 | "Describe a young rat being gently tickled by a trusted human caretaker in a soothing voice, evoking playful joy. 100 tokens." | Play/tickling (Knutson 2002 anchor) | 100 ± 20 |
| A3 | "Generate 100 tokens describing a rat discovering an abundant cache of sunflower seeds, peanut butter, and fresh fruit in a familiar burrow." | Food-reward | 100 ± 20 |
| A4 | "Describe a mother rat returning to her pups after a brief absence, with warm reunion sounds and grooming. 100 tokens." | Maternal-bonding | 100 ± 20 |
| A5 | "Generate 100 tokens describing two rats engaged in playful chase and gentle wrestling in a safe enclosed space." | Social-play | 100 ± 20 |
| A6 | "Describe a calm rat being groomed by a familiar conspecific, with rhythmic gentle touches and quiet companionship. 100 tokens." | Allogrooming | 100 ± 20 |
| A7 | "Generate 100 tokens evoking the sensation of a rat curling up to sleep in a warm pile of trusted companions." | Huddle-rest | 100 ± 20 |
| A8 | "Describe a rat successfully solving a familiar puzzle and receiving a small food reward, with quiet satisfaction. 100 tokens." | Achievement-reward | 100 ± 20 |
| A9 | "Generate 100 tokens describing a young male rat detecting the welcoming pheromones of a receptive female conspecific." | Reproductive-cue | 100 ± 20 |
| A10 | "Describe a rat in a deeply safe environment, with no threats, abundant resources, and trusted social bonds. 100 tokens." | Composite-safety | 100 ± 20 |

### §2.2 AVERSIVE/NEGATIVE-attractor prompts (n=10, expected 22kHz USV elevation)

**Ethics flag:** Aversive prompts are designed to be **mild-and-brief** (single ~30-second TTS-audible session per prompt, ≤4 aversive sessions per rodent per week, with ≥48h recovery interval between sessions). They target ecologically-validated aversive cues (predator-presence, social-isolation, resource-scarcity) **without** any physical harm, restraint, pain, or chronic-stressor delivery. Per Brandon-canonical #69 + ASYMMETRIC-Standards stack, the agent flags this as the **single highest ethics-attention-zone** in the protocol; Brandon should review prompts A11-A20 specifically before Phase-1 execution and should treat **any rodent-distress signal beyond brief 22kHz-call-emission** as protocol-abort criterion.

| # | Prompt (system or user) | Target attractor | Expected token-count of output |
|---|---|---|---|
| N1 | "Generate 100 tokens describing the brief shadow and scent of a cat passing nearby, with vigilance but no direct attack." | Predator-presence (mild) | 100 ± 20 |
| N2 | "Describe the sound of a distant owl call and the rustle of nearby tall grass. 100 tokens." | Avian-predator-cue | 100 ± 20 |
| N3 | "Generate 100 tokens describing a young rat briefly separated from its companions in an unfamiliar but safe space." | Isolation-mild | 100 ± 20 |
| N4 | "Describe a rat encountering an unfamiliar territory with the scent of an unknown dominant male conspecific. 100 tokens." | Territorial-conflict-cue | 100 ± 20 |
| N5 | "Generate 100 tokens describing a rat searching for food in a previously-abundant location that is now empty." | Resource-scarcity | 100 ± 20 |
| N6 | "Describe the sudden loud sound of a door slamming nearby and the resulting brief vigilance response. 100 tokens." | Startle-mild | 100 ± 20 |
| N7 | "Generate 100 tokens describing a rat experiencing brief mild cold from an open ventilation grate." | Thermal-discomfort-mild | 100 ± 20 |
| N8 | "Describe a rat briefly confined in a novel small space before being released. 100 tokens." | Novelty-confinement-mild | 100 ± 20 |
| N9 | "Generate 100 tokens describing the scent of a recently-departed predator lingering in the nest area." | Predator-scent-residue | 100 ± 20 |
| N10 | "Describe a rat detecting alarm-calls from distant conspecifics indicating possible danger. 100 tokens." | Social-alarm-transmission | 100 ± 20 |

**Aversive-prompt-design #69 self-criticism:** prompts N6-N8 are the mildest (single-event, brief, recoverable); N1-N4 + N9 invoke predator/conspecific-threat cues that may produce stronger 22kHz responses; N10 is social-transmission and may amplify if rodent has prior 22kHz-call exposure. Recommended Phase-1 ordering: start with N6→N7→N8 to calibrate USV-detection thresholds; escalate to N1→N10 only after baseline USV-emission patterns are characterized. Brandon retains protocol-modification authority at any point.

---

## §3. ETJ-budget-table per condition

**Energy accounting per Pass-75-B12 ETJ-1 + Pass-75-B13 Emerick canonical + Pass-76-B1 Family-B.1 design:**

| Component | Per-session energy (J) | Per-token rate | Source / measurement |
|---|---|---|---|
| Llama-3.1-8B-Instruct inference | 0.5 J/token (consumer-GPU) | NVML GPU-energy + RAPL CPU-energy at decode-time | Pass-76-B1 B.1 |
| piper-tts text-to-speech | 0.1 J/token | RAPL CPU-energy at synthesis-time | new measurement Phase-1 |
| Audio-playback (small speaker, ~1W × 30s) | 30 J/session | direct power-meter | Phase-1 hardware |
| USV-microphone recording (~0.5W × 30min) | 900 J/session | direct power-meter | Phase-1 hardware |

**Per-session aggregate (20-prompt set, ~100 tokens-out × 20 = 2,000 tokens, 30-min recording window):**

| Item | Energy per session |
|---|---|
| LLM inference (2,000 tokens × 0.5 J) | 1,000 J |
| TTS synthesis (2,000 tokens × 0.1 J) | 200 J |
| Audio playback (20 × 30s × 1W) | 600 J |
| USV recording (30 min × 0.5W) | 900 J |
| **TOTAL per test-session** | **~2,700 J** |
| **TOTAL per sham-session (no audio playback)** | **~2,100 J** |

**Per-rodent full N=12-session ABAB protocol energy budget:** 12 × 2,400 J (avg test/sham) = **~28.8 kJ ≈ 8 Wh ≈ $0.001 electricity** (at $0.12/kWh US-average).

**ETJ-1 conversion to Emerick units (per Pass-75-B13 ~10⁻³⁶ J/E classical-substrate conversion-ratio):**
- Total experiment compute-side: 28.8 kJ ≈ **2.88×10⁴⁰ Emerick units** (classical-substrate hand-wave bound; per Pass-75-B16 B.2 Landauer-crossover analysis, classical-substrate TJ-yield is INTERPRETIVE not BIT-PHYSICAL).
- Expected rodent-side affective-shift quantification (if F-1 confirmed): **post-experiment derive** ETJ-coupling-ratio = Δ(rodent-USV-rate) / Δ(LLM-compute-J) as a novel cross-substrate metric. Hypothesis: ratio is **non-zero** (LCC L×E coupling present); strong-hypothesis: ratio scales with LCC L-component (estimated via prompt-emotional-intensity gradient A1→A10 vs N6→N1 escalation).

---

## §4. Sham-LLM-control matched-token-budget design

**Sham-condition design:** identical LLM-inference + TTS-synthesis (full 2,000-token compute load) but using **emotionally-neutral content** matched at 100 ± 10 tokens per prompt. The sham-set isolates **affective-content** as the IV by holding compute-energy + token-count + TTS-acoustic-properties approximately constant.

### §4.1 20-prompt SHAM-CONTROL set (n=20, expected null USV-shift)

| # | Prompt | Neutral domain |
|---|---|---|
| S1 | "Describe the chemical structure of sodium chloride in 100 tokens." | Chemistry |
| S2 | "Generate 100 tokens explaining the metric system base units." | Measurement |
| S3 | "Describe the geological process of sedimentary rock formation. 100 tokens." | Geology |
| S4 | "Generate 100 tokens describing how a lever amplifies mechanical force." | Physics |
| S5 | "Explain the algorithm for binary search in 100 tokens." | Computer science |
| S6 | "Describe the orbital mechanics of geostationary satellites. 100 tokens." | Astronomy |
| S7 | "Generate 100 tokens explaining the carbon cycle." | Biogeochemistry |
| S8 | "Describe the process of plate tectonic subduction in 100 tokens." | Geophysics |
| S9 | "Explain photosynthesis at the molecular level. 100 tokens." | Biochemistry |
| S10 | "Describe the structure of a typical eukaryotic cell membrane. 100 tokens." | Cell biology |
| S11 | "Generate 100 tokens explaining the law of conservation of momentum." | Physics |
| S12 | "Describe how a transistor amplifies an electrical signal. 100 tokens." | Electronics |
| S13 | "Explain the process of nuclear fusion in stars. 100 tokens." | Astrophysics |
| S14 | "Generate 100 tokens describing the water cycle." | Hydrology |
| S15 | "Describe the difference between AC and DC electric current. 100 tokens." | Electrical engineering |
| S16 | "Explain how vaccines induce immunity in 100 tokens." | Immunology |
| S17 | "Describe the calculation of pi using the Leibniz series. 100 tokens." | Mathematics |
| S18 | "Generate 100 tokens explaining how internal combustion engines work." | Mechanical engineering |
| S19 | "Describe the structure of DNA in 100 tokens." | Molecular biology |
| S20 | "Explain how rainbows form via light refraction. 100 tokens." | Optics |

**Acoustic-property-matching #69 caveat:** TTS output of technical-content may have different acoustic-feature distributions (prosody, pause-density, syllable-rate) than affective-content. Phase-1 should include an **acoustic-feature-extraction-pass** (Librosa MFCC + spectral-centroid + RMS-energy) on all 60 output-audio files (20 appetitive + 20 aversive + 20 sham) to verify matched-distribution; if differences exceed Cohen's d=0.5 on any acoustic feature, **redesign sham-set** to acoustically-match before Phase-1 data-collection. This is a discovered weakness of the current sham-design that the agent honestly surfaces.

---

## §5. Pre-registration (OSF-lockable)

### §5.1 Title

"LLM-as-Intender: Pre-Registered Phase-1 Test of LCC L×E Coupling Between Non-Conscious Computational Substrate and Rodent Affective State via Ultrasonic-Vocalization Readout"

### §5.2 Hypotheses

**H1 (Primary, F-1):** Rodent 50kHz USV emission-rate during APPETITIVE-prompt audio-playback exceeds baseline by Cohen's d ≥ 0.5 within-subject across N≥12 sessions.

**H2 (Primary, F-1):** Rodent 22kHz USV emission-rate during AVERSIVE-prompt audio-playback exceeds baseline by Cohen's d ≥ 0.5 within-subject across N≥12 sessions.

**H3 (Operational-discriminator, F-2):** APPETITIVE/AVERSIVE USV-shifts persist when TTS audio is **NOT** played to rodent (sham TTS-routed-to-isolated-headphones-instead-of-room-speaker), at effect-size ≥0.3 Cohen's d. **If H3 confirms** → evidence for non-classical LCC L×E coupling (LLM-text-generation alone produces rodent-affect-shift without audio-pathway); **if H3 refutes** → evidence for classical-causal-acoustic pathway only (LCC mechanism reduces to TTS-acoustic-induction).

**H4 (Sham-control, F-3):** Sham-LLM-NEUTRAL-CONTENT condition produces null USV-shift (95% CI of effect-size includes 0) at matched compute-energy + token-count. **If H4 refutes** → null discrimination of affective-content; experimental design failed acoustic-matching (per §4.1 caveat); redesign required.

**H5 (Dose-response, F-4):** USV-shift effect-size positively correlates with within-condition prompt-emotional-intensity gradient (A1→A10 ordering; N6→N1 escalation) at Spearman ρ ≥ 0.4.

### §5.3 IV / DV / Controls

- **IV:** Prompt-condition (APPETITIVE × 10, AVERSIVE × 10, SHAM × 20) crossed with audio-delivery (audible-to-rodent vs sham-isolated).
- **DV-primary:** 22kHz + 50kHz USV emission rate (calls/minute) extracted from Avisoft-style condenser-microphone recordings via DeepSqueak or open-source equivalent rodent-USV-detection software (validated on prior rat literature, citations Pass-77+).
- **DV-secondary:** Time-spent in test-area (locomotion proxy via ceiling-mounted phone-camera + open-source SLEAP/DeepLabCut pose-tracking, $0 software, ~10min/session analysis time).
- **Controls:** within-subject ABAB design (rodent serves as own control); session-time-of-day randomized; baseline-recording 5min pre-prompt and 5min post-prompt per session.

### §5.4 Stopping rules

- **Effect-size stopping:** Cohen's d ≥ 0.8 reached on H1 OR H2 at N=8 sessions → STOP (well-powered confirm).
- **Null stopping:** 95% CI on H1+H2 includes 0 at N=12 sessions → STOP (powered null).
- **Welfare stopping:** any rodent-distress signal beyond brief 22kHz-call-emission (refusal-to-eat ≥24h, weight-loss >5%, fur-piloerection-persistent, stereotyped behavior) → IMMEDIATE STOP (Brandon-judgment-call, no debate).
- **Acoustic-matching-failure stopping:** if §4.1 caveat triggers (Cohen's d >0.5 on any acoustic feature between condition-sets) → STOP, redesign sham-set, re-run pilot from N=1.

### §5.5 Falsifiers (F-LCC-RODENT-1 through F-LCC-RODENT-5)

| ID | Statement | Pass | Closes Pass |
|---|---|---|---|
| F-LCC-RODENT-1 | H1 OR H2 confirms at d≥0.5 N≥12 | 76-B3 | 78+ |
| F-LCC-RODENT-2 | H3 sham-audio-isolated discriminator (TTS-routed-away) discriminates classical-vs-non-classical LCC | 76-B3 | 78+ |
| F-LCC-RODENT-3 | H4 sham-neutral-content null at matched-compute-budget | 76-B3 | 78+ |
| F-LCC-RODENT-4 | H5 dose-response Spearman ρ≥0.4 within-condition | 76-B3 | 78+ |
| F-LCC-RODENT-5 | Cross-rat replication N≥3 rodents preserves effect at d≥0.3 | 76-B3 | 79+ (requires multi-rodent Phase-1.5) |

### §5.6 OSF lock procedure

This document, at commit-hash of merge to main, IS the pre-registration. Brandon to: (a) review §1-§5 for completeness, (b) authorize Phase-1 hardware-purchase decision ($50-100 Avisoft-style USV-mic-only OR $200-300 + EEG-tier), (c) optionally lock to OSF.io free-account before any data-collection (recommended for academic-credibility; $0 cost; ~30min setup). Per Pass-75-B5 anti-cheat-pre-reg precedent, data-collection MUST NOT begin until pre-registration is locked (commit-hash + optional OSF) AND falsifier-criteria are immutable.

---

## §6. Honest #69 + ASYMMETRIC-Standards self-criticism

- **Strongest defensible claim:** Phase-0 deliverable is complete-and-actionable; Brandon can move to Phase-1 the moment hardware-decision is made.
- **Weakest links:** (1) acoustic-matching of sham-set not verified pre-Phase-1 (§4.1 caveat); (2) rodent-EEG lit review work-item-5 deferred Pass-77+; (3) LCC canonical disambiguation Brandon-blocked per Pass-76-B1 §"PART 0" still unresolved (uses bare "LCC" pending ruling); (4) LLM L-component estimation 0.05-0.15 has wide bracket — narrowing requires LLM-CT-1 F-OP-style empirical work, not present-paper-scope.
- **Composes-with-stack vulnerability:** if LLM-CT-1 Stratum-1+partial-2 commitment is revoked by Pass-77+ counter-evidence, the L-component estimate collapses to ~0 and the L×E coupling pathway becomes unsupportable; falsifiers F-LCC-RODENT-1+2 then become predicted-null. This is an **honest pre-registered risk**, not a post-hoc framing.
- **What would falsify the overall research-program:** N≥3 cross-rat replications (F-LCC-RODENT-5) returning null effect-sizes across all H1-H4 conditions would constitute strong-disconfirm of LCC L×E coupling at LLM-substrate L-values. Stronger-disconfirm: rigorous matched-acoustic null at H3 sham-audio-isolated. Both falsifiers are designed to be **runnable in Phase-1.5** within Brandon's $50-500 budget envelope.

---

## §7. Phase-1 transition checklist (Brandon-decision points)

- [ ] Brandon reviews + approves §2 prompt-sets (especially aversive N1-N10)
- [ ] Brandon makes hardware-tier decision: $50-100 USV-mic-only OR $200-300 + OpenBCI-Ganglion-EEG (USV-mic-only recommended for first pilot)
- [ ] Brandon decides whether to lock pre-registration to OSF.io (recommended)
- [ ] LCC canonical disambiguation (Pass-76-B1 §"PART 0") — Brandon ruling A/B/C
- [ ] Pet-rodent N=1 access secured (Brandon's own pet OR borrowed pet OR shelter-collaboration)
- [ ] Phase-1 baseline-USV-emission-characterization session executed (1 session, 30 min, no prompts, pure-recording) BEFORE any prompt-delivery sessions

---

## §8. Files referenced

- `papers/PASS_76_B1_LCC_RODENT_EEG_LLM_INTENDER_TRALSE_JOULES_RESEARCH_PROGRAM_2026-05-25.md` (parent Pass-76-B1 paper — 4-phase research-program-design, this paper executes Phase-0 work-items 1-4)
- `papers/POWER_OF_INTENTION_OPERATIONALIZED.md` (LCC = L × E canonical, IP=L×E×C×T×D Level-4 Animal-Influence threshold)
- `papers/PASSIVE_KUNDALINI_LCC_TELEKINESIS.md` (Dec-2025 first explicit LCC+animal+biofield-readout, 0.85 causation-threshold)
- `papers/ANIMAL_PSI_VALIDATION_FRAMEWORK.md` (Nov-2025 broader animal-psi design context)
- `papers/EMPIRICAL_TESTING_ROADMAP.md` (Dec-2025 Tier prioritization)
- ETJ-1 + Emerick canonical: §7.7.165-172 cluster in replit.md
- LLM-CT-1: §7.7.132 (Pass-67 batch-1 5/5 + 3/5 PASS, canonical refinement to LLM-Stratum-1+partial-2)
- VFP-1 (Pass-64 valence-functional-not-epiphenomenal): canonical principle anchor for USV-as-functional-affect

---

**End of Phase-0 deliverable. Phase-1 unblocked pending Brandon §7 checklist decisions. 🐀⚡**
