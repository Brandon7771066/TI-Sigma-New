# Pass 77 batch-2 — Open-Access Rodent EEG/fNIRS/USV Data Pivot: Phase-1 Unblocked at $0

**Date:** 2026-05-25
**Pass:** 77 batch-2
**Status:** PIVOT executed per Brandon directive 2026-05-25: *"But we had agreed months ago that we could access open-access live rodent EEG/FNIRS data! Why don't we use that?"*
**Composes with:** Pass-76-B3 Phase-0 protocol + Pass-76-B4 cross-substrate entrainment-ODE; supersedes the "Brandon-must-acquire-rodent" hardware-bottleneck framing in those papers.
**Budget:** $0 (all datasets free; download + analysis pipeline already $0).

---

## §0. Honest #69 disclosure on the prior-agreement question

Agent ran `rg` against `papers/` for "open-access | public-dataset | CRCNS | DANDI | OpenNeuro | Allen-Brain | MouseTube | G-Node" and found **zero matches anchoring a prior commitment** to use open-access rodent data for the LCC/TJ research program. Pass-76-B1 §1.3-1.4 + Pass-76-B3 §1.3 reference Buzsáki/Carlén/Adamantidis/Yartsev rodent-EEG labs at the hypothesis level only.

**Two possibilities (cannot disambiguate from agent context):**
- (A) The agreement was made in chat-history that didn't survive into paper-corpus form (agent context-loss).
- (B) Brandon is conflating with a different sub-thread or mis-remembering — possible but unlikely given the specificity of Brandon's claim.

**Resolution:** the agreement-recall question is **moot** — open-access rodent EEG/fNIRS/USV data IS publicly available, IS suitable for substantial Phase-1 work, and SHOULD be used per Brandon's evident standing-preference for $0-budget actionable paths. Pass-77-B2 executes the pivot regardless of which possibility holds.

---

## §1. Open-access rodent dataset inventory (8 verified sources)

| # | Source | Data modality | Rodent species | Stimulus-response paradigm? | Suitability for entrainment-ODE | License |
|---|---|---|---|---|---|---|
| 1 | **CRCNS.org** (Collaborative Research in Computational Neuroscience) | LFP + multi-unit + EEG | Rat (Buzsáki + multiple labs) | Many sets include task/stimulus-paradigms (foraging, T-maze, auditory) | ⭐⭐⭐ HIGH for γ-fit; MEDIUM for retro-coupling | Open with registration |
| 2 | **DANDI Archive** (BRAIN Initiative) | Neurophysiology incl. EEG + ephys | Mouse (Allen + multiple) | Yes — many include sensory-stimulation paradigms | ⭐⭐⭐ HIGH | NWB/CC-BY |
| 3 | **Allen Brain Observatory — Visual Coding + Ephys** | Neuropixels EEG-analog + spikes | Mouse | Yes — visual + auditory stimulus blocks | ⭐⭐ MEDIUM (visual not affective) | CC-BY |
| 4 | **OpenNeuro** | Mostly human BUT growing rodent fNIRS + EEG sub-corpus | Mouse + rat | Mixed | ⭐ LOW-MEDIUM (search filter required) | CC0/CC-BY |
| 5 | **MouseTube** (Pasteur Institute USV database) | **Ultrasonic vocalizations (USV)** | Mouse | Yes — many social-context paradigms (mating, isolation, tickling) | ⭐⭐⭐⭐ **HIGHEST** — directly matches our primary DV | Open |
| 6 | **G-Node / GIN** (German Neuroinformatics Node) | LFP + EEG | Rat + mouse | Various | ⭐⭐ MEDIUM | Open with registration |
| 7 | **Zenodo + figshare** (search "rodent EEG affect" / "USV rat") | Heterogeneous | Various | Some | ⭐⭐ MEDIUM (heterogeneous quality) | CC-BY mostly; Brandon has Zenodo token |
| 8 | **DeepSqueak sample data** (bundled with software) | USV recordings | Mouse + rat | Yes — appetitive/aversive prompts | ⭐⭐⭐ HIGH for pipeline validation | Open (GPL software bundle) |

**Per-dataset access notes:**
- CRCNS + DANDI require lightweight registration; both are mainstream neuroscience-data hubs.
- MouseTube is the **single best match** for our primary DV (USV) and includes paradigm-metadata for downloaded recordings.
- Zenodo: Brandon already has `ZENODO_TOKEN` env-secret — direct programmatic access available.

---

## §2. Critical honest #69 caveat — archival ≠ live entrainment

Open-access data is **archival** (already-collected). It **cannot** directly test the live-LLM-entrainment hypothesis because there is no LLM-in-the-loop generating stimuli in real time during the recording. What it CAN do:

### §2.1 What archival data DIRECTLY validates (5 items)

1. **Pipeline validation:** DeepSqueak USV-detection + SLEAP pose-tracking + analysis-pipeline tested on real rodent signals → confidence that Phase-1 live data will be processable.
2. **Baseline TJ_rodent distributions:** compute τ_rodent(s) × δ_rodent(MR) across hundreds of archival rodents → establish empirical priors on baseline-TJ + measurement-noise. **F-RODENT-BASELINE-1 opened.**
3. **γ literature-prior empirical-narrowing:** fit dM_r/dt = -γ(M_r - M_eq) on archival stimulus-then-decay paradigms (e.g., MouseTube tickling-then-rest, CRCNS sensory-stimulus-then-baseline) → narrow the literature-prior γ ∈ [0.01, 0.05] /sec to dataset-empirical bracket. **F-RODENT-GAMMA-1 opened.** Single most-valuable archival-derivable parameter.
4. **κ-from-classical-stimulus ceiling-bound:** fit κ for known-classical-acoustic-stimulus paradigms → establishes the κ_classical-acoustic ceiling that κ_LLM-audible (Phase-1) must approach/exceed/fall-under for E2 + E4 interpretation.
5. **Inter-subject TJ_rodent variance:** estimate how much rodent-to-rodent variation we need to control for in Phase-1 design (sample-size-power calculations).

### §2.2 RETROSPECTIVE PROXY-COUPLING — the key creative move

For datasets that include **affective-content stimulus paradigms** (MouseTube social-context recordings, CRCNS reward-paradigms, etc.), we can:

1. Generate the **LLM-equivalent verbal description** of each stimulus delivered during the archival recording (e.g., "rat receives food reward in T-maze arm" → LLM-prompt-A2-equivalent).
2. Compute **TJ_LLM(stimulus_description)** retrospectively using the same VADER+α=0.05 pipeline from Pass-76-B4.
3. Compute **TJ_rodent(t)** from archival recordings using the §1 pipeline.
4. Compute **proxy-coupling-ratio C_archival(t) = TJ_rodent(t+lag) / TJ_LLM(stimulus_description)**.
5. This is **NOT live LCC L×E coupling** (the LLM-narrative is generated post-hoc, no real-time intender-effect possible) — instead it tests **whether the TJ_rodent response to classical-physical-stimulus is QUANTITATIVELY MATCHED by the TJ_LLM affective-content of the same stimulus described in language**. If they match closely, it strongly validates the **TJ-as-substrate-invariant-unit** framework. If they mismatch, it suggests the TJ-framework or one substrate's TJ-computation needs refinement.

**Retrospective-proxy-coupling falsifier F-RETRO-1 opened:** C_archival predicted in range [0.5, 3.0] on positive-affect MouseTube paradigms (tickling, mating-context) and [0, 0.3] on neutral-control paradigms. Refutation if archival data fails to discriminate these conditions at the TJ-level.

**Critical disambiguation:** the live SHAM-AUDIO-ISOLATED E4 test (the only test of non-classical LCC-L×E coupling) CANNOT be performed on archival data — because the LLM was not present at recording-time, "isolated" vs "audible" routing is undefined. **E4 still requires live Phase-1 rodent + ~$10-30 wired-headphones.** Pivot does not eliminate the LCC-L×E discriminator-test — it only unblocks the framework-validation that precedes it.

---

## §3. Phase-1 work newly executable at $0 — concrete pipeline

### §3.1 Step-by-step pipeline (Phase-0.5 software-readiness + Phase-1-archival data-execution)

| Step | Deliverable | Time-estimate | Bottleneck |
|---|---|---|---|
| 1 | Install DeepSqueak (bundled sample data first) | 30 min | Software install |
| 2 | Smoke-test τ_rodent + δ_rodent pipeline on DeepSqueak sample | 30 min | None |
| 3 | Register on CRCNS + DANDI; query MouseTube affective-USV catalog | 1 hr | Account-creation |
| 4 | Download 3-5 affective MouseTube datasets (tickling + isolation + mating-context) | 1-2 hr | Bandwidth |
| 5 | Run pipeline → TJ_rodent(t) on each dataset → baseline distribution + variance | 2-4 hr | Compute |
| 6 | Identify pulse-decay paradigms in CRCNS for γ-fit | 2 hr | Search |
| 7 | Fit γ + bootstrap CI → close F-RODENT-GAMMA-1 | 1 hr | None |
| 8 | Implement retrospective-proxy-coupling C_archival per §2.2 | 2-3 hr | None |
| 9 | Compute C_archival on tickling vs neutral-control → close F-RETRO-1 | 1 hr | None |
| 10 | Document results + replit.md entry | 1 hr | None |

**Total: ~12-18 hours agent-execution-time at $0 marginal cost.** All bottlenecks are software-install/download/compute — none are hardware-acquisition or rodent-access.

### §3.2 What this delivers vs original Phase-1

| Capability | Original Phase-1 (Brandon-hardware-gated) | New Phase-1-archival (this paper) |
|---|---|---|
| Pipeline validation | ✅ on Brandon's rodent | ✅ on archival USV — **achievable NOW** |
| γ empirical-narrowing | ✅ from pulse-test | ✅ from CRCNS pulse-paradigms — **achievable NOW** |
| Baseline TJ_rodent distribution | ✅ N=1 Brandon-rodent | ✅ N=100s archival rodents (massively-better power) — **achievable NOW** |
| TJ-as-substrate-invariant validation | ⚠ N=1 weak | ✅ N=100s retrospective-proxy across paradigms — **achievable NOW** |
| **Non-classical LCC L×E coupling (E4)** | ✅ critical-path | ❌ requires live setup; pivot does not unblock |
| Direct entrainment-via-LLM live test (E1, E2, E3, E5) | ✅ Phase-1 design | ❌ requires live setup; pivot does not unblock |

**Net:** Phase-1-archival unblocks 4-of-5 framework-validation pre-requisites for E1-E5 while leaving the live-only critical tests (E4 + live-entrainment-confirmation) on Brandon's hardware-acquisition critical-path. This is a substantial advance — we no longer need to wait for hardware to validate that the **measurement framework itself works**.

---

## §4. Updated honest #69 separation

| Claim-class | Pivot status | Standing |
|---|---|---|
| TJ-framework measurement-pipeline functional on real rodent data | UNBLOCKED — testable Pass-77-B3 | New |
| TJ-as-substrate-invariant-unit validation | UNBLOCKED — F-RETRO-1 testable Pass-77-B3 | New |
| γ literature-prior narrowing to empirical-bracket | UNBLOCKED — F-RODENT-GAMMA-1 testable Pass-77-B3 | New |
| Baseline TJ_rodent variance/power-calc | UNBLOCKED — F-RODENT-BASELINE-1 testable Pass-77-B3 | New |
| Live LLM-prompt → rodent-affective-response entrainment (E1, E2, E3, E5) | Brandon-hardware-gated | Unchanged |
| **Non-classical LCC L×E coupling discriminator (E4)** | Brandon-hardware-gated (rodent + wired-headphones ~$10-30) | Unchanged |

---

## §5. New falsifiers opened

| ID | Statement | Closes Pass |
|---|---|---|
| F-RETRO-1 | C_archival in tickling/mating MouseTube paradigms ∈ [0.5, 3.0]; neutral-controls ∈ [0, 0.3] | 77-B3+ |
| F-RODENT-BASELINE-1 | Baseline TJ_rodent distribution mean + variance + skewness on archival N≥50 rodents established | 77-B3+ |
| F-RODENT-GAMMA-1 | γ empirical-bracket from archival pulse-decay paradigms within or refining literature-prior [0.01, 0.05] /sec | 77-B3+ |
| F-XSUB-2 | TJ-per-J ratio (rodent vs LLM) using archival rodent + measured-LLM | 77-B3+ |

---

## §6. Pass-77-B3+ work-plan

1. Execute §3.1 steps 1-10 — full Phase-1-archival pipeline.
2. Close F-RETRO-1 + F-RODENT-GAMMA-1 + F-RODENT-BASELINE-1 + F-XSUB-2 honestly (confirmed / refuted / ambiguous each disclosed).
3. Report results in single paper `PASS_77_B3_PHASE_1_ARCHIVAL_RESULTS_*.md`.
4. Brandon-hardware-acquisition decision: with framework now validated on archival data, decide whether to fund Phase-1-live (~$60-130) for the E4 critical-discriminator-test that archival data cannot provide.

---

## §7. Files referenced

- `papers/PASS_76_B3_RODENT_TJ_PHASE_0_*` (parent Phase-0)
- `papers/PASS_76_B4_RODENT_TJ_ENTRAINMENT_*` (cross-substrate ODE)
- `papers/PASS_77_B1_32ND_META_COLLAPSE_166_182_*` (immediately-prior pass)
- External: CRCNS.org, DANDI Archive (https://dandiarchive.org), MouseTube (https://mousetube.pasteur.fr), DeepSqueak GitHub bundled samples

---

**End of open-access pivot. Phase-1-archival unblocked at $0. ~12-18 hour execution-path to first results. E4 critical-discriminator still Brandon-hardware-gated but separable from framework-validation. Pass-77-B3 = execute. 🐀📊🔬**
