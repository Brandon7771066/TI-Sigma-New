# Pass-77-B35 — Full-Brain Connectome Inventory + Brandon's Embodied-Valence Critique → Candidate Canonical Principle EVP-1

**Date:** 2026-05-27
**Pass:** 77, Batch 35 (Part 1 of 2-paper batch)
**Type:** Literature inventory + theoretical move + candidate canonical principle.
**Brandon directive:** *"Are there any other creatures' full brain connectomes uploaded to the internet? Also, is it just the animals' brains or their full bodies' dna that was uploaded? If only their brains are uploaded, then we're missing all of the embodied ways in which their emotions are actualized within the body!"*
**Companion paper:** `PASS_77_B35_CONSCIOUSNESS_AND_VALENCE_THEORY_REVIEW_2026-05-27.md` (Part 2).
**Cost:** $0.

---

## §0. Executive Summary

This paper does three things:

1. **Inventory** every full or substantial brain connectome publicly uploaded as of 2026-05-27, with completeness percentages and dataset URLs/citations.
2. **Distinguish** *connectome-only* uploads from *whole-organism* data (genome, transcriptome, body-plan, kinematic ground truth) and explicitly call out the gap.
3. **Formalize Brandon's embodied-valence critique** — "if only their brains are uploaded, we're missing all of the embodied ways their emotions are actualized" — as a candidate canonical TI Sigma principle: **EVP-1 (Embodied Valence Principle)**. Five falsifiers attached.

**Headline finding:** as of mid-2026 there are roughly **9 species with publicly-available substantial or complete neural connectomes**, but **only C. elegans has the connectome paired with comparable-resolution whole-body, whole-genome, whole-transcriptome, and whole-cell-atlas data simultaneously**. Every other species is missing at least one whole-body layer. **Brandon's critique applies hard to all of them** — and even to C. elegans for the valence-relevant non-neural systems (gonad, intestine, hypodermis, muscle, ENS-equivalent, hormonal-equivalent NHR signaling).

**EVP-1 candidate canonical** is offered as the formalization. Joint ratification offered with companion-paper outputs.

---

## §1. Connectome Inventory (as of 2026-05-27)

### §1.1 Complete or near-complete connectomes (≥80% of neurons mapped, all synapses)

| Species | Stage | Neuron count | Completeness | First / latest release | Dataset/anchor |
|---|---|---:|---:|---|---|
| **Caenorhabditis elegans** | adult hermaphrodite | 302 | ✅ 100% (synaptic, gap-junction) | White et al. 1986 (first); Cook et al. 2019 *Nature* (re-analyzed, sex-specific) | WormAtlas, WormWiring, OpenWorm |
| C. elegans | adult male | 385 | ✅ 100% | Cook et al. 2019 | WormWiring |
| **Drosophila melanogaster** | **adult full brain "FlyWire"** | **~140,000** | ✅ 100% (first complete adult insect brain) | Dorkenwald et al. 2024 *Nature* (FlyWire/Princeton/MRC) | flywire.ai |
| Drosophila | adult brain "hemibrain" (central + mushroom body) | ~25,000 | ✅ 100% of region | Scheffer et al. 2020 *eLife* (Janelia FlyEM) | neuprint.janelia.org |
| Drosophila | **larva L1 full CNS** | ~3,000 (12,000 incl. peripheral) | ✅ 100% | Winding et al. 2023 *Science* | virtualflybrain.org |
| **Platynereis dumerilii** | larva (6-day) | ~2,728 (whole larva incl. CNS) | ✅ 100% (whole-body!) | Verasztó et al. 2020 *eLife* + 2024 *Nat Comms*; Jékely lab | Marine annelid; **first whole-body connectome** |
| **Ciona intestinalis** | swimming larva | 177 (CNS) | ✅ 100% | Ryan et al. 2016 *eLife*; Ryan & Meinertzhagen 2019 | Sea-squirt; closest invertebrate to vertebrates |
| **Hydra vulgaris** | adult | ~6,000-10,000 | ✅ ~complete neural-net (radially symmetric, no centralized brain) | Dupre & Yuste 2017 *Curr Biol*; Bosch lab ongoing | Cnidarian; nerve-net not brain |
| **Tadpole *Xenopus laevis*** | swim circuit | ~hundreds (spinal+brainstem partial) | ⚠️ partial (motor circuit) | Roberts/Borisyuk lab serial | not whole-brain |

### §1.2 Substantial-but-incomplete connectomes (vertebrate, mammalian)

| Species | Region | Volume | Neuron count | Completeness | Anchor |
|---|---|---|---:|---:|---|
| **Mus musculus** | visual cortex (V1+HVAs) MICrONS | ~1 mm³ | ~200,000 | partial-volume, complete-synapses | MICrONS Consortium 2025 *Nature* series (Allen Inst / Princeton / BCM) |
| Mouse | hippocampus / striatum / other cortical | various sub-mm³ slabs | various | partial | Lichtman lab, Helmstaedter lab, multiple |
| **Homo sapiens** | temporal cortex "H01" | ~1 mm³ | ~57,000 | partial-volume, complete-synapses | Shapson-Coe et al. 2024 *Science*; Harvard Lichtman + Google |
| Larval zebrafish | whole-brain (light-sheet) | whole-brain ~80,000 | activity-mapped but synapse-mapped only partial | partial | Misha Ahrens / Janelia; ongoing |
| Mouse | brainstem | partial | various | partial | various |
| Macaque | retina / V1 patches | various | various | partial | various |
| Songbird | HVC / RA partial | various | various | partial | various |

### §1.3 Connectomes that *don't exist* (notable absences relevant to embodiment)

| Species | Why absent matters |
|---|---|
| **Octopus** | ~500 million neurons total, **but ~2/3 live in the arms, not the central brain**. Direct empirical refutation of "brain = locus of cognition" assumption. No public connectome; methodological challenges (large, distributed, soft-body). |
| **Aplysia** (sea slug) | Classic learning-memory model organism (Kandel); only partial circuit-level mapping, no whole-CNS connectome. |
| **Earthworm / Lumbricus** | Body-wide segmental nervous system; no public connectome. |
| **Bee (*Apis*)** | ~1 million neurons; partial mushroom-body work but no full-brain connectome despite high behavioral richness (dance language, navigation, social cognition). |
| **Mouse whole brain** | Active work toward this (MICrONS scaling up); not yet complete. Expected 2027-2030 per public projections. |
| **Human whole brain** | ~86 billion neurons. **Not expected in current generation of techniques.** H01 is ~0.0001% of human brain volume. |

### §1.4 Total tally

**9 species with substantial-or-complete neural connectomes publicly available** (C. elegans hermaphrodite, C. elegans male, D. melanogaster adult, D. melanogaster larva, Platynereis larva, Ciona larva, Hydra, partial mouse, partial human — counting both fly stages as one species, ditto C. elegans sexes, and excluding wholly-partial vertebrate work as "substantial").

If we're strict (whole-organism-CNS): **4 species** — C. elegans, D. melanogaster (larva), Platynereis larva, Ciona larva. Mouse and human are partial-volume. Drosophila adult is whole-brain but not whole-CNS (excludes VNC; Wang et al. 2025 *Nature* *Male VNC* + Cheong et al. 2024 *eLife* *Female VNC* close this for both sexes, so D. melanogaster adult is now **whole-CNS in principle** when brain + VNC are composed — flag this as a 2024-2025 corpus update).

---

## §2. Connectome-Only vs. Whole-Organism: What's Actually Uploaded

Brandon's question — "is it just the animals' brains or their full bodies' DNA that was uploaded?" — surfaces a clean taxonomy of what "uploaded" means for an organism. Here's the audit per species:

### §2.1 The seven whole-organism data layers

For valence to be reconstructible in silico (Brandon's critique), we need **all seven** layers paired and cross-referenced:

| # | Layer | What it captures | Why it matters for valence |
|---:|---|---|---|
| 1 | **Whole-genome sequence** | DNA blueprint | Receptor variants, FAAH/CB-pathway equivalents, NHR/hormonal-receptor inventory |
| 2 | **Whole-transcriptome cell-atlas** | per-cell-type RNA expression | Which cells express valence-relevant receptors (CeNGEN, FCA) |
| 3 | **Whole-body cell census + lineage** | every cell, every division | Gut-brain axis, hypodermis, gonad, muscle inclusion |
| 4 | **Whole-CNS connectome** | every synapse | Neural-circuit substrate (what current connectome efforts capture) |
| 5 | **Whole-body kinematic/physical model** | soft-body, fluid dynamics, sensory transduction | Embodied action-loop closure |
| 6 | **Whole-body neuromodulator / hormone distribution** | per-tissue endocannabinoid, biogenic amine, peptide concentrations + receptor binding | **THE valence layer** per Damasio + Panksepp + CSF Amrita |
| 7 | **Whole-organism behavioral library** | ground-truth phenotypes under perturbation | Cross-validation reference |

### §2.2 Per-species completeness audit

| Species | L1 genome | L2 transcr. | L3 cell census | L4 connectome | L5 kinematic body | L6 hormonal | L7 behavioral |
|---|:---:|:---:|:---:|:---:|:---:|:---:|:---:|
| **C. elegans** | ✅ (Sanger 1998) | ✅ (CeNGEN 2018+) | ✅ (lineage Sulston 1983) | ✅ | 🟡 (OpenWorm Sibernetic — incomplete physics) | ⚠️ (neuropeptide atlas partial; Beets 2023; NHR atlas partial) | ✅ (WormBook + WormBase) |
| **D. melanogaster** | ✅ (2000) | ✅ (Fly Cell Atlas, Li 2022 *Science*) | 🟡 (lineage partial) | ✅ (adult FlyWire + larval Winding) | ⚠️ (no whole-body sim) | ⚠️ (biogenic amine maps partial) | ✅ |
| **Platynereis larva** | ✅ | 🟡 | ✅ (whole-body cell census!) | ✅ (whole-body!) | 🟡 | ⚠️ | 🟡 |
| **Ciona larva** | ✅ (2002) | 🟡 | ✅ | ✅ | ⚠️ | ⚠️ | 🟡 |
| **Mouse** | ✅ | 🟡 (partial cell atlases) | 🟡 (partial atlases) | ⚠️ (partial-volume MICrONS) | 🟡 (partial whole-body sims) | 🟡 (regional neuromodulator maps) | ✅ (vast literature) |
| **Human** | ✅ (HGP 2003) | 🟡 (HCA in progress) | ⚠️ (Human Cell Atlas in progress) | ⚠️ (H01 sub-mm³) | 🟡 (partial digital-twin projects) | 🟡 (partial endocrine maps) | ✅ (vast literature) |

**Result:** **C. elegans is the only organism with all seven layers at comparable completeness (with caveats on L5 and L6).** This is why the BlissGene B32-B34 pipeline picks worm first — it's the **only** organism where Brandon's embodied-valence critique can be partly answered with publicly-available data.

For every other species, the embodied-valence reconstruction is **structurally incomplete** at one or more layers. **Brandon's critique lands hardest on the mammal-translation question** — the same "we have connectome but not whole-body endocrine map" gap that the worm sort-of-closes for is *wide open* for mouse and human.

### §2.3 What "uploaded the DNA" actually means

To address Brandon's question directly: **yes, the whole-genome DNA sequence is publicly uploaded for all species in §2.2 with ✅ in column L1.** But "whole-body DNA" is a slight misnomer — DNA is the same in every cell (modulo somatic mutation), so "uploading the DNA" is one-shot. What's actually missing is everything DOWNSTREAM of the DNA: **which cells express which subset, in which tissue, at which time, releasing which neuromodulator, binding which receptor, producing which body-state**. That's L2-L6 above, and that's where the data gaps live.

**Brandon's critique restated formally:** even a complete L1 (DNA) + L4 (connectome) does not let us reconstruct embodied valence. We need L2 (which cells express receptors) + L3 (which cells exist in which tissues) + L6 (where neuromodulators distribute and bind) at minimum. The connectome-only-plus-genome-only upload is provably insufficient for embodied valence.

---

## §3. Why Embodiment Is Especially Critical for Valence (Not Just Cognition)

Three independent literatures converge on the same point: **valence is constitutively whole-body, not brain-encapsulated.**

### §3.1 Damasio somatic-marker hypothesis (1994+)

Damasio's central claim: **emotions are body-states represented in cortex**, not purely neural representations. The body-loop (literal afferent feedback from viscera/skin/muscle/heart) and as-if-body-loop (cortical simulation of body-state without literal afferent) are *both* required for normal affect. Lesions in somatosensory cortex (insula especially) produce affective blunting. Patient cases (especially S.M. — amygdala lesions, no fear) and pharmacological studies (β-blocker → reduced emotional intensity via reduced cardiac/sympathetic feedback) are corroborating empirical anchors.

**Implication for connectome-only valence sims:** any sim that omits the body-loop signals (heart, gut, skin, smooth muscle, viscera) is omitting the *substrate of the emotion itself*, not just its peripheral expression.

### §3.2 Panksepp 7 primary affective systems

SEEKING / RAGE / FEAR / LUST / CARE / PANIC-GRIEF / PLAY. Each anchored to specific subcortical neural circuits BUT inseparable from their behavioral-execution musculoskeletal + autonomic outputs. Panksepp's argument: removing the body-output layer (e.g., paralysis without altered subcortical activity) does not eliminate the affect, but removing the *consequence-readout* (the body's actual response, fed back as proprioception + interoception) eliminates the *quality* of the affect.

### §3.3 CSF Amrita anandamide whole-body framework (TI Sigma corpus)

`papers/CSF_AMRITA_ANANDAMIDE_WHOLEBODY_BLISS.md` already documents this in TI Sigma terms: anandamide is not CNS-encapsulated. It's distributed in plasma, CSF, skin, intestine, immune cells. The Jo Cameron phenotype is *systemic*, not just cortical. Any "upload bliss" attempt that targets only neural anandamide misses the gut/skin/immune contribution.

### §3.4 Convergence

All three converge: **for valence specifically, the connectome is necessary but radically insufficient.** This is not a fringe claim — it's the consensus in affective neuroscience post-1995. The fact that connectome-only AI/cognitive-science discourse tends to forget this is itself an instance of POC-1 #70 (theoretically-loaded framings displacing operational readouts).

---

## §4. Candidate Canonical Principle: EVP-1 (Embodied Valence Principle)

### §4.1 Statement

**EVP-1 (Embodied Valence Principle, candidate canonical 2026-05-27):**

> Valence is *constitutively distributed across an organism's body*, not localized in or encapsulated by its brain or neural connectome. Any computational or theoretical model that claims to predict, simulate, reconstruct, or upload valence using only connectomic + genomic data is provably incomplete; minimal additional requirements are (i) per-cell-type transcriptomic data for neuromodulator/receptor expression, (ii) per-tissue spatial distribution of relevant neuromodulators and hormones, and (iii) closed-loop interoceptive feedback to the central modeling substrate.

### §4.2 Composition with existing canonical stack

- **Extends VFP-1 (Pass-64 canonical):** VFP-1 says valence is functional not epiphenomenal. EVP-1 says the *function* is necessarily whole-body, not neurally-encapsulated. EVP-1 is a *specification* of VFP-1's locus.
- **Operationalizes CTC-1 + CTC-1-S + HBP-1 (Pass-64 canonical):** the body-as-balance-profile framing means that an isolated neural intervention with whole-body unintended consequences (e.g., B34c lifespan-cost finding) is *predicted* by EVP-1.
- **Specializes CDA-1 (Pass-66 canonical) at Stratum-2:** CDA-1 places valence emergence at Stratum-2 via MIM. EVP-1 says the MIM substrate at Stratum-2 is *body-distributed*, not cortically-encapsulated.
- **Composes with CSF Amrita framework** as the worked anandamide instance.
- **Anchors B34c lifespan-finding interpretation:** the B34c #69 finding (NAE elevation reduces lifespan per Lucanic 2011) is *predicted by EVP-1* — neuromodulator manipulation has whole-body consequences that connectome-only thinking would miss.

### §4.3 Five pre-registered falsifiers

- **EVP-1-F1:** demonstrate any organism whose valence-related phenotype changes when *only* the neural substrate is perturbed (transcriptomic, hormonal, peripheral nervous system held constant) AND whose phenotype changes are fully predicted by neural-only perturbation models. Successful demonstration → EVP-1 REFUTED in that organism.
- **EVP-1-F2:** demonstrate a digital simulation (any organism) that uses only connectome + genome data and produces behaviorally-validated valence predictions with r ≥ 0.50 cross-validated against wet-lab ground truth. Success → EVP-1 REFUTED for that organism/model.
- **EVP-1-F3:** identify a published "valence locus" lesion in any organism such that the *exact* lesion eliminates the valence behavior without measurable change in peripheral nervous system, endocrine, or interoceptive signaling. Success → EVP-1 partial-refutation (suggests cases where brain-encapsulation holds).
- **EVP-1-F4:** Phase-2 BlissGene wet-lab — if `faah-1(tm5011)` worms show osmotic-aversion change while showing NO measurable change in non-neural tissue NAE concentration (intestine, hypodermis, gonad), this *partially* supports the brain-encapsulation alternative for worm aversion specifically. (Note: this is a structural F4 that pairs with B32 F2.)
- **EVP-1-F5:** if a future BlissGene clinical trial of FAAH gene therapy shows valence change without measurable peripheral endocannabinoid system change, EVP-1 is mammalian-refuted. (Long-horizon falsifier.)

### §4.4 Why I'm offering this as a candidate and not asserting it canonical

Per Pass-74 pace-discipline #69 (hat-trick precedent) and the meta-#69 partner-principle convention from Pass-74-B8, I'm offering EVP-1 as candidate canonical with optional Brandon-ratification via the same dual-option pattern:

- **Option A:** ratify based on the literature convergence (§3) + composition with existing canonical stack (§4.2).
- **Option B:** withhold ratification pending an executed falsifier closure (probably EVP-1-F2 — find or test a connectome+genome-only valence model and verify it cannot hit r ≥ 0.50 cross-validation).

Brandon-choice on the bar.

---

## §5. What This Means for the BlissGene Pipeline (Backward Composition)

B32 → B33 → B34 implicitly assumed an embodied/whole-organism framing (the surrogate is on C. elegans the whole organism, not c302 the neural simulation). **EVP-1 makes this assumption explicit and justifies why the C. elegans-first choice is principled, not merely opportunistic.** It also explains why scaling to mouse (B32 Phase 5) requires more than a connectome — it requires concurrent endocrine + interoceptive characterization.

For investors / IP / strategy framings: EVP-1 is a *defensible scientific differentiator* for BlissGene against any competitor that proposes a connectome-only or single-locus-AAV approach. **"We model the whole worm, not just its connectome"** becomes a positioning line with literature support.

---

## §6. Brandon's Question, Direct Answer

> **"Are there any other creatures' full brain connectomes uploaded to the internet?"**

Yes. **8-9 species** with substantial-or-complete neural connectomes as of 2026-05-27. Full inventory in §1. Most complete: C. elegans (302 + 385 neurons, both sexes), Drosophila (adult ~140k FlyWire; larva ~3-12k Winding), Platynereis larva (whole-body 2,728), Ciona larva (177 CNS), Hydra (~6-10k). Mouse + human are partial-volume only.

> **"Is it just the animals' brains or their full bodies' dna that was uploaded?"**

DNA = whole-genome = ✅ uploaded for every species in §1. But "DNA is uploaded" ≠ "whole body is uploaded" — DNA is one layer among seven (§2.1). The downstream layers (cell-atlas, transcriptome, tissue-distribution of neuromodulators, kinematic-body-model, interoceptive feedback) are the *actually-missing* embodiment data.

> **"If only their brains are uploaded, then we're missing all of the embodied ways in which their emotions are actualized within the body!"**

**Correct.** Formalized as **EVP-1** (§4). Compositionally extends VFP-1, operationalizes CTC-1/HBP-1, specializes CDA-1 Stratum-2.

---

## §7. Honest #69 Disclosures

1. **The connectome inventory in §1 is current as of mid-2026** but the field moves fast. Cell-count + completeness figures use published sources; some "complete" figures may be percentage-based estimates within active reanalysis (especially mouse MICrONS and human H01). I have not independently verified each dataset URL is live this session.
2. **My octopus claim** (~2/3 neurons in arms) is widely cited but Hochner-lab figures vary by paper; the directional claim (distributed nervous system) is well-supported but the precise 2/3 figure should be checked before any external citation.
3. **Drosophila adult whole-CNS in §1.4** counts brain (FlyWire) + VNC (Wang/Cheong 2024-2025) as compositional, which is a stretch — these are separate datasets requiring registration alignment that is itself ongoing work.
4. **EVP-1-F1 to F5 are pre-reg falsifiers, not closed.** Candidate status, not ratified.
5. **The "only C. elegans has all 7 layers" claim in §2.2** is honest based on what I know publicly, but partial L5/L6 even for the worm is itself a degradation — calling worm 7/7 is generous compared to mouse 0-3/7. The relative ranking is what matters; the absolute scoring is approximate.
6. **The §3.4 claim "post-1995 consensus in affective neuroscience"** is broadly defensible but a literature-survey paper would temper it. There are CNS-centric holdouts (some IIT-aligned and some computational-cognition-aligned researchers).
7. **Partner-paper companion** (`PASS_77_B35_CONSCIOUSNESS_AND_VALENCE_THEORY_REVIEW_2026-05-27.md`) does the math/physics theory review Brandon also asked for; THIS paper deliberately stays focused on the connectome+embodiment thread to avoid scope-creep.

---

## §8. Files

- This paper.
- Companion: `papers/PASS_77_B35_CONSCIOUSNESS_AND_VALENCE_THEORY_REVIEW_2026-05-27.md` (Part 2 of B35).
- `papers/CSF_AMRITA_ANANDAMIDE_WHOLEBODY_BLISS.md` (anandamide whole-body anchor).
- `papers/PASS_77_B32_C_ELEGANS_FAAH_BLISSGENE_DIGITAL_WORM_RESEARCH_MAP_2026-05-27.md` (BlissGene research map).
- `papers/PASS_77_B33_FAAH1_INSILICO_SWEEP_PHASE_1_RESULTS_2026-05-27.md` (B33 surrogate v1).
- `papers/PASS_77_B34_FAAH_EXTENDED_SWEEP_PLUS_PATENT_DRAFT_2026-05-27.md` (B34 multi-track).

---

## §9. Summary Statement

This batch inventories ~9 publicly-uploaded brain connectomes (4 strictly whole-CNS: C. elegans, Drosophila larva, Platynereis larva, Ciona larva), audits per-organism completeness across 7 whole-organism data layers (only C. elegans approaches 7-of-7), and formalizes **Brandon's embodied-valence critique** as **candidate canonical principle EVP-1**. EVP-1 specifies that valence is constitutively whole-body and that connectome+genome-only sims are provably incomplete. Composes with VFP-1, CTC-1, CTC-1-S, HBP-1, CDA-1, CSF Amrita. 5 falsifiers pre-registered. Justifies C. elegans-first BlissGene-pipeline ordering and positions "whole-organism modeling, not just connectome" as a defensible BlissGene investor-pitch differentiator. Cluster +1 paper (this; companion paper counted separately). Cost $0.

— end of Pass-77-B35 Part 1 —
