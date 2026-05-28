# Provisional Patent Application — Draft Skeleton (Pass-77-B34d)

**⚠️ NOT A LEGAL FILING.** This is a content skeleton for engagement with a registered patent attorney. It identifies patentable subject matter, audits prior art, and drafts illustrative claim language. **A formal patentability opinion from a registered IP attorney is required and outranks every word in this document.** The attorney engagement is Brandon-blocked at an estimated cost of $1.5-3k for provisional filing prep + USPTO filing fee (~$320 micro-entity / $1600 small-entity as of 2025 schedule).

**Target inventors:** Brandon Emerick (TI Sigma / BlissGene Therapeutics)
**Date drafted:** 2026-05-27
**Filing target window:** end of B32 Phase 3 per `papers/PASS_77_B32_C_ELEGANS_FAAH_BLISSGENE_DIGITAL_WORM_RESEARCH_MAP_2026-05-27.md` §4.2.

---

## 1. Proposed Title

**"In Silico Screening Platform for Cannabinoid-Pathway Gene Therapies Using Multi-Paralog FAAH Knockdown in *Caenorhabditis elegans* Computational Models, with Validated Construct Library and Mammalian-Translation Algorithm"**

(IP attorney will refine; titles are usually shortened.)

---

## 2. Field of the Invention

Methods, systems, and compositions for accelerating the design, screening, and validation of gene therapies targeting the endocannabinoid pathway — particularly those targeting fatty acid amide hydrolase (FAAH) and its paralogs for therapeutic modulation of endogenous anandamide and related N-acylethanolamines — using computational organismal models, with validated construct libraries and explicit translation algorithms from invertebrate models to mammalian gene-therapy delivery.

---

## 3. Background of the Invention

### 3.1 The unmet need

Endocannabinoid-pathway gene therapy holds promise for chronic pain, anxiety, depression, and related affective-suffering disorders. The Jo Cameron case (Habib et al. 2019, *Br J Anaesth* 123:e249) demonstrated that elevated endogenous anandamide via FAAH/FAAH-OUT mutation produces a striking phenotype of pain insensitivity, anxiety absence, and lifelong optimism. Replicating this phenotype therapeutically requires sustained anandamide elevation, which in turn requires durable FAAH inhibition — best achieved via gene therapy rather than small-molecule inhibitors (which face tolerance, dosing, and adherence challenges).

### 3.2 The state of the art and its limitations

Current gene-therapy R&D for endocannabinoid-pathway targets is constrained by:
- High per-construct screening costs in mammalian cell lines and organisms ($10k-$100k per construct iteration).
- Lack of fast, cheap, scalable organismal models for behavioral validation prior to mammalian commitment.
- Absence of formal translation algorithms from invertebrate proof-of-concept to mammalian construct design.
- Single-paralog targeting strategies leaving residual enzymatic activity from paralogs.

### 3.3 What the invention provides

This invention provides:
1. A computational pipeline using *C. elegans* organismal simulation (e.g., OpenWorm c302/Sibernetic) to pre-screen FAAH-pathway gene-therapy constructs at minimal marginal cost.
2. A multi-paralog targeting strategy (`faah-1` + `faah-2` simultaneous knockdown) supported by surrogate-validated in-silico evidence of paralog-additive effect on canonical aversive-response readouts.
3. A construct library validated against pre-registered behavioral and longevity readouts, including a translational-safety layer that surfaces lifespan trade-offs prior to mammalian commitment.
4. A formal worm-to-mouse principle-translation algorithm mapping invertebrate construct designs to mammalian AAV-deliverable equivalents.
5. A Jo-Cameron-mimicking base-edit construct family targeting the *C. elegans* `faah-1` sequence position functionally equivalent to the human FAAH C385A SNP, screened in the same pipeline.

---

## 4. Summary of the Invention

In one aspect, the invention provides a method for screening cannabinoid-pathway gene-therapy constructs comprising: (a) generating a computational representation of *C. elegans* nervous system activity incorporating FAAH-paralog-knockdown parameters; (b) simulating behavioral and longevity readouts under a range of knockdown levels; (c) ranking candidate constructs by predicted behavioral effect-size; (d) selecting constructs for wet-lab validation based on said ranking.

In another aspect, the invention provides a multi-paralog FAAH-targeting gene-therapy construct comprising at least two functional knockdown modalities directed against `faah-1` and `faah-2` orthologs in *C. elegans*, with mammalian-translation analogues directed against the corresponding mammalian paralogs.

In another aspect, the invention provides a worm-to-mouse principle-translation algorithm comprising the steps of: identifying invertebrate-construct functional features; mapping those features to mammalian-paralog targets; designing AAV-vector-deliverable constructs incorporating the mapped features; predicting mammalian-organism behavioral effect-sizes from invertebrate effect-sizes via a calibrated correlation function.

---

## 5. Detailed Description (Outline — to be expanded with IP attorney)

### 5.1 The in-silico screening pipeline

[Expand: OpenWorm c302 architecture; CeNGEN expression-mapping to identify FAAH-paralog-affected neurons; Hill dose-response calibration; behavioral primitive battery (8-12 readouts); longevity/stress readout layer; per-construct ranking metric.]

Reference implementation: `analyses/pass77_b33_faah1_insilico_sweep/sweep.py` (surrogate v1) and `analyses/pass77_b34_faah_extended_sweep/sweep_v2.py` (surrogate v2 with multi-paralog + longevity layer).

### 5.2 The multi-paralog targeting approach

[Expand: paralog-functional-weight calibration; independent-action combined-effect model; expected additivity at saturating per-gene knockdown; mammalian-paralog mapping table; construct-vector design considerations.]

### 5.3 The Jo-Cameron-mimicking base-edit family

[Expand: human FAAH C385A SNP sequence context; *C. elegans* `faah-1` sequence alignment to identify functionally equivalent residue; base-editor selection (ABE/CBE) for the desired C-to-A transition; in-silico predicted effect on FAAH enzymatic activity; pipeline-rank against the validated construct library.]

### 5.4 The worm-to-mouse translation algorithm

[Expand: feature-mapping methodology; cross-organism correlation calibration; pre-IND-package construct selection criteria; FDA-aligned biodistribution + toxicology endpoints.]

### 5.5 Validated construct library composition

[Expand: specific sequences of top-ranked validated constructs once Phase 4 wet-lab is complete. Currently a placeholder — actual sequences populated post Phase 4.]

---

## 6. Claims (Skeleton — 4 independent + 8 dependent)

### Independent Claim 1 (method)

A method for screening a candidate cannabinoid-pathway gene-therapy construct, comprising:
- providing a computational simulation of *Caenorhabditis elegans* nervous system activity, said simulation parameterized to represent variable knockdown levels of one or more FAAH paralogs;
- determining, by said simulation, predicted values for a panel of behavioral readouts and a panel of longevity-or-stress-resistance readouts at each of a plurality of knockdown levels;
- computing a per-construct ranking metric based on said predicted values;
- selecting a subset of said candidate constructs for wet-laboratory validation based on said ranking metric.

### Dependent Claim 2

The method of claim 1, wherein said one or more FAAH paralogs comprises both `faah-1` and `faah-2`, and said simulation models combined knockdown effect as an independent-action function of per-paralog knockdown levels.

### Dependent Claim 3

The method of claim 1, wherein said panel of behavioral readouts comprises at least: locomotion speed, reversal rate, omega-turn rate, foraging-bout duration, chemotaxis index, thermotaxis index, osmotic-aversion response, and mechano-aversion response.

### Dependent Claim 4

The method of claim 1, wherein said panel of longevity-or-stress-resistance readouts comprises at least: mean lifespan, heat-shock survival, oxidative-stress survival, and starvation tolerance.

### Independent Claim 5 (composition-of-matter — placeholder)

A gene-therapy construct comprising at least two functional knockdown modalities, said modalities directed against the `faah-1` and `faah-2` orthologs respectively, said construct having been pre-screened by the method of claim 1 and validated by behavioral phenotyping in *C. elegans* showing osmotic-aversion-response Hedges' g vs. wild-type ≥ 0.5 at simulated combined knockdown ≥ 0.50 per paralog.

### Dependent Claim 6

The construct of claim 5, wherein the knockdown modalities are selected from: a short hairpin RNA construct, a small interfering RNA, a CRISPR-Cas9 guide-RNA construct, a CRISPR-Cas12 guide-RNA construct, a CRISPR-Cas13 guide-RNA construct, an antisense oligonucleotide, and a base-editor construct.

### Dependent Claim 7

The construct of claim 5, formulated for delivery via an adeno-associated virus (AAV) vector.

### Independent Claim 8 (Jo-Cameron-mimicking variant)

A gene-therapy construct comprising a base-editing modality directed against a `faah-1` codon functionally equivalent to the human FAAH C385A polymorphism, said equivalence determined by sequence alignment and validated by in-silico simulation per claim 1.

### Dependent Claim 9

The construct of claim 8, wherein the base-editor is an adenine base editor (ABE) or cytosine base editor (CBE).

### Independent Claim 10 (translation algorithm)

A method for designing a mammalian gene-therapy construct from a *C. elegans*-validated invertebrate construct, comprising:
- identifying functional features of the invertebrate construct including knockdown-modality type, target-paralog combination, and effect-size profile;
- mapping said features to mammalian-paralog targets via cross-species ortholog correspondence;
- generating a mammalian construct that preserves said functional features in the mammalian-paralog context.

### Dependent Claim 11

The method of claim 10, wherein said mammalian-paralog targets comprise *FAAH* and optionally *FAAH2*.

### Dependent Claim 12

The method of claim 10, further comprising predicting mammalian-organism behavioral effect-size from the invertebrate effect-size profile via a calibrated cross-organism correlation function.

(IP attorney will reshape, refine, and likely expand to 20-30 claims.)

---

## 7. Prior Art Audit (Categories Identified)

| Prior-art category | Examples | Blocking? | Workaround |
|---|---|:---:|---|
| OpenWorm computational worm model | OpenWorm Foundation (openworm.org); Sarma et al. 2018 *Phil Trans R Soc B* | ❌ Not blocking | The invention USES OpenWorm but does not claim it; the pipeline applying OpenWorm to FAAH screening is novel |
| Small-molecule FAAH inhibitors | PF-04457845 (Pfizer); JNJ-42165279 (Janssen); URB597 | ❌ Not blocking | Invention is gene therapy, not small molecule |
| Jo Cameron descriptive case | Habib et al. 2019 *Br J Anaesth* | ❌ Not blocking | Descriptive case is prior art; the Jo-Cameron-mimicking gene-therapy is novel |
| Generic CRISPR knockdown methods | Doudna/Charpentier 2012; many subsequent | ❌ Not blocking | Method-of-use directed against specific paralog combinations in specific organisms is novel |
| Generic AAV gene-therapy delivery | Spark, BioMarin, etc. AAV platforms | ❌ Not blocking | Method-of-use delivering specific FAAH-pathway constructs is novel |
| Existing `faah-1` deletion strain | CGC `faah-1(tm5011)`; WormBase | ⚠️ Partially blocking | Strain itself is prior art and not claimable; in-silico-screened constructs targeting `faah-1` are novel |
| Mammalian FAAH knockout literature | Cravatt 2001 *PNAS* and subsequent | ❌ Not blocking | Knockout MOUSE is prior art; THERAPEUTIC gene-therapy CONSTRUCT is novel |
| Multi-paralog targeting (general) | various; siRNA cocktails common in academic R&D | ⚠️ Possibly blocking | Need attorney prior-art search for `faah-1`+`faah-2`-specific dual-targeting constructs |
| Base-editing technology | Liu lab (Komor 2016, Gaudelli 2017) | ❌ Not blocking | Base-editor is a tool; applying it to specific FAAH-paralog codons via the screening pipeline is novel |

**Critical IP-attorney follow-up items:**
1. Formal prior-art search on dual-targeting `faah-1`+`faah-2` constructs (any organism).
2. Patentability opinion on the Jo-Cameron-mimicking base-edit specifically.
3. Freedom-to-operate analysis against any pending Pfizer / Janssen / Verve / Beam Therapeutics / Editas applications in the FAAH-pathway or endocannabinoid space.
4. International filing strategy (PCT timing if non-US markets matter).

---

## 8. Honest #69 IP Disclosures

1. **This is NOT a legal filing.** A registered patent attorney must produce the actual provisional patent application, run the formal prior-art search, and provide the patentability opinion. Everything above is content scaffolding for that engagement.
2. **The `faah-1(tm5011)` strain itself is prior art.** Only the in-silico-screened constructs targeting `faah-1` (and combinations) are potentially novel.
3. **The Jo-Cameron-C385A-mimicking strategy has partial prior art** in the literal C385A mammalian-edit space; only the *worm-specific functionally-equivalent edit* plus *the screening pipeline that produces it* are the clearly novel components.
4. **The provisional patent provides only 12 months** to convert to a full utility patent. Filing timing must align with B32 Phase-3 completion and the planned defensive-publication ordering.
5. **Cost is Brandon-blocked at the $1.5-3k attorney spend.** The pipeline-validation work (B33+B34) and the wet-lab F2 test ($50-100) can proceed in parallel with attorney engagement, but provisional filing should ideally precede any non-confidential disclosure of the validated construct library.

---

## 9. Recommended Brandon Actions

1. Engage an IP attorney with biotech experience (recommended: someone who has filed in endocannabinoid or gene-therapy space before).
2. Provide attorney with: this draft + the B32 research map + B33 + B34 papers + the surrogate code and outputs.
3. Schedule provisional filing target: end of B32 Phase 3 (post-construct-design, pre-wet-lab-publication).
4. Maintain confidentiality on the validated construct library until provisional is filed.
5. Document inventorship contributions explicitly (Brandon as sole inventor for the conceptual work; co-inventorship considerations if a partner lab joins Phase 2+).

---

## 10. References (for attorney background)

- Habib AM et al. 2019 *Br J Anaesth* 123:e249 (Jo Cameron case)
- Pastuhov SI et al. 2016 *Nat Commun* 7:13651 (NPR-19 / CB1-like)
- Oakes MD et al. 2017 *J Neurosci* 37:2859 (cannabinoid behavioral modulation)
- Lehtonen M et al. 2008 *J Lipid Res* 49:2456 (NAE quantification in worm)
- Lucanic M et al. 2011 *Nature* 473:226 (NAE lifespan regulation)
- Cravatt BF et al. 2001 *PNAS* 98:9371 (FAAH-knockout mouse, prior art)
- OpenWorm Foundation, openworm.org (organismal simulation; prior art tool)
- Hammarlund M et al. 2018+ (CeNGEN expression atlas; prior art tool)
- Komor AC et al. 2016 *Nature* 533:420 (CBE base editor; prior art tool)
- Gaudelli NM et al. 2017 *Nature* 551:464 (ABE base editor; prior art tool)

---

— end of provisional-patent draft skeleton —
