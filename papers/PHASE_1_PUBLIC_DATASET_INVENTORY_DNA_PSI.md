# Phase 1 Deliverable: Public Animal Genomic-Outcome Dataset Inventory for DNA-Anchored Psi-Signature Validation

**Date:** 2026-04-30
**Phase:** 1 of 6 (per `RESEARCH_ROADMAP_DNA_ANCHORED_PSI_SIGNATURE.md`)
**Cost:** $0 (all datasets free, public-access)
**Status:** Inventory complete; ready for Phase 2 (pharmacology simulator baseline validation) and Phase 3 (DNA-anchored module design)

## §1 — Inventory of $0-Access Animal Genomic-Outcome Datasets

### Tier A: Highest priority for Brandon's specific endocannabinoid focus

| Dataset | Species | Cohort | Genome Type | Phenotype/Outcome Coverage | Endocannabinoid Relevance | Access |
|---------|---------|--------|-------------|----------------------------|---------------------------|--------|
| **Mouse Phenome Database (MPD)** | Mouse | 70+ inbred strains, 400+ datasets, ~10,000+ animals | SNP genotypes, some WGS | Behavior (open-field, elevated-plus-maze for anxiety), pharmacology, physiology, disease susceptibility | FAAH-KO mouse studies, CB1-KO mouse studies, multiple cannabinoid pharmacology datasets indexed | https://phenome.jax.org — registration free |
| **Collaborative Cross (CC)** | Mouse | 70+ recombinant inbred strains | Full SNP imputation (~4M markers) | Standardized behavior, drug response, disease | Used in cannabinoid response studies; high genetic diversity captures CB1/FAAH variant effects | https://csbio.unc.edu/CCstatus — free |
| **Diversity Outbred (DO)** | Mouse | Heterozygous outbred from CC founders | High-resolution genotypes | Wide phenotype range | Better for mapping continuous traits (drug response curves) | https://www.jax.org/strain/009376 — free metadata, papers public |

### Tier B: Broader vertebrate datasets for cross-species validation

| Dataset | Species | Cohort | Phenotype Coverage | Access |
|---------|---------|--------|---------------------|--------|
| **Rat Genome Database (RGD)** | Rat | Multiple strains (BN, SHR, F344, etc.) | Disease models, behavior, pharmacology | https://rgd.mcw.edu — free |
| **Dog10K Genomes Project** | Canis | 10,000+ dogs across breeds | Breed traits, disease, behavior | https://dog10kgenomes.com — free, papers public |
| **1000 Bull Genomes** | Bovine | 4,500+ bulls | Production traits, longevity, fertility | https://www.1000bullgenomes.com — free |
| **Norwegian Salmon Genome Project** | Salmon | Multiple cohorts | Growth, disease resistance, behavior | https://www.salmobase.org — free |

### Tier C: Human reference panels for Brandon-specific extrapolation comparison

| Dataset | Cohort | Use | Access |
|---------|--------|-----|--------|
| **1000 Genomes Project** | 2,504 humans, 26 populations | Allele frequency reference for Brandon's variants | https://www.internationalgenome.org — free |
| **gnomAD v4** | 807,162 humans (730K exomes, 76K genomes) | Most comprehensive allele frequency reference | https://gnomad.broadinstitute.org — free |
| **OpenSNP** | ~7,000 self-uploaded 23andMe / AncestryDNA users with self-reported phenotypes | Direct comparison cohort for Brandon's data | https://opensnp.org — free, public domain |
| **Personal Genome Project (PGP)** | ~5,000 fully-public WGS + phenotype | Highest-quality public human comparison | https://www.personalgenomes.org — free |

### Tier D: Pharmacological-effect ground-truth databases

| Database | Content | Use | Access |
|----------|---------|-----|--------|
| **DrugBank** | 14,000+ drug entries with mechanism, pharmacokinetics | Ground-truth pharmacological effect sizes | https://go.drugbank.com — academic free |
| **PharmGKB** | Pharmacogenomic gene-drug-phenotype associations | Direct genotype→drug-response baseline (the conventional baseline LCC must beat) | https://www.pharmgkb.org — free |
| **ChEMBL** | 2M+ bioactivity assay results | Quantitative drug-target interaction data | https://www.ebi.ac.uk/chembl — free |
| **CB1/CB2/FAAH literature corpus (PubMed)** | Multi-decade endocannabinoid pharmacology | Brandon's specific "already-accurate published rodent" reference | https://pubmed.ncbi.nlm.nih.gov — free |

## §2 — Recommended Phase 2-3 Pipeline Using This Inventory

### Phase 2: Conventional baseline establishment (~1 week, $0)
1. Pull 50-100 published rodent endocannabinoid pharmacology trials from PubMed (FAAH inhibitor effects on AEA/anxiety/pain; CB1 antagonist effects on food intake; CB2 agonist effects on inflammation)
2. Pull matched genetic data from MPD where strain-level pharmacology was reported
3. Run `pharma_simulator_validation.py` on this clean test set
4. Run conventional polygenic risk score baseline on same predictions (e.g., using PRSice-2 or PLINK on MPD genotypes)
5. Document baseline: "Conventional methods predict X% of variance in rodent endocannabinoid pharmacology response"

### Phase 3: DNA-anchored LCC module design (~1 week, $0)
1. Design LCC R(A,B) integral where:
   - A = animal SNP profile at endocannabinoid system loci (FAAH, CNR1, CNR2, MGLL, NAPE-PLD, DAGLA, DAGLB)
   - B = pharmacological response phenotype (continuous, e.g., %Δ AEA after FAAH inhibition)
2. Implement TI Sigma Crystal aspectual decomposition over the 5 truth values for prediction confidence
3. Hold out 20% of animals for blind testing
4. Pre-register predictions BEFORE looking at held-out data

### Phase 4: Validation (~2 weeks, $0)
1. Score LCC predictions vs conventional PGS baseline on held-out animals
2. **Falsification threshold: LCC must outperform PGS by ≥5 percentage points on directional accuracy AND magnitude-within-2× to count as positive evidence**
3. Document outcome honestly regardless of direction
4. If positive: proceed to Phase 5 (Brandon DNA extrapolation, which is now feasible — DNA already uploaded)
5. If negative: write falsification paper documenting the negative result

## §3 — Why This Inventory Matches Brandon's Specific Vision

Brandon's clarification (2026-04-30): "the published studies on rats/mice on the endocannabinoid system drug trials." The MPD + RGD + Tier D combination is exactly the right substrate for that vision:
- MPD/CC have rodent genetic + pharmacological data with FAAH/CB1/CB2 phenotype coverage
- PharmGKB has the conventional-baseline genotype→drug-response associations LCC must beat
- PubMed has the published rodent endocannabinoid effect-size literature Brandon cited
- All Tier A-D datasets are FREE — total cost of this entire inventory + Phase 2-4 execution: $0
- Phase 5 (Brandon-DNA extrapolation) is now CONDITIONAL on Phase 4 positive outcome AND is also $0 (just applies validated module to already-uploaded file)

## §4 — Status

Phase 1 inventory complete. Awaiting Brandon's authorization to launch Phase 2 (pharmacology simulator baseline validation against MPD + PubMed).

Recommended next step: launch Phase 2 in parallel with continuing Trial 005 telepathy reveal. Both are $0 and parallelizable.
