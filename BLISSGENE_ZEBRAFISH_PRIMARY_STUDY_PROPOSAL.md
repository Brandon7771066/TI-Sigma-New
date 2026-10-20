# BlissGene zebrafish inventory and primary-study proposal

Date: 2026-10-14. Status of the proposed experiment: PLANNED. Nothing in this file is a zebrafish result.

Governing standard: `TI_SIGMA_RESEARCH_INTEGRITY_RULES.md`. A fish behavior study is not evidence of a human treatment. A failed computational model is not evidence of noncomputability. FAAH-OUT language stays a human-literature hypothesis until an ortholog artifact exists.

## Inventory of what is actually in the repository

| Material | Where | What it is | What it is not |
| --- | --- | --- | --- |
| C. elegans FAAH-1 sweep | `analyses/pass77_b33_faah1_insilico_sweep/`; paper `PASS_77_B33_...md` (2026-05-27) | 4,800 surrogate worm-runs, seed 20260527. Literature-shaped Hill curve, not OpenWorm c302. Pre-registered P1 (osmotic aversion at knockdown ≥ 0.50 falls below 70% of wild type) is recorded as a marginal fail: the paper says the cell stayed at 73–82% of wild type. Falsifier F1 (some behavioral signature exists) was not refuted inside the surrogate | Not a zebrafish experiment. Not a wet-lab result. Not Jo Cameron |
| Pharma baseline | `analyses/pharma_baseline/results_2026-05-08.txt` | 12 published experiments. Directional accuracy 12/12 ties an always-positive baseline, because every empirical effect in the set is positive. Magnitude-within-2× is 75% versus 66.7% for a mean-magnitude baseline | Not a trial. The Jo Cameron row in `linear_baseline.py` is a hardcoded pair `(100.0, 134.3)` |
| Human FAAH-OUT / Jo Cameron | pitch and book prose, including `book/ch15_lcc.md` | Motivation for a hypothesis | No genotype file, no zebrafish ortholog alignment, no therapeutic outcome table |
| Larval zebrafish mention | `papers/PASS_77_B35_...md` | One inventory row: whole-brain light-sheet, about 80,000 neurons, synapse map partial, Ahrens/Janelia | No recording, no endpoint, no statistic |
| Koyama 2026 figures | ChatGPT recovery dossier, `TI_Sigma_Zebrafish_Phase4_empirical_audit.csv` (SHA-256 `cf7e6261824a5b1e70bbee2df9145ee7daec7d5e935ff45ab369fb79558628ad`) | Published transcription: 181 fish, learner fraction 46.4%, 804 event cells across 10 fish, danger reassignment 89.7%, safety reassignment 81.0% | Not a TI Sigma feature test. Raw neural binaries are still blocked. Not refit in this repo |
| Krug 2018 faah2a locomotor statistics | same Phase 4 CSV | Published transcription: genotype main effect F = 1.89 and genotype × nicotine F = 1.224, both P > 0.05. Nicotine F = 81.51, P < 0.0001. Phase 6 prior: faah2a not detected by whole-mount ISH in the larval nervous system | Not a new fish experiment. Not an FAAH-OUT ortholog. Not a BlissGene knockdown |
| Phase 8 gene screen | dossier file `TI_Sigma_Zebrafish_Phase8_Gene_Screen.csv` | Hand-assigned component scores. cnr1 0.778, faah2a 0.681, faah 0.667 | Screen weights, not measured effects |
| Drosophila MIM | `main` at `b5955f25` and the master-ledger run summary | Whole-brain model execution and sensory propagation | Not a learning result and not a zebrafish result |
| LCC vs synchronized brains | `analyses/lcc_uop_openneuro/` and `PASS_77_B164` | Human dual-EEG. The coupling features did not track duet versus metronome. L_hybrid did not beat raw correlation | The test of “does current LCC predict synchronized brain activity?” already exists, and it is negative on that dataset |

Species actually studied in stored analyses: a C. elegans behavioral surrogate, a human EEG hyperscanning set, human actigraphy, and a fly connectome model. No Danio rerio recording is in the repo. The Koyama and Krug rows above are literature numbers copied into CSVs. They do not change BG-ZF-01. The Krug locomotor null and the larval in-situ limit are additional reasons the FAAH arm stays no-go until an orthology memo exists.

## Where LCC fits

LCC is relevant to BlissGene only as a later incremental test of coupling, and only after the index is refined.

The stored human test asked the question directly: does an LCC index predict joint behavioral synchronization and the accompanying inter-brain signals better than ordinary correlation? On ds007471 it did not. On Depresjon the hybrid index was worse than raw features (AUC 0.200 versus 0.520). Those negatives stay attached to any future fish proposal.

A zebrafish whole-brain recording could eventually host a better test, because many regions are measured in one animal and a conventional synchrony measure can be checked against a known stimulus. That test is Level 1 in the strategy note. It is not the first experiment. Using today’s L_hybrid on fish would ignore the index’s own incremental failures.

Level 2 (a GILE or HEM dimension corresponds to a perturbed biological process) waits on a replicated phenotype and a frozen feature definition. Level 3 (noncomputability, halting, libertarian free will) is a separate formal program. A finite fish dataset cannot establish it.

## Primary study — BG-ZF-01

One biological question: does a standardized acute stressor change locomotor behavior in larval zebrafish after a motor-capacity control, and do any prespecified extra features add prediction beyond that phenotype?

FAAH manipulation is outside this study. It becomes eligible only after a written orthology and expression memo for the zebrafish genes that would stand in for FAAH and FAAH-OUT. That memo is not in the repo. A human-specific regulatory RNA is not assumed to have a fish equivalent.

### Hypothesis

Acute stressor versus sham changes one locomotor endpoint (thigmotaxis or distance traveled; exactly one is locked before the confirmatory batch). A motor-capacity assay (for example touch-evoked swim or total swim speed outside the anxiety arena) is the check that the animals can still move.

### TI Sigma prediction, frozen before outcomes

Primary model A uses only conventional behavioral variables.

Model B, the TI challenger, is not L_hybrid and not a GILE composite fit after seeing the data. For BG-ZF-01 the TI slot is empty on purpose: no TI feature is allowed to be the primary endpoint.

Model C is reserved for a follow-on batch, BG-ZF-01b, and only if all of the following are true: the phenotype replicates, a conventional within-brain or between-region correlation already tracks the stressor, and the coupling feature was written down before that batch. The coupling feature must beat that conventional correlation on held-out animals. If it does not, the result is recorded as a negative and L_hybrid is not revived to replace it.

GILE weights are not estimated in this study. The stored specifications (√2−1 / 0.25 / 0.18 / 0.15, and the market 0.20 / 0.25 / 0.25 / 0.30) stay specifications.

### Controls, blinding, exclusions

- Arms: sham and stressor. No drug arm.
- Randomization of well or lane, and blinded scoring of the primary endpoint.
- Exclusions written before the run: tracking failure, unhealthy larva, missing video, experimenter note of a handling error. Exclusions are counted and reported.
- Positive control for the assay itself: the stressor must move the conventional endpoint in the expected direction in the pilot. If it does not, the assay is changed before any TI feature is discussed. That is a methods failure, not a TI Sigma result.

### Sample size

No fish variance is in the repo, so no powered n is claimed. Planning figure only: for a two-sided two-sample test at α=0.05 and 80% power, a standardized effect of 0.8 needs about 26 animals per arm. The actual n is computed from a pilot (12 per arm) that estimates the endpoint SD and is not used in the confirmatory test.

Go/no-go on size: if the pilot SD implies that a standardized effect of 0.5 would require more than 40 animals per arm, BG-ZF-01 stops or the endpoint changes. The cap is a resource rule, not a scientific finding.

### Go / no-go

1. Orthology memo absent: no FAAH or FAAH-OUT manipulation in fish. Current state: no-go for that arm.
2. Pilot does not move the conventional endpoint, or the motor assay shows the stressor merely immobilizes the fish: no-go. Do not interpret a GILE score.
3. Confirmatory batch: report the effect size and interval for model A. TI features stay out of the primary sentence.
4. BG-ZF-01b opens only after a second, independent batch reproduces the phenotype, and only with a coupling feature that was frozen beforehand and is required to beat raw correlation. The ds007471 and Depresjon negatives are cited in that preregistration.
5. Human therapeutic language is out of scope until mammalian evidence exists. This study cannot produce that evidence.

### What would count as a result

A replicated conventional phenotype is the first biological deliverable. An incremental win is a later, preregistered coupling feature beating raw correlation on held-out fish. Either outcome is reportable. A retrospective GILE reading of the videos is not.
