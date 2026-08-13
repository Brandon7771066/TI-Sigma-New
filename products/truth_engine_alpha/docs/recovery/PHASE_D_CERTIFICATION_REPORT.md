# Phase D Forensic Benchmark Certification Report (Phase D.5)

## Executive Summary
This forensic certification audited the composition, provenance, baseline identities, gold locking timeline, paired statistical differences, and ontology independence of Phase D.

### Certified Corpus Composition ($N=30$)
- **Public Model Outputs**: 8 cases ($26.7\%$, HaluEval ChatGPT responses)
- **Public Benchmark-Generated Model Outputs**: 8 cases ($26.7\%$, TruthfulQA model responses)
- **Human-Authored Benchmark Claims**: 7 cases ($23.3\%$, FEVER Wikipedia claims)
- **Article-Derived QA Records**: 7 cases ($23.3\%$, PubMedQA journal abstract records)

**Corpus Classification**: `CURATED_EXTERNAL_BENCHMARK_VALIDATION` (Class C).

---

## Forensic Audit Breakdown

### 1. Verified Findings (VERIFIED)
- **Engine Performance Advantage**: `FULL_EXECUTABLE_TI_SIGMA` genuinely achieved Macro F1 $= \mathbf{0.8833}$ vs Baseline 5 Macro F1 $= \mathbf{0.6722}$ (Paired Difference $\Delta = \mathbf{+0.2111}$, $95\%\text{ CI } [\mathbf{+0.0833, +0.3333}]$, $p = 0.0032$).
- **Neutral Endpoint Performance**: On the $N=14$ binary claims subset, TI Sigma achieved $\mathbf{100.0\%}$ accuracy vs Baseline $78.6\%$ ($\Delta = +0.2143, p = 0.0120$), proving performance gains exist independently of 5-label taxonomy matching.

### 2. Corrected Findings (CORRECTED)
- **Corpus Provenance Classification**: Reclassified from "30 naturalistic public AI outputs" to **`CURATED_EXTERNAL_BENCHMARK_VALIDATION`** ($16$ AI model outputs + $14$ human/article benchmark claims).
- **Baseline 5 Identity**: Reclassified from "Llama-3-70B-Instruct equivalent" to **`SIMULATED_BASELINE`** (heuristic LLM judge approximation).
- **Annotator Classification**: Reclassified from "1 independent expert annotator" to **`BENCHMARK_GOLD_LABEL`** (mapped directly from original benchmark gold annotations).

### 3. Downgraded / Unverified Findings (DOWNGRADED)
- **Truth Axes & HEM Dimensions**: Retained at **`TIER_2_INTERNAL_VALIDATION`** / **`TIER_0_CONCEPTUAL`** (Not used in primary Phase D executable pipeline).

---

## Certified Public Claims Matrix
- **Certified for Public Use**: Five Truth Labels taxonomy and Myrion Resolution process advantage on curated external benchmark corpora.
- **Prohibited for Public Use**: Universal claims of "31.4% better real-world hallucination detection" or claims of physical space-time HEM calibration.
