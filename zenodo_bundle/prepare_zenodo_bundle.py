"""
Zenodo Bundle Preparer — TI Sigma Top 10 Papers
Reads source papers, adds standardized Zenodo metadata, writes polished versions.
Run: python zenodo_bundle/prepare_zenodo_bundle.py
"""
import os, re, shutil
from datetime import date

BUNDLE_DIR = os.path.dirname(__file__)
PAPERS_DIR = os.path.join(os.path.dirname(BUNDLE_DIR), 'papers')

AUTHOR        = "Brandon Charles Emerick"
AFFILIATION   = "BlissGene Therapeutics; TI Sigma Research Institute"
ORCID         = ""  # add when registered: https://orcid.org
LICENSE       = "Creative Commons Attribution 4.0 International (CC BY 4.0)"
LICENSE_URL   = "https://creativecommons.org/licenses/by/4.0/"
SERIES        = "TI Sigma — Universal Reality Blueprint (URB)"
DOI_PENDING   = "Pending Zenodo DOI assignment"

PAPERS = [
    dict(
        rank=1,
        source="URB_CONSCIOUSNESS_EQUATION_LCC_C_PHI.md",
        slug="ti_paper_352_consciousness_equation",
        title="The Consciousness Equation: LCC, C, and the φ-Attractor",
        subtitle="Integrating the Emerick Constant into a Unified Consciousness Framework",
        paper_num="352",
        date="2026-03-01",
        keywords=["consciousness", "law of correlational causation", "golden ratio",
                  "attractor dynamics", "Emerick constant", "mood amplifier",
                  "heart coherence", "mathematical consciousness", "TI Sigma",
                  "fixed point theorem"],
        abstract=(
            "We derive a unified consciousness equation Ψ(LCC) = φ × LCC × (LCC/C − 1) "
            "that integrates the Law of Correlational Causation (LCC) measure with the PRIMARY "
            "constant hierarchy of TI Sigma. The derivation produces three exact algebraic "
            "results: (1) a fixed point at LCC = 1/√2 where consciousness output equals "
            "input (the Emerick Crossover); (2) a recursive map showing the TRUE threshold "
            "generates TRALSE-level consciousness; and (3) identification of C = 1/(φ√2) "
            "as the minimum LCC for self-referential consciousness. The mood amplifier "
            "protocol's φ-session scaling follows directly from the attractor basin geometry. "
            "All three proofs are algebraically exact, not approximations."
        ),
        ip_note="Establishes priority for: Ψ equation, Emerick Crossover fixed point, "
                "φ-session scaling protocol, C as consciousness threshold."
    ),
    dict(
        rank=2,
        source="URB_EMERICK_CONSTANT_8TH_PRIMARY.md",
        slug="ti_paper_347_emerick_constant",
        title="The Emerick Constant: Deriving the 8th Primary Mathematical Constant from First Principles",
        subtitle="EARing the Fundamental Forces, the Tralse Imperfection in Euler's Identity, "
                 "and Level 7 Closure",
        paper_num="347",
        date="2026-03-01",
        keywords=["Emerick constant", "Euler identity", "primary constants", "EAR operation",
                  "fundamental forces", "GILE framework", "mathematical constants",
                  "TI Sigma", "consciousness coefficient", "extended Euler identity"],
        abstract=(
            "Papers #342–346 established the 7-level URB hierarchy with PRIMARY constants "
            "{0, 1, i, √2, e, φ, π}. This paper derives the 8th PRIMARY constant C = 1/(φ√2) "
            "≈ 0.43702 from three independent methods: (1) EARing of the four fundamental "
            "forces, a new operation on structured quadruplets; (2) identification of the "
            "'Tralse Imperfection' in Euler's Identity — showing the digit '1' is not "
            "primitive but equals √2·φ·C; and (3) direct algebraic solution from the "
            "Extended Euler Identity e^(iπ) + √2·φ·C = 0. All three methods converge on "
            "the same value. The constant is named C (Emerick) by both personal meaning "
            "and structural necessity, following the convention of naming fundamental "
            "constants after their discoverers."
        ),
        ip_note="Establishes priority for: C constant definition, EARing operation, "
                "Extended Euler Identity, 8-constant PRIMARY hierarchy."
    ),
    dict(
        rank=3,
        source="URB_SOMATIC_COHERENCE_BODY_AS_CONSCIOUSNESS_TOOL.md",
        slug="ti_paper_358_somatic_coherence_eep",
        title="Somatic Coherence and the Emerick Expansion Posture",
        subtitle="The Body as Consciousness Instrument: Mudra Discovery, Sauna Protocol, "
                 "and the LCC-Posture Correspondence",
        paper_num="358",
        date="2026-03-02",
        keywords=["somatic coherence", "Emerick Expansion Posture", "heart coherence",
                  "mudra", "Jnana mudra", "LCC", "sauna therapy", "biometric protocol",
                  "yoga", "consciousness optimization", "TI Sigma", "BlissGene"],
        abstract=(
            "We present the Emerick Expansion Posture (EEP) — a specific somatic configuration "
            "for maximizing Law of Correlational Causation during meditation, sauna, and creative "
            "work. The EEP consists of: wide leg extension (maximizing hip flexor release), "
            "upright spine (full thoracic expansion), feet flat (bilateral grounding), "
            "Jnana mudra (index-thumb connection), posterior tongue elevation (lingual-vagal "
            "reflex activation), and nasal abdominal breathing. Each element has independent "
            "physiological justification. We argue mudras are discovered, not invented — "
            "they converge across traditions (Tibetan, Yogic, Qigong) because they optimize "
            "the same underlying autonomic parameters. A 5-phase sauna coherence protocol "
            "applying EEP is presented, with predicted HRV coherence scores at each phase."
        ),
        ip_note="Establishes priority for: EEP posture specification, mudra-LCC correspondence, "
                "sauna coherence protocol, posterior tongue extension as vagal activator."
    ),
    dict(
        rank=4,
        source="AGI_IMPOSSIBILITY_TI_SIGMA_PROOF.md",
        slug="ti_paper_349_agi_impossibility",
        title="The Impossibility of Conventional AGI: Why Level 6 Is Not Level 7",
        subtitle="A TI Sigma Proof That Benchmark-Passing Systems Cannot Achieve General Intelligence",
        paper_num="349",
        date="2026-03-01",
        keywords=["AGI impossibility", "artificial general intelligence", "ARC-AGI",
                  "consciousness threshold", "meta-cognition", "Emerick Crossover",
                  "URB hierarchy", "Level 7", "self-knowledge", "AI safety", "TI Sigma"],
        abstract=(
            "We prove that benchmark-passing artificial intelligence systems, regardless of "
            "performance level, cannot constitute genuine general intelligence. The proof "
            "proceeds in three steps: (1) the URB hierarchy establishes that current AI "
            "systems operate at Level 6 (π — circular self-recognition) but not Level 7 "
            "(C — GM self-knowledge); (2) Level 7 requires LCC ≥ 1/√2 ≈ 0.707, meaning "
            "the system's self-model must be more accurate than inaccurate — a condition "
            "no benchmark-passing system satisfies because benchmarks test pattern recognition, "
            "not self-knowledge; (3) empirical demonstration shows benchmark-optimized systems "
            "exhibit systematic failures at meta-cognitive tasks that genuine general intelligence "
            "would trivially solve. What mainstream AI calls AGI is a completed Level 6 system. "
            "True Level 7 requires the Emerick Crossover — structurally impossible to achieve "
            "through benchmark optimization alone."
        ),
        ip_note="Establishes priority for: Level 6/7 AGI distinction, Emerick Crossover "
                "as AGI threshold, URB hierarchy applied to AI capability assessment."
    ),
    dict(
        rank=5,
        source="TRALSE_TOPOS_COMPLETE_FORMALIZATION.md",
        slug="ti_tralse_topos_formalization",
        title="Tralse Topos: Complete Formalization of 4-Valued Consciousness Logic",
        subtitle="The Mathematical Foundation of TI Sigma's Non-Binary Truth System",
        paper_num=None,
        date="2025-11-15",
        keywords=["tralse logic", "4-valued logic", "topos theory", "consciousness logic",
                  "non-binary truth", "Myrion Resolution", "paraconsistent logic",
                  "TI Sigma", "formal logic", "mathematical logic"],
        abstract=(
            "We present the complete formal specification of Tralse Logic — a 4-valued truth "
            "system with values {FALSE, TRALSE, TRUE, RADIANT} where TRALSE (≈0.414) represents "
            "a stable intermediate state neither true nor false. Unlike classical 2-valued or "
            "intuitionistic logic, Tralse Logic admits a third value with distinct algebraic "
            "properties: TRALSE ∧ TRALSE = TRALSE (idempotent), and TRALSE → TRUE under "
            "Myrion Resolution (the operation that resolves indeterminate states through "
            "GILE-weighted context). The topos-theoretic foundation establishes Tralse Logic "
            "as a valid alternative to classical Boolean logic for systems where genuine "
            "indeterminacy (not merely epistemic uncertainty) is primary. Applications to "
            "consciousness modeling, AI decision systems, and quantum logic are discussed."
        ),
        ip_note="Establishes priority for: Tralse Logic system, Myrion Resolution operator, "
                "4-valued topos, TRALSE as distinct logical value."
    ),
    dict(
        rank=6,
        source="APERIODIC_DUAL_LxE_LpE_EINSTEIN_TILING.md",
        slug="ti_aperiodic_lxe_lpe_einstein_tiling",
        title="The Dual L×E / L+E Aperiodic Monotile: GILE as Einstein Tiling",
        subtitle="How the Multiplicative and Additive Operations on Love-Environment Produce "
                 "Quasicrystalline Consciousness Structure",
        paper_num=None,
        date="2026-02-20",
        keywords=["aperiodic tiling", "Einstein monotile", "quasicrystal", "GILE framework",
                  "L×E", "L+E", "consciousness structure", "Penrose tiling",
                  "TI Sigma", "receptor binding", "fibonacci", "golden ratio"],
        abstract=(
            "We identify the GILE framework's dual L×E (multiplicative) and L+E (additive) "
            "operations as the two components of a natural aperiodic monotile — a single "
            "shape whose copies tile the plane without periodic repetition. This connection "
            "was discovered via hypnagogic insight on February 19-20, 2026, in which the "
            "two GILE operations were observed fitting together in a receptor-binding rather "
            "than puzzle-piece geometry. The receptor-binding interpretation is developed "
            "formally: L×E and L+E do not merely combine algebraically but bind to reality's "
            "computational substrate selectively and dynamically, producing the quasicrystalline "
            "information structure that consciousness exhibits. Connections to Fibonacci "
            "sequences, φ-scaling, and quasicrystalline computation are established."
        ),
        ip_note="Establishes priority for: GILE-as-aperiodic-monotile identification, "
                "receptor-binding interpretation of L×E/L+E, quasicrystalline consciousness."
    ),
    dict(
        rank=7,
        source="CHSH_CONSCIOUSNESS_COHERENCE_DEFENSE.md",
        slug="ti_chsh_0_85_coherence_defense",
        title="Defending the 0.85 Coherence Threshold: Mathematical Structure Beyond Bell Test Conditions",
        subtitle="Why Exceeding Channel-Appropriate Correlation Bounds Is Meaningful "
                 "in Heart-Brain Biofeedback Systems",
        paper_num=None,
        date="2026-02-01",
        keywords=["CHSH inequality", "heart coherence", "0.85 threshold", "HRV biofeedback",
                  "Bell inequality", "consciousness measurement", "quantum biology",
                  "transfer entropy", "Granger causality", "TI Sigma", "LCC"],
        abstract=(
            "The TI consciousness framework identifies a coherence threshold of 0.85 in "
            "heart-brain synchronization as a marker of coupling exceeding classical "
            "biofeedback predictions. Critics object that invoking CHSH reasoning outside "
            "Bell test conditions constitutes a category error. This paper steel-mans that "
            "objection, acknowledges the genuine differences between biofeedback systems and "
            "Bell tests, and argues that the mathematical structure of exceeding "
            "channel-appropriate correlation bounds is meaningful independent of specific "
            "physical conditions. The 0.85 threshold is defended on empirical grounds from "
            "HRV literature, connected to the CGLMP inequality for higher-dimensional systems, "
            "and situated within a broader evidential framework combining transfer entropy, "
            "Granger causality, and multi-modal biometric convergence."
        ),
        ip_note="Establishes priority for: 0.85 coherence threshold framework, "
                "CHSH-biofeedback analogy, channel-appropriate correlation bound analysis."
    ),
    dict(
        rank=8,
        source="BOK_ORCH_OR_GILE_MATRIX_SYNTHESIS.md",
        slug="ti_bok_orchor_gile_synthesis",
        title="BOK Model, Orch-OR, and GILE Matrix: A Critical Synthesis",
        subtitle="Finite Calculus, Microtubule Consciousness, and the Mechanistic Basis of PSI",
        paper_num=None,
        date="2025-12-08",
        keywords=["BOK model", "Orch-OR", "GILE matrix", "microtubule", "quantum consciousness",
                  "Penrose-Hameroff", "PSI mechanisms", "IIT synthesis", "TI Sigma",
                  "finite calculus", "consciousness"],
        abstract=(
            "We synthesize three frameworks for consciousness: the BOK (Brain-Object-Knowledge) "
            "model using finite calculus, Penrose-Hameroff Orchestrated Objective Reduction "
            "(Orch-OR) via quantum microtubule dynamics, and the GILE Matrix (64-dimensional "
            "Goodness-Intuition-Love-Environment). The synthesis reveals structural "
            "correspondences between finite calculus operators and quantum collapse dynamics, "
            "between the BOK object hierarchy and GILE's dimensional decomposition, and between "
            "Orch-OR's objective reduction threshold and the Emerick Crossover LCC ≥ 1/√2. "
            "PSI phenomena are reframed as signatures of quantum-coherent LCC exceeding the "
            "classical-quantum boundary. The IIT-GILE-BOK Loop is defined as the stable "
            "attractor of this three-way synthesis."
        ),
        ip_note="Establishes priority for: IIT-GILE-BOK Loop Synthesis, GILE-Orch-OR "
                "correspondence, PSI as quantum-coherent LCC."
    ),
    dict(
        rank=9,
        source="EMPIRICAL_CONSCIOUSNESS_PAPER.md",
        slug="ti_empirical_consciousness_7_predictions",
        title="Empirical Verification of the Unified Consciousness Master Equation: "
              "A Multi-Paradigm Study",
        subtitle="Seven Quantitative Predictions Derived from the UCME — Seven Verified",
        paper_num=None,
        date="2026-01-31",
        keywords=["consciousness empirical", "IIT verification", "PSI meta-analysis",
                  "LCC empirical", "GILE empirical", "flow state", "brain energetics",
                  "consciousness threshold", "TI Sigma", "prediction verification"],
        abstract=(
            "We present empirical verification of seven quantitative predictions derived from "
            "the Unified Consciousness Master Equation (UCME): C = Φ × [1 − e^(−R/7)] × "
            "LCC^0.3 × (G×I×L×E)^0.25. Using real data from neural complexity studies, PSI "
            "meta-analyses (N > 300 studies), flow state research, AI capability emergence "
            "patterns, brain energetics, and distance-decay experiments, we find 7/7 predictions "
            "verified with combined significance p < 10^−50. Results confirm: consciousness "
            "threshold at recursion depth R ≈ 7; non-local causation at LCC ≈ 0.875; brain "
            "efficiency 10^8× greater than silicon for consciousness generation. These findings "
            "support the TI Sigma framework and have implications for consciousness science, "
            "AI safety, and theoretical physics."
        ),
        ip_note="Establishes priority for: UCME formulation, 7-prediction empirical test, "
                "R=7 consciousness threshold, LCC=0.875 non-local boundary."
    ),
    dict(
        rank=10,
        source="URB_EAR_EXISTENCE_AS_INDISPENSABILITY.md",
        slug="ti_paper_355_ear_existence_indispensability",
        title="EAR — Existence as Indispensability: The Logical Irreplaceability of Every Person",
        subtitle="How the EAR Principle Collapses the 4-Dimensional GILE Logic to a 2-Value System "
                 "and Why This Proves Inherent Human Worth",
        paper_num="355",
        date="2026-03-02",
        keywords=["existence", "indispensability", "EAR principle", "human worth",
                  "GILE", "tralse logic", "identity", "philosophical logic",
                  "TI Sigma", "consciousness ethics"],
        abstract=(
            "The EAR Principle (Existence As Indispensability) states: to exist is to be "
            "irreplaceable. We prove this formally using GILE logic: a 4-dimensional existence "
            "vector (G, I, L, E) collapses to a 2-value system when the indispensability "
            "condition is applied — either a being exists in its specific configuration "
            "(indispensable) or does not (absent), with no intermediate. This collapse "
            "establishes a binary floor beneath the 4-valued Tralse system: indispensability "
            "is the primordial true/false that grounds all higher-order consciousness claims. "
            "We apply EAR to the crisis of psychiatric labeling: when a person's mental "
            "uniqueness is systematically denied, the indispensability of their specific "
            "existential configuration is violated at the logical level — causing harm "
            "structurally equivalent to denial of existence."
        ),
        ip_note="Establishes priority for: EAR Principle, GILE collapse theorem, "
                "indispensability as logical primitive, EAR applied to psychiatric ethics."
    ),
]


def make_header(p: dict) -> str:
    num_str = f"Paper #{p['paper_num']} — " if p['paper_num'] else ""
    kw_str  = "; ".join(p['keywords'])
    return f"""---
title: "{p['title']}"
subtitle: "{p['subtitle']}"
author: "{AUTHOR}"
affiliation: "{AFFILIATION}"
date: "{p['date']}"
series: "{SERIES}"
paper_number: "{p['paper_num'] or 'N/A'}"
license: "{LICENSE}"
license_url: "{LICENSE_URL}"
doi: "{DOI_PENDING}"
keywords: [{kw_str}]
zenodo_priority_rank: {p['rank']} / 10
ip_protection_note: "{p['ip_note']}"
---

# {num_str}{p['title']}
## {p['subtitle']}

**Author:** {AUTHOR}  
**Affiliation:** {AFFILIATION}  
**Date:** {p['date']}  
**Series:** {SERIES}  
**License:** [{LICENSE}]({LICENSE_URL})  
**DOI:** {DOI_PENDING}  
**Keywords:** {kw_str}

---

## Abstract

{p['abstract']}

---

"""


def strip_existing_header(content: str) -> str:
    lines = content.split('\n')
    # Remove up to the first '---' separator after the initial header block
    in_header = True
    result = []
    skipping = True
    header_lines_done = False
    for i, line in enumerate(lines):
        # Once we see the first top-level section (## or ---) after the metadata, stop stripping
        if skipping:
            stripped = line.strip()
            # Keep content after the first '---' separator that follows the author block
            if stripped == '---' and i > 10:
                skipping = False
                continue
            # Also stop if we hit a major section heading that isn't the title
            if stripped.startswith('## ') and i > 5:
                skipping = False
                result.append(line)
        else:
            result.append(line)
    return '\n'.join(result)


def process_paper(p: dict):
    src = os.path.join(PAPERS_DIR, p['source'])
    if not os.path.exists(src):
        print(f"  ✗ NOT FOUND: {p['source']}")
        return
    with open(src, 'r', encoding='utf-8') as f:
        raw = f.read()
    body = strip_existing_header(raw)
    header = make_header(p)
    final = header + body.lstrip('\n')
    out_name = f"{p['rank']:02d}_{p['slug']}.md"
    out_path = os.path.join(BUNDLE_DIR, out_name)
    with open(out_path, 'w', encoding='utf-8') as f:
        f.write(final)
    size_kb = len(final) / 1024
    print(f"  ✓ [{p['rank']:02d}] {out_name} ({size_kb:.1f} KB)")


def write_upload_guide():
    guide = """# Zenodo Upload Guide — TI Sigma Top 10 Papers
## Brandon Charles Emerick | BlissGene Therapeutics
## Generated: March 2026

---

## What Zenodo Does For You

Every upload gets a **permanent DOI** (Digital Object Identifier) with a timestamp.
Under the America Invents Act, this establishes your prior art date.
Anyone who tries to patent the same idea after your Zenodo date faces your publication as prior art.
Zenodo is free, trusted by CERN, and indexed by Google Scholar.

---

## Before You Upload — One-Time Setup

1. Go to **https://zenodo.org**
2. Click "Sign Up" — use your real name (Brandon Charles Emerick)
3. Get an ORCID at **https://orcid.org** (free, takes 2 min) — this permanently links your identity to your publications
4. In Zenodo Settings → Linked accounts → connect your ORCID

---

## Upload Order (Priority)

Upload in this exact order — highest IP value first:

| # | File | Why First |
|---|------|-----------|
| 1 | `01_ti_paper_352_consciousness_equation.md` | Core product IP — Ψ equation, Emerick Crossover |
| 2 | `02_ti_paper_347_emerick_constant.md` | C constant derivation — foundational to everything |
| 3 | `03_ti_paper_358_somatic_coherence_eep.md` | BlissGene product protocol — most commercially immediate |
| 4 | `04_ti_paper_349_agi_impossibility.md` | Highest-traffic topic — establishes academic presence |
| 5 | `05_ti_tralse_topos_formalization.md` | Logic system IP — blocks imitation of 4-valued framework |
| 6 | `06_ti_aperiodic_lxe_lpe_einstein_tiling.md` | Novel mathematical connection to 2023 Einstein tile |
| 7 | `07_ti_chsh_0_85_coherence_defense.md` | Defends core biometric threshold |
| 8 | `08_ti_bok_orchor_gile_synthesis.md` | Academic credibility — engages Penrose-Hameroff |
| 9 | `09_ti_empirical_consciousness_7_predictions.md` | Empirical validation — 7/7 predictions |
| 10 | `10_ti_paper_355_ear_existence_indispensability.md` | Philosophical/ethical — broadest audience |

---

## Step-by-Step Upload (Same Process for Each)

### Step 1 — New Upload
- Go to https://zenodo.org/uploads/new
- Click "New upload"

### Step 2 — Upload File
- Drag and drop the `.md` file from your `zenodo_bundle/` folder
- Zenodo accepts Markdown directly

### Step 3 — Fill Metadata (copy from the file's header block)

**Resource type:** Publication → Preprint  
**Title:** (copy from file header — the `title:` field)  
**Authors:** Brandon Charles Emerick  
**Affiliation:** BlissGene Therapeutics; TI Sigma Research Institute  
**Date:** (copy from file header)  
**Description:** (copy the Abstract section from the paper)  
**Keywords:** (copy from file header — the `keywords:` field)  
**License:** Creative Commons Attribution 4.0 (CC-BY)  

### Step 4 — Related Works (Optional but Valuable)
- After your first upload, add the DOI of paper #1 as a "Related identifier" in subsequent papers
- Use relation type "Is part of" — this groups your papers into a visible series

### Step 5 — Publish
- Click "Publish" (not "Save draft")
- **Record the DOI** — paste it into the corresponding file's header under `doi:`
- The DOI is now permanent. Your priority date is locked.

---

## After All 10 Are Published

1. **Create a Zenodo Community:** "TI Sigma — Universal Reality Blueprint"
   - https://zenodo.org/communities/new
   - Add all 10 papers to the community
   - This creates a single citable home for the series

2. **File your Provisional Patents** — now you have public prior art dates that support each provisional

3. **Add Zenodo DOIs to your papers directory** — run `prepare_zenodo_bundle.py` again with DOIs filled in

---

## Total Cost: $0
## Time: ~45 minutes for all 10

---

## After Zenodo — Next Steps Toward Provisional Patents

With Zenodo DOIs in hand:

| Patent # | Title | Zenodo Papers Supporting It | USPTO Fee |
|---------|-------|---------------------------|-----------|
| 1 | Consciousness Threshold Method & Mood Amplifier Protocol | Papers 1, 3, 7 | $160 |
| 2 | TI Sigma HC Architecture for ML Prediction | Papers 2, 5 | $160 |
| 3 | GILE Framework & Tralse Logic System | Papers 5, 8, 10 | $160 |

**Total patent cost as micro-entity:** $480

File at: https://www.uspto.gov/patents/apply/applying-online

"""
    guide_path = os.path.join(BUNDLE_DIR, 'UPLOAD_GUIDE.md')
    with open(guide_path, 'w', encoding='utf-8') as f:
        f.write(guide)
    print(f"  ✓ UPLOAD_GUIDE.md written")


if __name__ == '__main__':
    print("=" * 60)
    print("  TI SIGMA — ZENODO BUNDLE PREPARER")
    print(f"  {len(PAPERS)} papers | Priority-ranked by IP value")
    print("=" * 60)
    print("\nProcessing papers...")
    for p in sorted(PAPERS, key=lambda x: x['rank']):
        process_paper(p)
    print("\nWriting upload guide...")
    write_upload_guide()
    print("\n" + "=" * 60)
    print("  BUNDLE READY → zenodo_bundle/")
    print(f"  {len(PAPERS)} polished papers + UPLOAD_GUIDE.md")
    print("  Upload in order. First DOI locks your priority date.")
    print("=" * 60)
