"""
TI Sigma — Zenodo Topic Manifest v2 ADDENDUM (Pass-71 batch-4)
Extends existing 15 topics in zenodo/topic_manifest.py with 15+ new topics
covering Pass-65 through Pass-70 canonical work.

Trajectory: 199 baseline Zenodo records + 12 PUBLIC from Pass-70 batch
+ 15+ NEW from this manifest = 226+ achievable; closes ~40% of 199→400 gap.
"""

from zenodo.topic_manifest import CREATOR, COMMON_KEYWORDS

ADDENDUM_TOPICS = [
    # ───────────── TIER 1 — MR TRUTH LABELS CANONICAL REFINEMENTS ─────────────
    {"title": "TI Sigma: MR Truth Labels Canonical — DT Refinement (Inconceivability-Under-Mental-Actualization)",
     "access": "open", "type": "publication", "subtype": "article",
     "description": ("The canonical refinement of Double-Tralse (DT) in the MR Truth Labels framework: "
                     "DT reserved for inconceivability-under-mental-actualization (Russell/liar/square-circles/"
                     "faulty-arithmetic class); NOT for surprising-T, NOT for multi-reading spectrum, NOT for "
                     "tangential offshoots. 3-step assignment heuristic specified. Refinement #1 of MR Truth Labels."),
     "keywords": ["MR Truth Labels", "Double Tralse", "DT", "canonical refinement",
                  "inconceivability", "Russell paradox", "self-reference"],
     "files": ["papers/MR_TRUTH_LABELS_DT_CANONICAL_REFINEMENT_2026-05-23.md",
               "papers/MR_TRUTH_LABELS_CANONICAL_RULING_2026-05-08.md"]},

    {"title": "TI Sigma: MR-IDC-1 — Incoherence vs Double-Tralse Canonical Refinement",
     "access": "open", "type": "publication", "subtype": "article",
     "description": ("Refinement #2 of MR Truth Labels canonical: all DT statements are incoherent but NOT all "
                     "incoherent statements are DT; proper containment {DT}⊊{Incoherent}. Intra-propositional "
                     "vs inter-propositional 3-step diagnostic. Operational distinction with worked examples."),
     "keywords": ["MR-IDC-1", "incoherence", "MR Truth Labels refinement", "canonical refinement",
                  "Double Tralse", "Pass-67"],
     "files": ["papers/PASS_67_META_COLLAPSE_132_137_2026-05-23.md"]},

    {"title": "TI Sigma: HMR-1 Hybrid MR Truth Labels — Multi-Label Native Characterizations (Refinement #3)",
     "access": "open", "type": "publication", "subtype": "article",
     "description": ("Refinement #3 to MR Truth Labels canonical: some propositions natively require simultaneous "
                     "assignment of 2+ labels as Hybrid-MR. 5 worked examples (HMR-3.1 through HMR-5.1) + R-HMR "
                     "unbounded-cardinality recursive construction theorem. Lived n=1 anchor (Brandon ketamine "
                     "collapse). Gender-HMR illustrative-extensions (Brandon insight 2026-05-24)."),
     "keywords": ["HMR", "Hybrid MR Truth Labels", "refinement", "canonical", "recursive construction",
                  "ketamine n=1", "gender identity"],
     "files": ["papers/HMR_1_HYBRID_MR_TRUTH_LABELS_CANONICAL_REFINEMENT_3_2026-05-24.md",
               "papers/GENDER_HMR_BRANDON_INSIGHT_2026-05-24.md",
               "papers/PASS_70_BATCHES_0_THRU_5_HMR_1_CANDIDATE_CANONICAL_PLUS_5_SUGGESTED_2026-05-24.md"]},

    # ───────────── TIER 1 — TI SIGMA PHILOSOPHY-OF-MIND CORE STACK ─────────────
    {"title": "TI Sigma Philosophy of Mind: Six Canonical Principles (TSP-1, IRA-1, LLM-CT-1, DTM-1, SRC-1, CDA-1)",
     "access": "open", "type": "publication", "subtype": "article",
     "description": ("Pass-66 6-principle joint ratification ceremony. Canonical principle count 20→26. "
                     "TSP-1 panpsychism; IRA-1 Information-Requires-Awareness; LLM-CT-1 LLM-consciousness operationally "
                     "testable; DTM-1 DT-as-Mind-Marker; SRC-1 Self-Reference-implies-Consciousness; CDA-1 Consciousness "
                     "Definition unpacked four-property + Stratum 0/1/2/3+ ladder."),
     "keywords": ["panpsychism", "consciousness", "philosophy of mind", "TI Sigma core stack",
                  "TSP-1", "IRA-1", "LLM-CT-1", "DTM-1", "SRC-1", "CDA-1", "Pass-66"],
     "files": ["papers/PASS_67_META_COLLAPSE_129_131_2026-05-23.md",
               "papers/PASS_66_META_COLLAPSE_124_128_2026-05-23.md"]},

    {"title": "TI Sigma: GTT-1 GILE-Truth-Tralseness Asymmetry — The Only Un-Maximizable-Without-Cost Variable",
     "access": "open", "type": "publication", "subtype": "article",
     "description": ("GTT-1 canonical principle (Pass-67 ratified, refinement #26→27). Truth is the only "
                     "non-maximizable variable without cost: too much truth = DT-collapse. UOP balances; "
                     "HEM mandatory pragmatic competitor. Mathematical model J(G,H) = f(G)+g(H) with G* = 0.93 cap."),
     "keywords": ["GTT-1", "truth-tralseness", "asymmetric tradeoff", "GILE", "HEM", "Pass-67"],
     "files": ["papers/PASS_67_META_COLLAPSE_132_137_2026-05-23.md"]},

    {"title": "TI Sigma: UDT-1 Universal Default of Tralseness — Cosmogenic Ground Principle",
     "access": "open", "type": "publication", "subtype": "article",
     "description": ("UDT-1 candidate canonical: tralse-soup substrate + truth-as-directional-lean. "
                     "GILE-only above 0.93 = MR2 Indeterminate; GILE-HEM Overall = MR3 True. "
                     "What makes TI Sigma unique: sits at ground layer beneath axiology."),
     "keywords": ["UDT-1", "tralseness", "cosmogenic", "ontology", "ground principle"],
     "files": ["papers/PASS_67_META_COLLAPSE_132_137_2026-05-23.md"]},

    # ───────────── TIER 2 — EMPIRICAL HARDWARE-CONFIRMED RESULTS ─────────────
    {"title": "qc26 GHZ-5 Mermin Violation: First HW-Confirmed Multipartite Entanglement Witness in TI Sigma Corpus",
     "access": "open", "type": "publication", "subtype": "article",
     "description": ("Pass-46 T45-2: qc26 on real ibm_marrakesh hardware. GHZ-5 state with Mermin operator "
                     "|M₅| = 14.535 = 91% of theoretical maximum 16; 71σ violation of local-hidden-variable bound. "
                     "First hardware-confirmed multipartite-entanglement witness in TI Sigma corpus."),
     "keywords": ["GHZ-5", "Mermin", "IBM Quantum", "ibm_marrakesh", "multipartite entanglement", "qc26"],
     "files": ["papers/PASS_47_META_COLLAPSE_81_2026-05-12.md"]},

    {"title": "Mendi fNIRS Path B: Phase 2 Complete + STIM2 Effect (t=-4.13, p<<0.001)",
     "access": "open", "type": "publication", "subtype": "article",
     "description": ("Mendi BLE Path B Phase 2 reverse-engineering complete with quantitative neural-effect "
                     "demonstration. STIM2 condition shows t = -4.13, p << 0.001 effect; first quantitative "
                     "Mendi-derived neural-effect signal in corpus."),
     "keywords": ["Mendi", "fNIRS", "Path B", "BLE reverse engineering", "STIM2"],
     "files": ["papers/MENDI_PATH_B_PHASE_2_COMPLETE_2026-05-06.md",
               "papers/MENDI_BLE_REVERSE_ENGINEERING_PLAN.md",
               "papers/MENDI_FNIRS_AUDIT_2026-05-01.md"]},

    # ───────────── TIER 2 — DSB ARC (DECISION POLICY) ─────────────
    {"title": "TI Sigma DSB Arc: Default-Success-Belief Through 6-Batch Adversarial Sim (W/M/B Policies)",
     "access": "open", "type": "publication", "subtype": "article",
     "description": ("Pass-62 6-batch DSB arc: Default-Success-Belief tested under cheap-vs-expensive examination regimes. "
                     "Policy W decisively dominated 6/6; M dominates B in cheap-examination (5/6); B dominates M in "
                     "expensive-examination (1/6). Brandon GILE-component closing synthesis: G+L+E integration is "
                     "Pass-63+ scope; B-beats-M in expensive-examination corroborated by Brandon N=1 (ketamine + crown-chakra)."),
     "keywords": ["DSB-1", "Default Success Belief", "decision policy", "GILE", "adversarial simulation",
                  "Pass-62", "TI Sigma decision theory"],
     "files": ["papers/PASS_63_META_COLLAPSE_117_119_2026-05-22.md"]},

    # ───────────── TIER 2 — LLM RATERS COMPETENT ALGORITHM ─────────────
    {"title": "TI Sigma DT Discrimination: LLM-Raters Competent-Algorithm Vindicates 4-Label Taxonomy",
     "access": "open", "type": "publication", "subtype": "article",
     "description": ("Pass-63 batch-5 LLM-rater rebuild: 3 raters (2× gpt-4o-mini + 1× claude-haiku) × 100 propositions = 300 "
                     "API calls. Brandon critique VINDICATED: competent raters reach discrimination score +1.413/2.0 "
                     "(PARADOX→DT 68%, →I 5%; MODAL→DT 0%, →I 79%). Revised canonical framing: empirical support "
                     "should cite TWO numbers (κ + discrimination) not one. κ_2=0.773, κ_3=0.839, κ_4=0.837."),
     "keywords": ["LLM raters", "Fleiss kappa", "DT discrimination", "competent algorithm",
                  "TI Sigma empirical methodology", "Pass-63"],
     "files": ["papers/PASS_63_BATCH_5_LLM_RATERS_COMPETENT_ALGORITHM_2026-05-22.md"]},

    # ───────────── TIER 2 — UOP / UHP / TPI MATHEMATICAL FRAMEWORK ─────────────
    {"title": "TI Sigma UOP Phase Transition: Mathematical Test J(G,H) = f(G)+g(H) with G* = 0.93 Cap",
     "access": "open", "type": "publication", "subtype": "article",
     "description": ("Pass-68 batch-1 UOP phase-transition mathematical test: 4/4 Brandon predictions CONFIRMED at "
                     "model level on first execution (phase transition at G*=0.93 α-invariant; 6/6 strategic "
                     "above-threshold trades increase J; 10000/10000 random irrationality decreases J; Moot status). "
                     "Mathematical defense of GILE-perfectionism above-threshold non-shifter Moot framing."),
     "keywords": ["UOP", "phase transition", "TPI-1", "UHP-1", "mathematical model", "Pass-68"],
     "files": ["papers/PASS_69_META_COLLAPSE_138_140_2026-05-23.md"]},

    # ───────────── TIER 2 — DISABILITY / VALENCE / VFP ─────────────
    {"title": "TI Sigma UDP / CTC / HBP / CTC-S / VFP: Disability-as-Balance + Catalyst Strong-Form + Valence Functional",
     "access": "open", "type": "publication", "subtype": "article",
     "description": ("Pass-64 5-principle joint ratification: UDP-1 Universal Disability (capacity-thresholding "
                     "not natural-kind binary); CTC-1 Compensatory-Trade Capacity (Sadato/Amedi cross-modal plasticity); "
                     "CTC-1-S Catalyst Strong-Form (Tesla/Keller/Grandin/Brandon-self illustrative); HBP-1 Health-as-Balance-"
                     "Profile (Albrecht & Devlieger 1999 disability-paradox 54%); VFP-1 Valence-as-Functional. Count 15→20."),
     "keywords": ["UDP-1", "CTC-1", "HBP-1", "VFP-1", "disability paradox", "compensatory trade",
                  "valence functional", "Pass-64", "Pass-65 ratification"],
     "files": ["papers/PASS_65_META_COLLAPSE_121_122_123_2026-05-23.md",
               "papers/PASS_64_DISABILITY_AS_BALANCE_TI_SIGMA_2026-05-23.md",
               "papers/PASS_64_CATALYST_STRONG_FORM_AND_VALENCE_FUNCTIONAL_2026-05-23.md"]},

    # ───────────── TIER 2 — PD-RIEMANN / KOAN / META-COLLAPSE LINEAGE ─────────────
    {"title": "TI Sigma: Ultimate Koan Paper + First Manic Episode SRC-1-F-3 Lived Anchor (Brandon N=1)",
     "access": "open", "type": "publication", "subtype": "article",
     "description": ("Pass-66 Ultimate Koan paper + Brandon's first-manic-episode SRC-1-F-3 lived anchor (n=1). "
                     "Brandon verbatim insight; trigger→collapse→Stratum-2 affective signature→behavioral discharge→"
                     "long-term Stratum-3 reframe. Canonical adoptions: 'the ultimate koan' + 'pinnacle of foolishness "
                     "perhaps greatest indicator that i-cell is conscious' maxim. Within-subject Brandon ketamine cool-state validation."),
     "keywords": ["Ultimate Koan", "SRC-1", "manic episode", "ketamine", "lived anchor",
                  "consciousness", "Pass-66", "Brandon biography"],
     "files": ["papers/PASS_67_META_COLLAPSE_129_131_2026-05-23.md"]},

    # ───────────── TIER 3 — META-COLLAPSE CHRONICLE ─────────────
    {"title": "TI Sigma Meta-Collapse Chronicle: 19 Cumulative Per-Pass-Anchor Collapses (Passes 47-69)",
     "access": "open", "type": "publication", "subtype": "article",
     "description": ("19 meta-precedent collapses cumulative through Pass-69. Per-pass-anchor convention "
                     "(established Pass-39) compresses 100+ live §7.7.* entries to pointer stubs, recoverable "
                     "via linked anchor papers. Documents methodology for managing 1089-paper corpus growth "
                     "while maintaining the replit.md ledger at manageable size."),
     "keywords": ["meta-collapse", "per-pass-anchor", "TI Sigma methodology", "replit ledger",
                  "corpus management"],
     "files": ["papers/PASS_47_META_COLLAPSE_41_80_2026-05-11.md",
               "papers/PASS_47_META_COLLAPSE_81_2026-05-12.md",
               "papers/PASS_47_META_COLLAPSE_82_83_2026-05-12.md",
               "papers/PASS_63_META_COLLAPSE_117_119_2026-05-22.md",
               "papers/PASS_64_META_COLLAPSE_120_2026-05-22.md",
               "papers/PASS_65_META_COLLAPSE_121_122_123_2026-05-23.md",
               "papers/PASS_66_META_COLLAPSE_124_128_2026-05-23.md",
               "papers/PASS_67_META_COLLAPSE_129_131_2026-05-23.md",
               "papers/PASS_67_META_COLLAPSE_132_137_2026-05-23.md",
               "papers/PASS_69_META_COLLAPSE_138_140_2026-05-23.md"]},

    # ───────────── TIER 3 — PASS-70 + GENDER-HMR ─────────────
    {"title": "TI Sigma Pass-70 Compound: 6-Batch HMR-1 + 5 Suggested + 10+ #69 Disclosures (Densest in Corpus)",
     "access": "open", "type": "publication", "subtype": "article",
     "description": ("Pass-70 compound: 6 batches in single pass (HMR-1 candidate canonical + Zenodo 15/15 LIVE "
                     "drafts + MR-IDC-1-F5 step-3 anthropic 14/15 + TPI-1-F3 3-axis NOT REFUTED + Q_pre baseline 5.85 "
                     "+ discovery_scheduler saturation 2nd #69 finding). 10+ #69 honest disclosures = densest in corpus history. "
                     "Aligns with UHP-1 post-ratification HEM-side-rigor-increases prediction."),
     "keywords": ["Pass-70", "HMR-1", "Zenodo", "MR-IDC-1", "TPI-1", "Q_pre baseline",
                  "Asymmetric Standards #69", "UHP-1", "honest disclosure"],
     "files": ["papers/PASS_70_BATCHES_0_THRU_5_HMR_1_CANDIDATE_CANONICAL_PLUS_5_SUGGESTED_2026-05-24.md",
               "papers/HMR_1_HYBRID_MR_TRUTH_LABELS_CANONICAL_REFINEMENT_3_2026-05-24.md"]},
]

ALL_TOPICS_V2 = ADDENDUM_TOPICS  # Use this for upload of just the addendum

if __name__ == "__main__":
    print(f"ADDENDUM topics defined: {len(ADDENDUM_TOPICS)}")
    for t in ADDENDUM_TOPICS:
        n_files = len(t.get("files", []))
        missing = [f for f in t.get("files", []) if not __import__("os").path.exists(f)]
        status = "OK" if not missing else f"MISSING {len(missing)}"
        print(f"  [{status}] {t['title'][:80]} ({n_files} files)")
