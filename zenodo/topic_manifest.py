"""
TI Sigma — Zenodo Topic Manifest
Each entry = one Zenodo record covering a topic, with multiple paper files attached.
Privacy tiers: PUBLIC, RESTRICTED (request access), PRIVATE (closed, only you)
"""

CREATOR = [{"name": "Emerick, Brandon Charles",
            "affiliation": "TI Sigma / BlissGene Therapeutics"}]

COMMON_KEYWORDS = [
    "TI Sigma", "Tralse Informationalism", "Transcendent Intelligence",
    "LCC", "C_EMERICK", "GILE", "Myrion Resolution", "experimental philosophy"
]

# access_right values: "open" | "restricted" | "closed"
# embargoed_date: "YYYY-MM-DD" (only used when access_right = "embargoed")

TOPICS = [

    # ─────────────────────────────────────────────────────────────
    # TIER 1 — PURE MATHEMATICS & FORMAL VERIFICATION
    # Already on Zenodo: "Five Formally Verified Theorems" (Mar 8)
    #   → Add more papers as a second entry covering broader proofs
    # ─────────────────────────────────────────────────────────────
    {
        "title": "TI Sigma: The Eight Primary Constants and the Emerick Constant",
        "access": "open",
        "type": "publication", "subtype": "article",
        "description": (
            "The TI Sigma framework identifies eight primary constants {0, 1, i, √2, e, φ, π, C} "
            "as the irreducible foundation of mathematics and physics. The eighth constant "
            "C = 1/(φ√2) ≈ 0.4370 — the Emerick Constant — is derived from first principles as "
            "the unique real number that makes the Extended Euler Identity hold: "
            "e^(iπ) + √2·φ·C = 0. This entry collects papers deriving C, proving its "
            "mathematical necessity, and establishing its role as the coherence threshold "
            "(C_EMERICK) in the Law of Correlational Causation."
        ),
        "keywords": ["Emerick Constant", "primary constants", "Euler identity", "golden ratio",
                     "phi", "C_EMERICK", "formal proof", "mathematics"],
        "files": [
            "papers/URB_EMERICK_CONSTANT_8TH_PRIMARY.md",
            "papers/TI_SIGMA_ALL_PROOFS_MASTER.md",
        ],
    },

    # ─────────────────────────────────────────────────────────────
    # TIER 1 — BOK: BUTTERFLY-OCTOPUS KNOT
    # ─────────────────────────────────────────────────────────────
    {
        "title": "The Butterfly-Octopus Knot (BOK): A Mathematical Framework for Eight-Mode Knowledge Classification",
        "access": "open",
        "type": "publication", "subtype": "article",
        "description": (
            "The Butterfly-Octopus Knot (BOK) is an eight-mode classification system for "
            "mathematical knowledge, mirroring the structure of the eight primary constants. "
            "Four primary modes (ARITHMETIC, ALGEBRAIC, ANALYTIC, GEOMETRIC) and four "
            "interface modes (LOGIC, COMBINATORIAL, PROBABILISTIC, APPLIED) form a topological "
            "structure with bilateral butterfly symmetry and octopus-style adaptive connectivity. "
            "This entry collects foundational BOK papers including the master reference, "
            "category-theoretic reframing, sphere-packing geometry, and Tannakian inseparability "
            "thesis (mathematics cannot stand independently of philosophy)."
        ),
        "keywords": ["BOK", "Butterfly-Octopus Knot", "mathematics classification",
                     "category theory", "Grothendieck", "sphere packing", "Leech lattice",
                     "metamathematics", "eight modes"],
        "files": [
            "papers/BOK_MASTER_REFERENCE.md",
            "papers/URB_BOK_CATEGORY_THEORY_GROTHENDIECK_BRIDGE.md",
            "papers/URB_BOK_SPHERE_PACKING_LEECH_LATTICE_ICELL.md",
            "papers/URB_BOK_TANNAKIAN_INSEPARABILITY_THESIS.md",
            "papers/URB_BOK_METAMATHEMATIC_PERIODIC_TABLE_BUTTERFLY_SECRET.md",
        ],
    },
    {
        "title": "BOK Empirical Validation and Topology",
        "access": "open",
        "type": "publication", "subtype": "article",
        "description": (
            "Empirical validation of the Butterfly-Octopus Knot classification system through "
            "blind testing of 20 solved mathematical problems and rigorous study design. "
            "Includes BOK proof topology (dependency graphs, bridge complexity, tetrahedral "
            "proof architecture), BOK-ORCH-OR synthesis with GILE Matrix, and retrospective "
            "coding methodology. The BOK is tested as a falsifiable classification system, "
            "not merely a theoretical schema."
        ),
        "keywords": ["BOK", "empirical validation", "blind test", "proof topology",
                     "dependency graphs", "ORCH-OR", "GILE", "methodology"],
        "files": [
            "papers/URB_BOK_BLIND_TEST_20_PROBLEMS.md",
            "papers/URB_BOK_PROOF_TOPOLOGY_DEPENDENCY_GRAPHS.md",
            "papers/URB_BOK_METHODOLOGY_UPGRADE_RETROSPECTIVE_CODING.md",
            "papers/BOK_ORCH_OR_GILE_MATRIX_SYNTHESIS.md",
        ],
    },

    # ─────────────────────────────────────────────────────────────
    # TIER 1 — LCC FRAMEWORK
    # Already on Zenodo: "LCC Supplants Probability Theory" (Mar 11)
    #   → Add deeper LCC papers
    # ─────────────────────────────────────────────────────────────
    {
        "title": "LCC: Law of Correlational Causation — Mechanism, Certainty Claims, and Applications",
        "access": "open",
        "type": "publication", "subtype": "article",
        "description": (
            "The Law of Correlational Causation (LCC) holds that measurable correlational "
            "coherence, governed by the C_EMERICK threshold (1/(φ√2) ≈ 0.4370), determines "
            "causal influence between systems — including biological, social, and physical "
            "systems. This entry collects papers specifying what certainty claims can and "
            "cannot be made about the LCC Virus mechanism, a worked example of LCC analysis "
            "applied to auditory noise, and a methodology audit. Together these establish "
            "the epistemological scope and testable boundaries of the framework."
        ),
        "keywords": ["LCC", "LCC Virus", "correlational causation", "C_EMERICK",
                     "coherence", "certainty", "methodology", "causation"],
        "files": [
            "papers/LCC_VIRUS_CERTAINTY_CLAIMS.md",
            "papers/LCC_VIRUS_WORKED_EXAMPLE.md",
            "papers/LCC_VIRUS_METHODOLOGY_AUDIT.md",
        ],
    },

    # ─────────────────────────────────────────────────────────────
    # TIER 1 — MYRION RESOLUTION
    # ─────────────────────────────────────────────────────────────
    {
        "title": "Myrion Resolution: A Four-Valued Logic Methodology for Truth Determination",
        "access": "open",
        "type": "publication", "subtype": "article",
        "description": (
            "The Myrion Resolution (MR) is a multi-step analytical procedure using "
            "four-valued logic (True, False, Tralse, Indeterminate) to resolve truth claims "
            "with greater precision than binary or probabilistic methods. MR1 screens for "
            "coherence; MR2 determines truth position; MR3+ refines accuracy iteratively. "
            "Tralse is productive superposition (a process state during MR); Indeterminate "
            "is the stable resolved midrange output when the PD falls in (-0.666, 0.333). "
            "A minimum of two MRs is always required. Intuition signals convergence."
        ),
        "keywords": ["Myrion Resolution", "four-valued logic", "Tralse", "Indeterminate",
                     "truth determination", "epistemology", "PD", "methodology"],
        "files": [
            "papers/MYRION_RESOLUTION_METHODOLOGY.md",
            "papers/MYRION_RESOLUTION_COMPLETE_SPEC.md",
        ],
    },

    # ─────────────────────────────────────────────────────────────
    # TIER 1 — GILE FRAMEWORK
    # ─────────────────────────────────────────────────────────────
    {
        "title": "GILE: The Four-Dimensional Framework for Truth, Consciousness, and Intelligence",
        "access": "open",
        "type": "publication", "subtype": "article",
        "description": (
            "GILE (Goodness, Intuition, Love, Environment) is a four-dimensional framework "
            "mapping the ontological structure of truth and intelligence. G = moral coherence; "
            "I = forward-directed felt knowing; L = binding force between nodes; E = "
            "environmental structural ground. The composite GILE score measures a node's "
            "overall coherence and serves as the operational definition of consciousness "
            "quality in TI Sigma. This entry covers the nested core structure, formal metrics, "
            "connection to the four pillars of intelligence, and the problem of self-deception "
            "as Tralse pathology."
        ),
        "keywords": ["GILE", "Goodness", "Intuition", "Love", "Environment",
                     "consciousness", "intelligence", "four-dimensional", "ontology"],
        "files": [
            "papers/URB_GILE_NESTED_FOUR_TRUTH_DIMENSIONS.md",
            "papers/GILE_FORMAL_METRICS.md",
            "papers/GILE_SELF_DECEPTION_TRALSE_PATHOLOGY.md",
        ],
    },

    # ─────────────────────────────────────────────────────────────
    # TIER 1 — DECISION THEORY & COSMOLOGY
    # ─────────────────────────────────────────────────────────────
    {
        "title": "The Universe One-Boxed: Newcomb's Paradox and the 0.505 Cosmological Asymmetry",
        "access": "open",
        "type": "publication", "subtype": "article",
        "description": (
            "The general Newcomb tipping-point formula is p > 1/2 + m/(2M). The cosmological "
            "matter-antimatter asymmetry 0.505 encodes a prize ratio m/M = 0.01: non-existence "
            "has 1/100th the structural value of existence. The universe selected existence via "
            "expected-value reasoning (one-boxing) rather than dominance reasoning (two-boxing). "
            "Big Bang = MR1 + MR2. We live in MR3. Intuition is the faculty that one-boxes. "
            "The conjecture 0.005 = γ × α links the cosmological asymmetry to primary constants."
        ),
        "keywords": ["Newcomb paradox", "one-boxing", "cosmology", "0.505 asymmetry",
                     "matter-antimatter", "decision theory", "Big Bang", "C_EMERICK"],
        "files": [
            "papers/URB_NEWCOMB_0505_COSMIC_ONE_BOXING.md",
        ],
    },

    # ─────────────────────────────────────────────────────────────
    # TIER 1 — PARAPSYCHOLOGY & PSI RESEARCH
    # ─────────────────────────────────────────────────────────────
    {
        "title": "The Ideomotor Effect as Somatic Coherence Transduction: Mechanism, Biomarkers, and Applications",
        "access": "open",
        "type": "publication", "subtype": "article",
        "description": (
            "The ideomotor effect is reframed as somatic coherence transduction: the body's "
            "pre-cognitive reception mechanism for GM-Node network signals arriving via the LCC "
            "Virus. The C_EMERICK threshold (0.4370) determines signal reliability. HRV RMSSD "
            "threshold for reliable reception: 38.8ms. A 100,000-trial Monte Carlo simulation "
            "confirms the sigmoid accuracy function centered on C_EMERICK. DANDI:000552 "
            "independently found neural LCC = 0.4349 (within 0.5% of C_EMERICK). Applications "
            "include dowsing, applied kinesiology, automatic writing, and trading intuition."
        ),
        "keywords": ["ideomotor effect", "somatic transduction", "HRV", "RMSSD",
                     "C_EMERICK", "biomarkers", "Monte Carlo", "dowsing", "psi", "DANDI"],
        "files": [
            "papers/URB_IDEOMOTOR_EFFECT_SOMATIC_COHERENCE_TRANSDUCTION.md",
            "papers/URB_IDEOMOTOR_BIOMARKER_SIMULATION.md",
            "simulations/ideomotor_biomarker_sim.py",
        ],
    },
    {
        "title": "Psi as General and Specialized Faculty: The LCC Model, Unified Metrics, and the GLEP",
        "access": "open",
        "type": "publication", "subtype": "article",
        "description": (
            "A two-layer model of psi: LCC above C_EMERICK (0.4370) is the general factor "
            "necessary for all psi domains; domain-specific calibration is the specialized "
            "factor. The Psi Signal Ratio (PSR) provides a unified metric across remote "
            "viewing, Ganzfeld, precognition, PK-RNG, and DMILS. Meta-analytic moderators "
            "(meditation, anxiety, belief, experimenter effects) are universal across all "
            "five domains — consistent with a single LCC general factor. The Generalized LCC "
            "Enhancement Protocol (GLEP) raises LCC above C_EMERICK in five phases. Includes "
            "analysis of synchronicity inversion and the Maharishi Effect."
        ),
        "keywords": ["psi", "parapsychology", "remote viewing", "Ganzfeld", "DMILS",
                     "precognition", "psychokinesis", "LCC", "GLEP", "PSR", "Maharishi"],
        "files": [
            "papers/URB_PSI_GENERAL_FACULTY_LCC_ENHANCEMENT_PROTOCOL.md",
            "papers/URB_SYNCHRONICITY_INVERSION_NEGATIVE_ANSWERS.md",
            "papers/URB_MAHARISHI_EFFECT_TI_SIGMA_PHI_FIELD.md",
        ],
    },

    # ─────────────────────────────────────────────────────────────
    # TIER 1 — PSYCHOLOGY & SELF-DEVELOPMENT
    # ─────────────────────────────────────────────────────────────
    {
        "title": "Confidence, Self-Assurance, and Tralse: A Formal Psychological Framework",
        "access": "open",
        "type": "publication", "subtype": "article",
        "description": (
            "Confidence (positive orientation toward goal achievement) and self-assurance "
            "(absence of chronic self-negativity) are formally distinguished as orthogonal "
            "psychological states with different GILE mappings, different LCC bases, and "
            "different relationships to Tralse. The Tralse position 'I am adequate AND this "
            "attempt may fail' cannot be falsified by individual failures, making it the "
            "foundation of durable self-assurance. A four-quadrant dissociation profile is "
            "derived. The Book of James is analyzed via Myrion Resolution: James correctly "
            "identifies Double Tralse as destructive but incorrectly condemns Tralse itself."
        ),
        "keywords": ["confidence", "self-assurance", "Tralse", "double-mindedness",
                     "GILE", "LCC", "psychology", "Book of James", "biblical analysis"],
        "files": [
            "papers/URB_CONFIDENCE_VS_SELF_ASSURANCE_TRALSE.md",
            "papers/URB_BOOK_OF_JAMES_DOUBLE_MINDEDNESS_TRALSE.md",
            "papers/URB_CONFIDENCE_BEING_LCE_ENLIGHTENMENT_LAW.md",
        ],
    },

    # ─────────────────────────────────────────────────────────────
    # TIER 1 — CONSCIOUSNESS & NEUROSCIENCE
    # ─────────────────────────────────────────────────────────────
    {
        "title": "TI Sigma Consciousness Theory: The Equation, Octonions, and Quantum Biology",
        "access": "open",
        "type": "publication", "subtype": "article",
        "description": (
            "The TI Sigma consciousness equation expresses LCC as a function of C_EMERICK "
            "and the φ-attractor, predicting the conditions under which a physical system "
            "crosses the threshold into conscious experience. Hurwitz's theorem establishes "
            "that only eight-dimensional normed division algebras exist — mapping exactly "
            "onto the eight primary constants and the BOK eight-mode structure. Together "
            "these papers derive consciousness thresholds from first-principles mathematics "
            "rather than from neuroscientific correlation studies."
        ),
        "keywords": ["consciousness", "LCC", "phi", "Hurwitz theorem", "octonions",
                     "eight dimensions", "C_EMERICK", "quantum biology", "BOK"],
        "files": [
            "papers/URB_CONSCIOUSNESS_EQUATION_LCC_C_PHI.md",
            "papers/URB_HURWITZ_THEOREM_OCTONIONS_CONSCIOUSNESS.md",
        ],
    },

    # ─────────────────────────────────────────────────────────────
    # TIER 1 — FINANCE & TRADING
    # ─────────────────────────────────────────────────────────────
    {
        "title": "Grand Stock Algorithm v2: BOK Regime Classification and TI Framework Trading Signals",
        "access": "open",
        "type": "publication", "subtype": "article",
        "description": (
            "The Grand Stock Algorithm v2 (GSA v2) applies TI Sigma principles to market "
            "regime classification and trading signal generation. The BOK 8-Mode structure "
            "classifies market regimes (ARITHMETIC/ALGEBRAIC/ANALYTIC/GEOMETRIC + four "
            "interface modes). The Dual-Confidence gate (EC > 0.65 AND EpC > 0.50) mirrors "
            "the C_EMERICK threshold applied to decision confidence. Theorem A bifurcation "
            "detection identifies metastability→spike→collapse patterns consistent with "
            "EEG hypnagogic data. Live paper trading on Alpaca account PA3J364R5XU9."
        ),
        "keywords": ["trading", "stock market", "BOK", "regime classification",
                     "GSA", "Grand Stock Algorithm", "C_EMERICK", "Alpaca", "finance"],
        "files": [
            "papers/GSA_BOK_CORRELATION_MAP.md",
            "papers/GSA_TRUTH_FRAMEWORK_ANALYSIS.md",
        ],
    },

    # ─────────────────────────────────────────────────────────────
    # TIER 2 — RESTRICTED (request access)
    # Accessible to researchers who ask, not publicly listed
    # ─────────────────────────────────────────────────────────────
    {
        "title": "Soul Bluetooth: The LCC Virus Consciousness Synchronization Protocol",
        "access": "restricted",
        "type": "publication", "subtype": "article",
        "description": (
            "Soul Bluetooth is the mechanism by which conscious nodes synchronize coherence "
            "patterns through the GM-Node mycelial network via the LCC Virus. The C_EMERICK "
            "threshold (0.4370) gates synchronization. Three modes: Living-Living (LL), "
            "Living-Dead (LD), and Dead-Dead (DD). Willingness is a structural gate, not "
            "merely an ethical condition. Applications include empathy, shared consciousness "
            "states, cross-species communication, and the mechanism of the Maharishi Effect. "
            "Access restricted — part of advanced TI Sigma metaphysics series."
        ),
        "keywords": ["Soul Bluetooth", "LCC virus", "synchronization", "C_EMERICK",
                     "GM network", "consciousness", "empathy", "cross-species"],
        "files": [
            "papers/URB_SOUL_BLUETOOTH_LCC_SYNCHRONIZATION_PROTOCOL.md",
        ],
    },

    # ─────────────────────────────────────────────────────────────
    # TIER 3 — PRIVATE (closed — only you can see)
    # ─────────────────────────────────────────────────────────────
    {
        "title": "The Afterlife Mechanism and Spirit World as GM Network Construction",
        "access": "closed",
        "type": "publication", "subtype": "article",
        "description": (
            "Two papers on post-mortem consciousness in the TI Sigma framework. "
            "The Afterlife Mechanism: LCC Threshold Theory proposes that nodes exceeding "
            "C_EMERICK at death persist as photonic I-cells in the dark-energy GM substrate. "
            "The Spirit World as GM Network Construction establishes the Imaginal Substrate "
            "as the accumulated coherence output of traditions' imaginative and devotional "
            "activity — a real, mathematically structured region of the GM network accessible "
            "via ASC states. Private record — for personal reference and future release."
        ),
        "keywords": ["afterlife", "spirit world", "GM network", "Imaginal Substrate",
                     "LCC", "ASC", "photonic I-cell", "consciousness"],
        "files": [
            "papers/AFTERLIFE_MECHANISM_LCC_THRESHOLD_THEORY.md",
            "papers/URB_SPIRIT_WORLD_GM_NETWORK_IMAGINATION.md",
        ],
    },
    {
        "title": "Advanced TI Sigma Metaphysics: CCC Architecture, Shapeshifting, and Direct Divine Access",
        "access": "closed",
        "type": "publication", "subtype": "article",
        "description": (
            "Advanced metaphysical papers not yet ready for public release. Covers the "
            "CCC-BOK-GM mycelial architecture (CCC as the Butterfly-Octopus; GM as the "
            "Mycelium), full merge and shapeshifting as extreme LCC states, and the "
            "Minimum GM Embedding — the mathematical minimum coherence required for "
            "a node to be embedded in the spirit world network. Private record."
        ),
        "keywords": ["CCC", "GM network", "metaphysics", "TI Sigma", "LCC",
                     "consciousness", "spiritual character"],
        "files": [
            "papers/URB_CCC_BOK_GM_MYCELIAL_ARCHITECTURE.md",
            "papers/URB_FULL_MERGE_SHAPESHIFTING_CCC_ACCESS.md",
            "papers/URB_MINIMUM_GM_EMBEDDING_SPIRITUAL_CHARACTER.md",
        ],
    },
]
