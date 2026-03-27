"""
TI Sigma Paper Classification System
Handles DB schema, keyword-based classification, and export utilities.

Classification uses a keyword/heuristic engine (no external API needed).
Runs entirely free and offline. The AI enhance path is available when APIs work.
"""
import os
import json
import time
import re
import psycopg2
from pathlib import Path
from datetime import datetime

PAPERS_DIR = Path("papers")

RADICALITY_RUBRIC = """
1 = Accepted mainstream science — standard empirical methods, no TI-specific claims, publishable in Nature/Science.
2 = Heterodox but citable — challenges conventions but uses recognized data/citations; plausible to philosophy-of-mind or consciousness-studies journals.
3 = Speculative with partial support — PSI, quantum consciousness, holistic models, partial empirical grounding; fringe peer-reviewed (Neuroquantology) realistic target.
4 = Paradigm-challenging — TI Sigma mathematical framework (LCC, GILE, PD zones, MR gates) as fundamental laws; Zenodo primary venue.
5 = Entirely novel framework — afterlife mechanisms, CCC as substrate, direct PSI transmission, no mainstream acceptance pathway; Zenodo private.
"""

JOURNAL_RUBRIC = """
top_tier             = Nature, Science, PNAS, Frontiers, PLOS ONE, eLife
mid_tier             = MDPI (Entropy, Symmetry), Minds & Machines, Journal of Consciousness Studies, Biological Theory
fringe_peer_reviewed = Neuroquantology, Journal of Non-Locality, Dynamical Psychology, Explore, Cosmos & History
zenodo_only          = too radical for peer-review; Zenodo is primary venue
"""

DOMAIN_LIST = [
    "consciousness", "physics", "mathematics", "philosophy", "psychology",
    "neuroscience", "biology", "finance", "computing", "quantum",
    "music_sound", "psychology_clinical", "social_theory", "spirituality",
    "language", "ecology", "information_theory",
]

ARXIV_CATEGORIES = {
    "mathematics":        "math.HO",
    "physics":            "physics.gen-ph",
    "computing":          "cs.AI",
    "philosophy":         "physics.hist-ph",
    "quantum":            "quant-ph",
    "information_theory": "cs.IT",
}

ARXIV_ALLOWED_DOMAINS = {
    "mathematics", "physics", "computing", "philosophy",
    "quantum", "information_theory",
}

# ── Keyword rule sets ──────────────────────────────────────────────────────────

# Radical-5 topics: entirely novel, no mainstream pathway
RAD5_KEYWORDS = [
    "afterlife", "ccc", "central_cosmic", "psi_transmission", "telekinesis",
    "remote_viewing", "astral", "soul", "reincarnation", "spirit",
    "yogic_energy", "bliss_activation", "chakra_physics", "whole_body_chakra",
    "grand_psi", "psi_proof", "animal_psi", "manifestation_machine",
    "power_of_8", "intention_field", "non_local_consciousness",
    "afterlife_mechanism", "lcc_threshold_theory",
]

# Radical-4 topics: TI Sigma mathematical framework as fundamental law
RAD4_KEYWORDS = [
    "ti_sigma", "tralse", "lcc", "gile", "myrion", "pd_zone", "urb",
    "universal_reality", "emerick", "primary_constant", "bok",
    "butterfly_octopus", "true_tralse", "mr1", "mr2", "mr_radiant",
    "4_valued", "four_valued", "ternary", "tralse_free_energy", "tfep",
    "permissibility_distribution", "i_cell", "uop", "existence_gate",
    "causation_gate", "crystallized_tralse", "ast_theorem",
    "arithmetic_scaffold", "messy_math", "quantum_tralse", "verisyn",
    "anti_gile", "ontological_holes", "agi_impossibility", "gm_hypercomputer",
    "ji_boundary", "i_completeness", "minimal_operations",
]

# Radical-3 topics: speculative but partially grounded
RAD3_KEYWORDS = [
    "psi", "quantum_consciousness", "quantum_biology", "quantum_cognition",
    "non_local", "telepathy", "intuition", "synchronicity",
    "consciousness_proof", "a_priori_consciousness", "integrated_information",
    "iit", "phi_measure", "global_workspace", "hard_problem",
    "aperiodic", "einstein_tiling", "penrose", "quasicrystal",
    "holographic", "morphic_resonance", "epigenetic",
    "acupuncture", "meridian", "chakra", "biofield", "biophoton",
    "water_memory", "homeopathy", "plant_consciousness",
    "lucid_dream", "out_of_body", "oob", "hypnagogic",
    "alarm_free", "acetylcholine_dream",
    "autism_deconstruction", "schizophrenia_tralse",
    "autism_schizophrenia", "dimensional_framework",
]

# Radical-2 topics: heterodox but citable
RAD2_KEYWORDS = [
    "affection", "love_primacy", "agape", "homophobia", "gile_love",
    "emotion_theory", "attitude_emotion", "social_psychology",
    "consciousness_studies", "philosophy_of_mind", "phenomenology",
    "free_will", "determinism", "moral_philosophy",
    "evolutionary", "adaptation", "fitness", "natural_selection",
    "trauma", "ptsd", "resilience", "mental_health",
    "meditation", "mindfulness", "contemplative", "maharishi",
    "tm_meditation", "coherence", "heart_coherence",
    "affective_science", "emotional_regulation",
    "transpersonal", "peak_experience", "flow_state",
]

# Mainstream (radical-1): standard empirical / data-driven
RAD1_KEYWORDS = [
    "statistical_analysis", "p_value", "regression", "control_group",
    "clinical_trial", "randomized", "meta_analysis", "systematic_review",
    "affection_decline_data", "data_analysis_evidence",
    "holmes_rahe", "stress_scale", "life_events", "hrv_analysis",
    "eeg_analysis", "brain_wave", "sleep_analysis",
    "stock_analysis", "financial_data", "market_analysis",
    "ai_code_verification", "calculator_accuracy",
    "competition_strategy", "arc_critique", "arc_debunking",
]

# Formal proof indicators
PROOF_KEYWORDS = [
    "lean", "coq", "agda", "isabelle", "proof_assistant",
    "formally_verified", "theorem_proof", "qed", "axiom",
    "lemma", "proposition", "formally", "five_formally_verified",
    "impossibility_proof", "proof_that", "mathematical_proof",
    "existence_proof", "constructive_proof",
]

# Domain keyword maps
DOMAIN_KEYWORDS = {
    "mathematics":       ["theorem", "proof", "tiling", "aperiodic", "einstein_tiling",
                          "arithmetic", "scaffold", "riemann", "prime", "zero",
                          "fibonacci", "golden_ratio", "topology", "string_theory",
                          "24d_sufficiency", "26d"],
    "physics":           ["quantum", "physics", "relativity", "string_theory", "cosmology",
                          "wave_function", "collapse", "decoherence", "entanglement",
                          "bohr", "planck", "entropy"],
    "consciousness":     ["consciousness", "awareness", "sentience", "qualia", "phenomenal",
                          "hard_problem", "ccc", "psi", "subjective_experience"],
    "philosophy":        ["philosophy", "ontology", "epistemology", "metaphysics",
                          "ethics", "moral", "truth", "reality", "existence",
                          "free_will", "determinism", "tralse", "informationalism"],
    "psychology":        ["psychology", "emotion", "behavior", "cognition", "personality",
                          "adhd", "autism", "therapy", "trauma", "affection"],
    "neuroscience":      ["brain", "neural", "eeg", "neuro", "cortex", "synapse",
                          "dopamine", "serotonin", "faah", "acetylcholine", "hrv"],
    "biology":           ["biology", "evolution", "gene", "dna", "cell", "organism",
                          "epigenetic", "biophoton", "biofield"],
    "finance":           ["stock", "market", "trading", "algorithm", "gsa",
                          "financial", "investment", "alpaca", "kalshi"],
    "computing":         ["ai", "algorithm", "agi", "machine_learning", "arc",
                          "computation", "ternary", "quantum_computing", "code"],
    "quantum":           ["quantum", "entanglement", "superposition", "collapse",
                          "wave_function", "non_local", "bell_test"],
    "spirituality":      ["yogic", "chakra", "meridian", "bliss", "meditation",
                          "consciousness_evolution", "spirit", "soul", "afterlife",
                          "maharishi", "vedic", "psi", "intention"],
    "music_sound":       ["music", "sound", "frequency", "entrainment", "brainwave",
                          "binaural", "432hz", "harmonic", "resonance"],
    "information_theory": ["information", "entropy", "shannon", "kolmogorov",
                           "compression", "ticl", "ternary_computation"],
    "social_theory":     ["society", "social", "culture", "political", "economic",
                          "american_phase", "phase_transition", "systemic"],
    "ecology":           ["ecology", "environment", "sustainability", "ecovillage",
                          "climate", "biodiversity"],
    "psychology_clinical": ["clinical", "therapy", "treatment", "disorder", "diagnosis",
                             "anxiety", "depression", "adhd", "ptsd"],
    "language":          ["language", "semantics", "pragmatics", "linguistic", "metaphor",
                          "meaning", "symbol"],
}


def _text_to_tokens(text: str) -> set:
    """Normalize text to lowercase tokens for keyword matching."""
    text = text.lower()
    text = re.sub(r"[^a-z0-9_\s]", " ", text)
    return set(text.split())


def _slug_tokens(filename: str) -> set:
    """Get lowercase underscore-joined tokens from filename."""
    stem = Path(filename).stem.lower()
    tokens = set(stem.split("_"))
    tokens.add(stem)  # also check full stem
    # add bigrams and trigrams
    parts = stem.split("_")
    for i in range(len(parts) - 1):
        tokens.add(f"{parts[i]}_{parts[i+1]}")
    for i in range(len(parts) - 2):
        tokens.add(f"{parts[i]}_{parts[i+1]}_{parts[i+2]}")
    return tokens


def _match_keywords(tokens: set, keywords: list) -> bool:
    """Check if any keyword (underscore-separated) matches in the token set."""
    for kw in keywords:
        kw_low = kw.lower()
        kw_parts = set(kw_low.split("_"))
        if kw_low in tokens:
            return True
        if len(kw_parts) > 1 and kw_parts.issubset(tokens):
            return True
    return False


def _classify_paper(filename: str, title: str, content_snippet: str) -> dict:
    """
    Rules-based classification using filename + title + content snippet.
    Returns classification dict.
    """
    # Build token set from filename, title, and first 1500 chars of content
    combined = f"{filename} {title} {content_snippet[:1500]}"
    tokens   = _text_to_tokens(combined)
    slug     = _slug_tokens(filename)
    all_tok  = tokens | slug

    # ── Radicality ─────────────────────────────────────────────────────────────
    if _match_keywords(all_tok, RAD5_KEYWORDS):
        radicality = 5
    elif _match_keywords(all_tok, RAD4_KEYWORDS):
        radicality = 4
    elif _match_keywords(all_tok, RAD3_KEYWORDS):
        radicality = 3
    elif _match_keywords(all_tok, RAD2_KEYWORDS):
        radicality = 2
    elif _match_keywords(all_tok, RAD1_KEYWORDS):
        radicality = 1
    else:
        # Default: if filename contains TI-specific terms → 4, else 3
        ti_terms = {"urb", "gile", "lcc", "tralse", "myrion", "bok", "ti_sigma"}
        radicality = 4 if all_tok & ti_terms else 3

    # ── Formal proof ───────────────────────────────────────────────────────────
    has_formal_proof = _match_keywords(all_tok, PROOF_KEYWORDS)

    # ── Journal tier ───────────────────────────────────────────────────────────
    if radicality == 1:
        journal_tier = "mid_tier"
    elif radicality == 2:
        journal_tier = "mid_tier"
    elif radicality == 3:
        journal_tier = "fringe_peer_reviewed"
    else:
        journal_tier = "zenodo_only"

    # Upgrade to top_tier if content mentions top venues and radicality <= 2
    if radicality <= 2 and any(kw in all_tok for kw in ["nature", "science", "pnas", "lancet"]):
        journal_tier = "top_tier"

    # ── Domain tags ─────────────────────────────────────────────────────────────
    domains = []
    for domain, kws in DOMAIN_KEYWORDS.items():
        if _match_keywords(all_tok, kws):
            domains.append(domain)

    if not domains:
        domains = ["philosophy"]
    if len(domains) > 4:
        # Limit to 4 most specific domains
        priority = ["consciousness", "mathematics", "physics", "neuroscience",
                    "computing", "finance", "biology", "quantum"]
        domains = sorted(domains, key=lambda d: priority.index(d) if d in priority else 99)[:4]

    return {
        "radicality_score":  radicality,
        "has_formal_proof":  has_formal_proof,
        "journal_tier":      journal_tier,
        "domain_tags":       domains,
        "zenodo_status":     "unpublished",
    }


# ── Database ───────────────────────────────────────────────────────────────────

def get_db():
    return psycopg2.connect(os.environ["DATABASE_URL"])


def init_classification_db():
    conn = get_db()
    cur  = conn.cursor()
    cur.execute("""
        CREATE TABLE IF NOT EXISTS paper_classifications (
            id                  SERIAL PRIMARY KEY,
            filename            TEXT UNIQUE NOT NULL,
            title               TEXT,
            radicality_score    INTEGER CHECK (radicality_score BETWEEN 1 AND 5),
            has_formal_proof    BOOLEAN DEFAULT FALSE,
            journal_tier        TEXT CHECK (journal_tier IN (
                                    'top_tier','mid_tier',
                                    'fringe_peer_reviewed','zenodo_only')),
            platform_assignment TEXT[],
            domain_tags         TEXT[],
            zenodo_doi          TEXT,
            zenodo_status       TEXT DEFAULT 'unpublished'
                                    CHECK (zenodo_status IN (
                                        'published','unpublished','private')),
            user_notes          TEXT,
            last_classified_at  TIMESTAMP,
            created_at          TIMESTAMP DEFAULT NOW()
        )
    """)
    conn.commit()
    cur.close()
    conn.close()


def get_all_classifications():
    conn = get_db()
    cur  = conn.cursor()
    cur.execute("""
        SELECT filename, title, radicality_score, has_formal_proof,
               journal_tier, platform_assignment, domain_tags,
               zenodo_doi, zenodo_status, user_notes, last_classified_at
        FROM paper_classifications
        ORDER BY filename
    """)
    cols = [d[0] for d in cur.description]
    rows = [dict(zip(cols, r)) for r in cur.fetchall()]
    cur.close()
    conn.close()
    return rows


def upsert_classification(data: dict):
    conn = get_db()
    cur  = conn.cursor()
    cur.execute("""
        INSERT INTO paper_classifications
            (filename, title, radicality_score, has_formal_proof,
             journal_tier, platform_assignment, domain_tags,
             zenodo_doi, zenodo_status, user_notes, last_classified_at)
        VALUES (%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s)
        ON CONFLICT (filename) DO UPDATE SET
            title               = EXCLUDED.title,
            radicality_score    = EXCLUDED.radicality_score,
            has_formal_proof    = EXCLUDED.has_formal_proof,
            journal_tier        = EXCLUDED.journal_tier,
            platform_assignment = EXCLUDED.platform_assignment,
            domain_tags         = EXCLUDED.domain_tags,
            zenodo_doi          = COALESCE(EXCLUDED.zenodo_doi, paper_classifications.zenodo_doi),
            zenodo_status       = EXCLUDED.zenodo_status,
            user_notes          = COALESCE(EXCLUDED.user_notes, paper_classifications.user_notes),
            last_classified_at  = EXCLUDED.last_classified_at
    """, (
        data["filename"],
        data.get("title"),
        data.get("radicality_score"),
        data.get("has_formal_proof", False),
        data.get("journal_tier"),
        data.get("platform_assignment", []),
        data.get("domain_tags", []),
        data.get("zenodo_doi"),
        data.get("zenodo_status", "unpublished"),
        data.get("user_notes"),
        datetime.now(),
    ))
    conn.commit()
    cur.close()
    conn.close()


def update_field(filename: str, field: str, value):
    allowed = {"radicality_score", "has_formal_proof", "journal_tier",
               "platform_assignment", "domain_tags", "zenodo_doi",
               "zenodo_status", "user_notes", "title"}
    if field not in allowed:
        raise ValueError(f"Field {field!r} not editable")
    conn = get_db()
    cur  = conn.cursor()
    cur.execute(
        f"UPDATE paper_classifications SET {field} = %s WHERE filename = %s",
        (value, filename)
    )
    conn.commit()
    cur.close()
    conn.close()


def get_classified_filenames():
    conn = get_db()
    cur  = conn.cursor()
    cur.execute("SELECT filename FROM paper_classifications")
    result = {r[0] for r in cur.fetchall()}
    cur.close()
    conn.close()
    return result


def extract_paper_snippet(md_path: Path, max_chars: int = 1500) -> tuple:
    """Extract (title, snippet) from a paper for classification."""
    try:
        text = md_path.read_text(encoding="utf-8", errors="ignore")
    except Exception:
        return md_path.stem.replace("_", " ").title(), ""

    lines = text.splitlines()
    title = md_path.stem.replace("_", " ").title()

    for line in lines:
        if line.startswith("# "):
            title = line[2:].strip()
            break

    snippet = text[:max_chars].strip()
    return title, snippet


def build_assignment(radicality: int, domains: list = None) -> list:
    """
    Derive platform_assignment from radicality + domains.
    arXiv requires radicality 1-3 AND at least one allowed domain
    (math/physics/cs/philosophy/quantum/biology/neuroscience/consciousness/finance/info-theory).
    """
    platforms = []
    domain_set = set(domains or [])
    if radicality <= 2:
        platforms.append("researchgate")
    if radicality <= 3 and bool(domain_set & ARXIV_ALLOWED_DOMAINS):
        platforms.append("arxiv")
    if radicality <= 4:
        platforms.append("zenodo_public")
    if radicality == 5:
        platforms.append("zenodo_private")
    return platforms


def run_batch_classification(force: bool = False,
                              progress_fn=None) -> dict:
    """
    Classify all unclassified papers using the keyword/heuristic engine.
    Skip already classified unless force=True.
    Returns {"classified": N, "skipped": N, "failed": N}
    """
    init_classification_db()
    all_mds = sorted(PAPERS_DIR.glob("*.md"))
    already  = get_classified_filenames() if not force else set()
    todo     = [p for p in all_mds if p.name not in already]

    classified = 0
    failed     = 0
    skipped    = len(all_mds) - len(todo)

    for i, md_path in enumerate(todo):
        if progress_fn and i % 10 == 0:
            progress_fn(i + 1, len(todo))

        title, snippet = extract_paper_snippet(md_path)
        result = _classify_paper(md_path.name, title, snippet)

        data = {
            "filename":            md_path.name,
            "title":               title,
            "radicality_score":    result["radicality_score"],
            "has_formal_proof":    result["has_formal_proof"],
            "journal_tier":        result["journal_tier"],
            "platform_assignment": build_assignment(result["radicality_score"], result["domain_tags"]),
            "domain_tags":         result["domain_tags"],
            "zenodo_status":       result["zenodo_status"],
        }
        try:
            upsert_classification(data)
            classified += 1
        except Exception as e:
            print(f"DB upsert failed for {md_path.name}: {e}")
            failed += 1

    return {"classified": classified, "skipped": skipped, "failed": failed}


# ── Export helpers ─────────────────────────────────────────────────────────────

def _derive_description(filename: str, title: str, max_chars: int = 160) -> str:
    """Pull first non-header, non-empty sentence from the paper as a one-line description."""
    md_path = PAPERS_DIR / filename
    if not md_path.exists():
        return ""
    try:
        text = md_path.read_text(encoding="utf-8", errors="ignore")
        for line in text.splitlines():
            line = line.strip()
            if not line or line.startswith("#") or line.startswith("**") or line.startswith("|"):
                continue
            if len(line) < 20:
                continue
            return line[:max_chars]
    except Exception:
        pass
    return ""


def get_researchgate_list() -> list:
    conn = get_db()
    cur  = conn.cursor()
    cur.execute("""
        SELECT filename, title, radicality_score, zenodo_doi, domain_tags, journal_tier
        FROM paper_classifications
        WHERE radicality_score <= 2
        ORDER BY radicality_score, filename
    """)
    cols = [d[0] for d in cur.description]
    rows = [dict(zip(cols, r)) for r in cur.fetchall()]
    cur.close()
    conn.close()
    for row in rows:
        row["short_description"] = _derive_description(row["filename"], row["title"])
    return rows


def get_arxiv_list() -> list:
    """Return papers eligible for arXiv: radicality 1-3 AND at least one arXiv-allowed domain."""
    conn = get_db()
    cur  = conn.cursor()
    cur.execute("""
        SELECT filename, title, radicality_score, domain_tags, journal_tier, zenodo_doi
        FROM paper_classifications
        WHERE radicality_score <= 3
        ORDER BY radicality_score, filename
    """)
    cols = [d[0] for d in cur.description]
    rows = [dict(zip(cols, r)) for r in cur.fetchall()]
    cur.close()
    conn.close()

    result = []
    for row in rows:
        tags      = row.get("domain_tags") or []
        tag_set   = set(tags)
        allowed   = tag_set & ARXIV_ALLOWED_DOMAINS
        if not allowed:
            continue
        category = "physics.gen-ph"
        for tag in tags:
            if tag in ARXIV_CATEGORIES:
                category = ARXIV_CATEGORIES[tag]
                break
        row["arxiv_category"] = category
        result.append(row)
    return result


def get_zenodo_privacy_map() -> list:
    conn = get_db()
    cur  = conn.cursor()
    cur.execute("""
        SELECT filename, title, radicality_score, zenodo_doi, zenodo_status, user_notes
        FROM paper_classifications
        WHERE radicality_score = 5
        ORDER BY filename
    """)
    cols = [d[0] for d in cur.description]
    rows = [dict(zip(cols, r)) for r in cur.fetchall()]
    cur.close()
    conn.close()
    return rows


def get_summary_counts() -> dict:
    conn = get_db()
    cur  = conn.cursor()

    def count(where=""):
        cur.execute(f"SELECT COUNT(*) FROM paper_classifications {where}")
        return cur.fetchone()[0]

    total  = count()
    rg     = count("WHERE radicality_score <= 2")
    arxiv  = count("WHERE 'arxiv' = ANY(platform_assignment)")
    zpub   = count("WHERE radicality_score <= 4")
    zpriv  = count("WHERE radicality_score = 5")
    proofs = count("WHERE has_formal_proof = TRUE")
    pub    = count("WHERE zenodo_status = 'published'")

    all_mds = len(list(PAPERS_DIR.glob("*.md")))
    cur.close()
    conn.close()

    return {
        "total_papers":     all_mds,
        "classified":       total,
        "unclassified":     all_mds - total,
        "researchgate":     rg,
        "arxiv":            arxiv,
        "zenodo_public":    zpub,
        "zenodo_private":   zpriv,
        "has_formal_proof": proofs,
        "zenodo_published": pub,
    }
