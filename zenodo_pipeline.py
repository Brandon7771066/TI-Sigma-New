"""
TI Sigma Zenodo Publication Pipeline
Handles: PDF generation, batch upload, versioning, status tracking.
"""
import os, requests, json, time, re, hashlib, logging
from pathlib import Path
from datetime import datetime
import markdown as md_lib
import psycopg2

log = logging.getLogger(__name__)

ZENODO_TOKEN   = os.environ.get("ZENODO_TOKEN", "")
ZENODO_BASE    = "https://zenodo.org/api"
PAPERS_DIR     = Path("papers")
ZENODO_HEADERS = {"Content-Type": "application/json"}

AUTHOR_META = {
    "name": "Emerick, Brandon Charles",
    "affiliation": "BlissGene Therapeutics / TI Sigma Research Institute",
    "orcid": ""
}

COMMUNITY_KEYWORDS = [
    "TI Sigma", "Tralse Informationalism", "GILE Framework",
    "consciousness", "primary constants", "LCC", "BOK",
    "quantum biology", "psi research", "Emerick Constant"
]

PUBLISHED_RECORDS = {
    18916599: "TI Sigma: Five Formally Verified Theorems",
    18930175: "Proofs For TI Sigma Meta-Theory",
    18929980: "Software Involving Entrainment Via LCC",
    18930896: "LCC Supplants Probability Theory"
}


# ── Database ──────────────────────────────────────────────────────────────────

def get_db():
    return psycopg2.connect(os.environ["DATABASE_URL"])


def init_zenodo_db():
    """Create tracking tables if they don't exist."""
    conn = get_db()
    cur = conn.cursor()
    cur.execute("""
        CREATE TABLE IF NOT EXISTS zenodo_uploads (
            id          SERIAL PRIMARY KEY,
            filename    TEXT UNIQUE NOT NULL,
            title       TEXT,
            zenodo_id   BIGINT,
            doi         TEXT,
            status      TEXT DEFAULT 'pending',
            batch       INTEGER DEFAULT 0,
            uploaded_at TIMESTAMP,
            notes       TEXT
        )
    """)
    cur.execute("""
        CREATE TABLE IF NOT EXISTS zenodo_batches (
            id          SERIAL PRIMARY KEY,
            batch_num   INTEGER UNIQUE NOT NULL,
            created_at  TIMESTAMP DEFAULT NOW(),
            total       INTEGER DEFAULT 0,
            published   INTEGER DEFAULT 0,
            status      TEXT DEFAULT 'in_progress'
        )
    """)
    conn.commit(); cur.close(); conn.close()


def get_upload_status():
    """Return all upload records."""
    conn = get_db()
    cur = conn.cursor()
    cur.execute("SELECT filename, title, zenodo_id, doi, status, batch, uploaded_at, notes FROM zenodo_uploads ORDER BY id DESC")
    rows = cur.fetchall()
    cur.close(); conn.close()
    return rows


def mark_uploaded(filename, title, zenodo_id, doi, batch=0, notes=""):
    conn = get_db()
    cur = conn.cursor()
    cur.execute("""
        INSERT INTO zenodo_uploads (filename, title, zenodo_id, doi, status, batch, uploaded_at, notes)
        VALUES (%s, %s, %s, %s, 'published', %s, NOW(), %s)
        ON CONFLICT (filename) DO UPDATE SET
            zenodo_id=EXCLUDED.zenodo_id, doi=EXCLUDED.doi,
            status='published', uploaded_at=NOW(), notes=EXCLUDED.notes
    """, (filename, title, zenodo_id, doi, batch, notes))
    conn.commit(); cur.close(); conn.close()


def mark_failed(filename, reason):
    conn = get_db()
    cur = conn.cursor()
    cur.execute("""
        INSERT INTO zenodo_uploads (filename, status, notes)
        VALUES (%s, 'failed', %s)
        ON CONFLICT (filename) DO UPDATE SET status='failed', notes=EXCLUDED.notes
    """, (filename, reason))
    conn.commit(); cur.close(); conn.close()


def get_already_uploaded():
    conn = get_db()
    cur = conn.cursor()
    cur.execute("SELECT filename FROM zenodo_uploads WHERE status='published'")
    rows = {r[0] for r in cur.fetchall()}
    cur.close(); conn.close()
    return rows


# ── PDF Generation ────────────────────────────────────────────────────────────

PDF_CSS = """
@page { margin: 2.2cm 2cm; size: A4; }
body { font-family: 'Georgia', serif; font-size: 11pt; line-height: 1.65;
       color: #111; max-width: 100%; }
h1 { font-size: 18pt; color: #1a1a2e; margin-top: 0; border-bottom: 2px solid #4a90d9;
     padding-bottom: 6px; }
h2 { font-size: 14pt; color: #16213e; margin-top: 1.4em; }
h3 { font-size: 12pt; color: #0f3460; }
p  { margin: 0.5em 0 0.8em 0; text-align: justify; }
code, pre { font-family: 'Courier New', monospace; background: #f5f5f5;
            padding: 2px 5px; border-radius: 3px; font-size: 9.5pt; }
pre { padding: 10px; white-space: pre-wrap; word-wrap: break-word; }
blockquote { border-left: 4px solid #4a90d9; margin-left: 0; padding-left: 14px;
             color: #333; font-style: italic; }
table { border-collapse: collapse; width: 100%; margin: 1em 0; font-size: 10pt; }
th { background: #1a1a2e; color: white; padding: 7px 10px; text-align: left; }
td { padding: 6px 10px; border-bottom: 1px solid #ddd; }
tr:nth-child(even) td { background: #f9f9f9; }
.header-block { background: #f0f4ff; border: 1px solid #4a90d9; border-radius: 6px;
                padding: 12px 16px; margin-bottom: 20px; font-size: 10pt; }
"""

TITLE_TEMPLATE = """
<div class="header-block">
<strong>TI Sigma Research Institute</strong> · BlissGene Therapeutics<br/>
<strong>Author:</strong> Brandon Charles Emerick · March 2026<br/>
<strong>Series:</strong> Universal Reality Blueprint (URB) Corpus
</div>
"""


def md_to_pdf(md_path: Path, pdf_path: Path) -> bool:
    """Convert a markdown file to a polished PDF. Returns True on success."""
    try:
        from weasyprint import HTML, CSS
        text = md_path.read_text(encoding="utf-8")
        html_body = md_lib.markdown(text, extensions=["tables", "fenced_code", "toc"])
        full_html = f"""
<!DOCTYPE html><html><head><meta charset="utf-8"/>
<style>{PDF_CSS}</style></head><body>
{TITLE_TEMPLATE}{html_body}
</body></html>"""
        HTML(string=full_html).write_pdf(
            str(pdf_path),
            stylesheets=[CSS(string=PDF_CSS)]
        )
        return True
    except Exception as e:
        log.warning(f"PDF generation failed for {md_path.name}: {e}")
        return False


def ensure_pdf(md_path: Path) -> Path:
    """Return PDF path, generating it if needed."""
    pdf_path = md_path.with_suffix(".pdf")
    if not pdf_path.exists():
        md_to_pdf(md_path, pdf_path)
    return pdf_path


# ── Zenodo API Helpers ────────────────────────────────────────────────────────

def _params():
    return {"access_token": ZENODO_TOKEN}


def list_depositions(status="published"):
    r = requests.get(f"{ZENODO_BASE}/deposit/depositions",
                     params={**_params(), "size": 100, "status": status})
    r.raise_for_status()
    return r.json()


def create_deposition(metadata: dict) -> dict:
    r = requests.post(f"{ZENODO_BASE}/deposit/depositions",
                      params=_params(),
                      headers=ZENODO_HEADERS,
                      data=json.dumps({"metadata": metadata}))
    r.raise_for_status()
    return r.json()


def upload_file(dep_id: int, filepath: Path) -> dict:
    bucket_url = get_bucket_url(dep_id)
    with open(filepath, "rb") as f:
        r = requests.put(f"{bucket_url}/{filepath.name}",
                         params=_params(), data=f)
    r.raise_for_status()
    return r.json()


def get_bucket_url(dep_id: int) -> str:
    r = requests.get(f"{ZENODO_BASE}/deposit/depositions/{dep_id}",
                     params=_params())
    r.raise_for_status()
    return r.json()["links"]["bucket"]


def publish_deposition(dep_id: int) -> dict:
    r = requests.post(f"{ZENODO_BASE}/deposit/depositions/{dep_id}/actions/publish",
                      params=_params())
    r.raise_for_status()
    return r.json()


def create_new_version(dep_id: int) -> dict:
    """Create a new draft version of an existing published record."""
    r = requests.post(
        f"{ZENODO_BASE}/deposit/depositions/{dep_id}/actions/newversion",
        params=_params())
    r.raise_for_status()
    latest_draft_url = r.json()["links"]["latest_draft"]
    new_id = int(latest_draft_url.rstrip("/").split("/")[-1])
    return {"new_id": new_id, "url": latest_draft_url}


def delete_deposition_files(dep_id: int):
    """Delete all existing files from a draft (for clean re-upload)."""
    r = requests.get(f"{ZENODO_BASE}/deposit/depositions/{dep_id}",
                     params=_params())
    files = r.json().get("files", [])
    for f in files:
        requests.delete(
            f"{ZENODO_BASE}/deposit/depositions/{dep_id}/files/{f['id']}",
            params=_params())


def update_metadata(dep_id: int, metadata: dict) -> dict:
    r = requests.put(f"{ZENODO_BASE}/deposit/depositions/{dep_id}",
                     params=_params(),
                     headers=ZENODO_HEADERS,
                     data=json.dumps({"metadata": metadata}))
    r.raise_for_status()
    return r.json()


# ── Metadata Builder ──────────────────────────────────────────────────────────

def build_metadata(title: str, description: str, extra_keywords=None) -> dict:
    keywords = list(COMMUNITY_KEYWORDS)
    if extra_keywords:
        keywords = list(set(keywords + extra_keywords))
    return {
        "title": title,
        "description": description,
        "upload_type": "publication",
        "publication_type": "preprint",
        "publication_date": datetime.now().strftime("%Y-%m-%d"),
        "creators": [AUTHOR_META],
        "keywords": keywords,
        "license": "cc-by-4.0",
        "access_right": "open",
        "language": "eng",
        "notes": "Part of the TI Sigma Universal Reality Blueprint (URB) Corpus. "
                 "Tralse Informationalism officially coined June 25, 2025."
    }


def extract_title_and_desc(md_path: Path):
    """Extract title (first H1) and abstract (first paragraph after title) from markdown."""
    text = md_path.read_text(encoding="utf-8")
    lines = text.splitlines()
    title = md_path.stem.replace("_", " ").title()
    desc = "A TI Sigma research paper by Brandon Charles Emerick."

    for i, line in enumerate(lines):
        if line.startswith("# "):
            title = line[2:].strip()
        elif line.startswith("## Abstract"):
            # grab next non-empty paragraph
            for j in range(i+1, min(i+10, len(lines))):
                if lines[j].strip():
                    desc = lines[j].strip()
                    break
            break
        elif i > 0 and line.strip() and not line.startswith("#") and not line.startswith("**"):
            if len(line.strip()) > 40:
                desc = line.strip()[:500]
                break
    return title, desc


# ── Priority Paper Queue ──────────────────────────────────────────────────────

PRIORITY_BATCH_1 = [
    # Latest URBs (#505–#508) — brand new theory
    "URB_TF_LCC_UNIFIED_TELEKINESIS_505.md",
    "URB_I_COMPLETENESS_THEOREM_506.md",
    "URB_MINIMAL_OPERATIONS_507.md",
    "URB_BENGSTON_WATER_QUARTZ_508.md",
    # Core theoretical foundations
    "BOK_CLOSURE_THEOREM.md",
    "LOVE_GENESIS_THEOREM.md",
    "LOVE_PRIMACY_THEOREM.md",
    "MAHARISHI_I_THRESHOLD.md",
    "ONTOGENY_RECAPITULATES_COSMOGONY.md",
    # Financial / Hull Tactical
    "GRAND_STOCK_ALGORITHM_V2.md",
    "HULL_TACTICAL_COMPETITION_STRATEGY.md",
    # Consciousness & PSI
    "GRAND_PSI_PROOF.md",
    "A_PRIORI_CONSCIOUSNESS_PROOF_EMPIRICAL_BRIDGE.md",
    "AFTERLIFE_MECHANISM_LCC_THRESHOLD_THEORY.md",
    # Patent-safe theoretical papers
    "AGI_IMPOSSIBILITY_TI_SIGMA_PROOF.md",
    "APERIODIC_DUAL_LxE_LpE_EINSTEIN_TILING.md",
    "ANTI_GILE_ONTOLOGICAL_HOLES.md",
    "AUTISM_DECONSTRUCTION_DIMENSIONAL_FRAMEWORK.md",
    "VERISYN_EQUATION_BOK_PRIMORDIAL_ANALYSIS.md",
    "YOGIC_ENERGY_OPERATIONAL_DEFINITION.md",
    "WHOLE_BODY_CHAKRA_PHYSICS_BLISS_ACTIVATION.md",
    "WHAT_ARE_EMOTIONS_MIM_GEOMETRY_PHENOMENALITY.md",
    "ALARM_FREE_LUCID_DREAM_LCC_ACETYLCHOLINE.md",
    "AMERICAN_PHASE_TRANSITION_TI_ANALYSIS.md",
]


def get_all_urb_mds(limit=None):
    """Return all URB markdown files sorted by URB number."""
    urb_files = sorted(PAPERS_DIR.glob("URB_*.md"),
                       key=lambda p: int(re.search(r"(\d+)", p.stem).group(1))
                       if re.search(r"(\d+)", p.stem) else 0)
    return urb_files[:limit] if limit else urb_files


def get_priority_queue():
    """Return priority batch 1 paths that exist."""
    queue = []
    for fname in PRIORITY_BATCH_1:
        p = PAPERS_DIR / fname
        if p.exists():
            queue.append(p)
    return queue


# ── Single Paper Upload ───────────────────────────────────────────────────────

def upload_paper(md_path: Path, batch_num: int = 0, use_existing_pdf: bool = True) -> dict:
    """Full upload flow: metadata → create → upload PDF → publish."""
    fname = md_path.name
    title, desc = extract_title_and_desc(md_path)
    meta = build_metadata(title, desc)

    # Find or generate PDF
    pdf_path = md_path.with_suffix(".pdf")
    if not pdf_path.exists() or not use_existing_pdf:
        ok = md_to_pdf(md_path, pdf_path)
        if not ok:
            return {"status": "error", "reason": "PDF generation failed"}

    try:
        dep = create_deposition(meta)
        dep_id = dep["id"]
        upload_file(dep_id, pdf_path)
        # Also upload the raw markdown as a supplementary file
        upload_file(dep_id, md_path)
        result = publish_deposition(dep_id)
        doi = result.get("doi", "")
        mark_uploaded(fname, title, dep_id, doi, batch_num)
        return {"status": "ok", "dep_id": dep_id, "doi": doi, "title": title}
    except Exception as e:
        err = str(e)
        mark_failed(fname, err)
        return {"status": "error", "reason": err}


# ── New Version of Existing Record ───────────────────────────────────────────

def update_existing_record(dep_id: int, new_files: list, new_meta: dict = None) -> dict:
    """Create a new version of an existing published record, replace files, publish."""
    try:
        nv = create_new_version(dep_id)
        new_id = nv["new_id"]

        # Clear old files from the new draft
        delete_deposition_files(new_id)

        # Upload new files
        for fp in new_files:
            if isinstance(fp, str):
                fp = Path(fp)
            if fp.exists():
                upload_file(new_id, fp)

        # Update metadata if provided
        if new_meta:
            update_metadata(new_id, new_meta)

        result = publish_deposition(new_id)
        return {"status": "ok", "new_id": new_id, "doi": result.get("doi", "")}
    except Exception as e:
        return {"status": "error", "reason": str(e)}


# ── Batch Upload ──────────────────────────────────────────────────────────────

def run_batch(papers: list, batch_num: int, max_per_run: int = 10,
              progress_callback=None) -> dict:
    """Upload up to max_per_run papers from the list. Returns summary."""
    already = get_already_uploaded()
    todo = [p for p in papers if Path(p).name not in already][:max_per_run]

    results = {"uploaded": [], "failed": [], "skipped": len(papers) - len(todo) - max(0, len(todo) - max_per_run)}
    for i, paper in enumerate(todo):
        paper = Path(paper)
        if progress_callback:
            progress_callback(i + 1, len(todo), paper.name)
        r = upload_paper(paper, batch_num=batch_num)
        if r["status"] == "ok":
            results["uploaded"].append({"file": paper.name, "doi": r.get("doi"), "title": r.get("title")})
        else:
            results["failed"].append({"file": paper.name, "reason": r.get("reason")})
        time.sleep(0.5)  # be polite to the API

    return results


# ── Stats ─────────────────────────────────────────────────────────────────────

def get_stats():
    """Return summary statistics for the dashboard."""
    rows = get_upload_status()
    total_papers = len(list(PAPERS_DIR.glob("*.md"))) + len(list(PAPERS_DIR.glob("*.pdf")))
    published = sum(1 for r in rows if r[4] == "published")
    failed    = sum(1 for r in rows if r[4] == "failed")
    pending   = total_papers - published
    return {
        "total_local": total_papers,
        "published": published,
        "failed": failed,
        "pending": pending,
        "live_records": 4,  # known published with DOI
        "corpus_urbs": 163
    }
