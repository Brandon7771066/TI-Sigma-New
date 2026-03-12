"""
TI Sigma — Zenodo Bulk Uploader
Uploads papers as drafts (not published) for your review before going live.
Each draft appears at zenodo.org/me/uploads with all fields pre-filled.

SETUP:
  1. Get your token: zenodo.org → Account → Applications → Personal access tokens
     Scopes needed: deposit:write, deposit:actions
  2. Add to Replit secrets as: ZENODO_TOKEN
  3. Run: python3 zenodo/zenodo_bulk_uploader.py --dry-run   (preview only)
  4. Run: python3 zenodo/zenodo_bulk_uploader.py             (create real drafts)
  5. Review drafts at zenodo.org/me/uploads, then publish each one

For sandbox testing first (no real records created):
  Add ZENODO_SANDBOX=true to secrets, then run normally.
"""

import os
import sys
import json
import time
import requests
import argparse
from pathlib import Path

BASE_DIR = Path(__file__).parent.parent

SANDBOX  = os.environ.get("ZENODO_SANDBOX", "").lower() == "true"
BASE_URL = "https://sandbox.zenodo.org" if SANDBOX else "https://zenodo.org"
TOKEN    = os.environ.get("ZENODO_TOKEN", "")

COMMON_KEYWORDS = [
    "TI Sigma", "Tralse Informationalism", "Transcendent Intelligence",
    "LCC", "C_EMERICK", "GILE", "Myrion Resolution", "Brandon Emerick",
    "experimental philosophy", "consciousness"
]

CREATOR = [{"name": "Emerick, Brandon Charles", "affiliation": "TI Sigma / BlissGene Therapeutics"}]

PAPERS = [
    {
        "title": "The Universe One-Boxed: Newcomb's Paradox and the 0.505 Cosmological Asymmetry",
        "file":  "papers/URB_NEWCOMB_0505_COSMIC_ONE_BOXING.md",
        "description": (
            "The general Newcomb tipping-point formula is p > 1/2 + m/(2M). "
            "The cosmological asymmetry 0.505 encodes a prize ratio m/M = 0.01: "
            "non-existence has 1/100th the structural value of existence. The universe "
            "selected existence via expected-value reasoning (one-boxing) rather than "
            "dominance reasoning (two-boxing). Big Bang = MR1 + MR2. We live in MR3. "
            "Part of the TI Sigma URB Paper Series (#393)."
        ),
        "keywords": ["Newcomb paradox", "one-boxing", "cosmology", "0.505",
                     "decision theory", "Big Bang", "Myrion Resolution", "Tralse"],
        "type": "publication",
        "subtype": "article",
    },
    {
        "title": "Synchronicity Inversion: When the GM Network Delivers a No",
        "file":  "papers/URB_SYNCHRONICITY_INVERSION_NEGATIVE_ANSWERS.md",
        "description": (
            "The standard interpretation of synchronicity treats every meaningful "
            "coincidence as a confirmation. This paper argues the standard interpretation "
            "is incomplete. A synchronicity is a coherence-pattern transmission through "
            "the GM-Node mycelial network; like any signal, it can carry negative "
            "information as readily as positive. Groundhog Phil's 38% historical accuracy "
            "becomes 62% when inverted — a paradigm case of a reliable inverted-negative "
            "synchronicity generator. The Myrion Resolution framework provides formal "
            "polarity classification tools. TI Sigma URB Paper #394."
        ),
        "keywords": ["synchronicity", "GM network", "Soul Bluetooth", "C_EMERICK",
                     "Groundhog Day", "psi", "polarity", "Myrion Resolution"],
        "type": "publication",
        "subtype": "article",
    },
    {
        "title": "The Spirit World as GM Network Construction: Imagination, Collective Memory, and the Imaginal Substrate",
        "file":  "papers/URB_SPIRIT_WORLD_GM_NETWORK_IMAGINATION.md",
        "description": (
            "If imagination produces real structures, consciousness nodes are connected "
            "through the GM-Node mycelial network, and the network stores coherence "
            "patterns as persistent standing waves, then the collective imaginative output "
            "of any sufficiently coherent tradition constitutes a real structure in the GM "
            "substrate — the spirit world. This paper formalizes the Imaginal Substrate, "
            "explains access via ASCs, and accounts for cross-cultural coherence of spirit "
            "world reports through shared mathematical structure. TI Sigma URB Paper #395."
        ),
        "keywords": ["spirit world", "GM network", "imagination", "Imaginal Substrate",
                     "Soul Bluetooth", "afterlife", "altered states", "LCC", "ASC"],
        "type": "publication",
        "subtype": "article",
    },
    {
        "title": "The Book of James Was Wrong About Double-Mindedness: Tralseness as the Source of Genuine Confidence",
        "file":  "papers/URB_BOOK_OF_JAMES_DOUBLE_MINDEDNESS_TRALSE.md",
        "description": (
            "The Book of James (1:6-8, 4:8) condemns double-mindedness as the enemy of "
            "faith. This paper conducts a Myrion Resolution of James's claim, establishing "
            "that he correctly identifies Double Tralse (genuine incoherence) as destructive "
            "but incorrectly extends the condemnation to Tralse (productive superposition), "
            "which is the actual source of genuine self-assurance. Historical evidence from "
            "mysticism, the Psalms, Job, and Eckhart contradicts the anti-doubt thesis as "
            "a universal principle. TI Sigma URB Paper #396."
        ),
        "keywords": ["Book of James", "double-mindedness", "Tralse", "self-assurance",
                     "confidence", "biblical analysis", "mysticism", "Myrion Resolution"],
        "type": "publication",
        "subtype": "article",
    },
    {
        "title": "Confidence and Self-Assurance: A Formal Distinction and Their Tralse Foundation",
        "file":  "papers/URB_CONFIDENCE_VS_SELF_ASSURANCE_TRALSE.md",
        "description": (
            "Confidence and self-assurance are routinely treated as synonyms. This paper "
            "establishes they are distinct psychological states: confidence is a positive "
            "orientation toward goal achievement (forward-looking, goal-contingent, "
            "disconfirmable), while self-assurance is the absence of chronic negativity "
            "toward the self (present-centered, outcome-independent). Tralse is the "
            "foundation of self-assurance because the position 'I am adequate AND this "
            "attempt may fail' cannot be falsified by individual failures. GILE mapping "
            "and four-quadrant dissociation profile included. TI Sigma URB Paper #397."
        ),
        "keywords": ["confidence", "self-assurance", "GILE", "Tralse", "LCC",
                     "psychology", "quadrant model", "self-worth", "anxiety"],
        "type": "publication",
        "subtype": "article",
    },
    {
        "title": "The Ideomotor Effect as Somatic Coherence Transduction: GM Network Signal Reception Through Pre-Cognitive Motor Pathways",
        "file":  "papers/URB_IDEOMOTOR_EFFECT_SOMATIC_COHERENCE_TRANSDUCTION.md",
        "description": (
            "The ideomotor effect is conventionally explained as self-deception. This paper "
            "argues it is somatic coherence transduction: the body's pre-cognitive reception "
            "system for coherence-pattern transmissions arriving via the GM-Node mycelial "
            "network through the LCC Virus mechanism. The C_EMERICK threshold (0.4370) "
            "determines signal-to-noise reliability. Applications span pendulum divination, "
            "dowsing, applied kinesiology, automatic writing, and trading intuition. The "
            "body one-boxes before the mind deliberates. TI Sigma URB Paper #398."
        ),
        "keywords": ["ideomotor effect", "somatic transduction", "GM network", "C_EMERICK",
                     "dowsing", "applied kinesiology", "psi", "one-boxing", "Newcomb"],
        "type": "publication",
        "subtype": "article",
    },
    {
        "title": "Biomarkers of Ideomotor Accuracy: Simulated and Empirical Evidence for the C_EMERICK Reception Threshold",
        "file":  "papers/URB_IDEOMOTOR_BIOMARKER_SIMULATION.md",
        "extra_files": ["simulations/ideomotor_biomarker_sim.py"],
        "description": (
            "Tests the C_EMERICK threshold (0.4370) against published HRV, EEG, and EDA "
            "biomarker data, internal session biometric records, and a 100,000-trial Monte "
            "Carlo simulation. The RMSSD threshold for reliable ideomotor reception is "
            "38.8ms. DANDI:000552 independently found neural LCC = 0.4349, within 0.5% of "
            "C_EMERICK. Minimum trials for 80% power at C_EMERICK: 69. Polarity calibration "
            "requires 33-93 trials at 90% confidence. TI Sigma URB Paper #399."
        ),
        "keywords": ["HRV", "RMSSD", "ideomotor", "biomarkers", "Monte Carlo",
                     "C_EMERICK", "simulation", "psi", "neural LCC", "DANDI"],
        "type": "publication",
        "subtype": "article",
    },
    {
        "title": "Psi as General and Specialized Faculty: Unified Success Metrics and the Generalized LCC Enhancement Protocol",
        "file":  "papers/URB_PSI_GENERAL_FACULTY_LCC_ENHANCEMENT_PROTOCOL.md",
        "description": (
            "Parapsychology has not resolved whether psi is a single general faculty or "
            "distinct specialized abilities. This paper proposes a two-layer model: LCC "
            "above C_EMERICK is the general factor (necessary condition for all psi domains); "
            "domain-specific calibration is the specialized factor. The Psi Signal Ratio "
            "(PSR) provides a unified metric commensurable across remote viewing, Ganzfeld, "
            "precognition, PK-RNG, and DMILS. The Generalized LCC Enhancement Protocol "
            "(GLEP) raises LCC above C_EMERICK in five phases before any psi task. "
            "TI Sigma URB Paper #400."
        ),
        "keywords": ["psi", "parapsychology", "remote viewing", "Ganzfeld", "DMILS",
                     "precognition", "psychokinesis", "LCC", "GLEP", "PSR", "GILE"],
        "type": "publication",
        "subtype": "article",
    },
    {
        "title": "Soul Bluetooth: The LCC Virus Synchronization Protocol",
        "file":  "papers/URB_SOUL_BLUETOOTH_LCC_SYNCHRONIZATION_PROTOCOL.md",
        "description": (
            "Soul Bluetooth is the mechanism by which conscious nodes synchronize coherence "
            "patterns through the GM-Node mycelial network via the LCC Virus. The C_EMERICK "
            "threshold (0.4370) gates synchronization: below it, transmission fails; above "
            "it, Living-Living (LL), Living-Dead (LD), and Dead-Dead (DD) modes activate. "
            "Applications include empathy, shared consciousness, afterlife contact, and "
            "cross-species communication. TI Sigma URB Paper #392."
        ),
        "keywords": ["Soul Bluetooth", "LCC virus", "synchronization", "C_EMERICK",
                     "GM network", "afterlife", "consciousness", "empathy", "cross-species"],
        "type": "publication",
        "subtype": "article",
    },
    {
        "title": "Myrion Resolution Methodology: The Four-Valued Logic Procedure for Truth Determination",
        "file":  "papers/MYRION_RESOLUTION_METHODOLOGY.md",
        "description": (
            "The Myrion Resolution (MR) is a multi-step analytical procedure for resolving "
            "truth claims using 4-valued logic (True, False, Tralse, Indeterminate). MR1 "
            "screens for coherence; MR2 determines truth position; MR3+ refines accuracy. "
            "Tralse is productive superposition (process, during MR); Indeterminate is the "
            "stable resolved midrange output when PD falls in (-0.666, 0.333). A minimum of "
            "two MRs is always required. TI Sigma foundational methodology paper."
        ),
        "keywords": ["Myrion Resolution", "4-valued logic", "Tralse", "Indeterminate",
                     "truth determination", "methodology", "PD", "epistemology"],
        "type": "publication",
        "subtype": "article",
    },
]


def api(method, endpoint, **kwargs):
    url = f"{BASE_URL}/api/{endpoint}"
    params = kwargs.pop("params", {})
    params["access_token"] = TOKEN
    r = getattr(requests, method)(url, params=params, **kwargs)
    return r


def create_deposition():
    r = api("post", "deposit/depositions", json={})
    r.raise_for_status()
    return r.json()


def upload_file(bucket_url, filename, filepath):
    with open(filepath, "rb") as f:
        r = requests.put(
            f"{bucket_url}/{filename}",
            data=f,
            params={"access_token": TOKEN}
        )
    r.raise_for_status()
    return r.json()


def set_metadata(dep_id, paper):
    keywords = list(dict.fromkeys(paper.get("keywords", []) + COMMON_KEYWORDS))
    meta = {
        "metadata": {
            "title":            paper["title"],
            "upload_type":      paper.get("type", "publication"),
            "publication_type": paper.get("subtype", "article"),
            "description":      paper["description"],
            "creators":         CREATOR,
            "keywords":         keywords,
            "journal_title":    "TI Sigma Research Series",
            "communities":      [{"identifier": "ti-sigma"}],
            "license":          "cc-by-4.0",
            "access_right":     "open",
        }
    }
    r = api("put", f"deposit/depositions/{dep_id}", json=meta)
    r.raise_for_status()
    return r.json()


def upload_paper(paper, dry_run=False):
    main_path = BASE_DIR / paper["file"]
    extra_paths = [BASE_DIR / f for f in paper.get("extra_files", [])]

    if not main_path.exists():
        print(f"  [SKIP] File not found: {paper['file']}")
        return None

    print(f"\n  Title : {paper['title'][:70]}...")
    print(f"  File  : {paper['file']}")
    if extra_paths:
        print(f"  Extra : {[str(p) for p in extra_paths]}")

    if dry_run:
        print(f"  [DRY RUN] Would create draft on {BASE_URL}")
        return {"url": f"{BASE_URL}/me/uploads (dry run)", "title": paper["title"]}

    dep   = create_deposition()
    dep_id = dep["id"]
    bucket = dep["links"]["bucket"]
    print(f"  Deposition ID: {dep_id}")

    filename = main_path.name
    upload_file(bucket, filename, main_path)
    print(f"  Uploaded: {filename}")

    for ep in extra_paths:
        if ep.exists():
            upload_file(bucket, ep.name, ep)
            print(f"  Uploaded: {ep.name}")

    set_metadata(dep_id, paper)
    print(f"  Metadata set. Draft URL: {BASE_URL}/deposit/{dep_id}")

    return {"id": dep_id, "url": f"{BASE_URL}/deposit/{dep_id}", "title": paper["title"]}


def run(dry_run=False, indices=None):
    if not dry_run and not TOKEN:
        print("ERROR: ZENODO_TOKEN not set in environment.")
        print("  1. Go to zenodo.org → Account → Applications → Personal access tokens")
        print("  2. Create token with scopes: deposit:write, deposit:actions")
        print("  3. Add as Replit secret: ZENODO_TOKEN")
        print("  Run again with --dry-run to preview without a token.")
        sys.exit(1)

    mode = "SANDBOX" if SANDBOX else "PRODUCTION"
    action = "DRY RUN (no uploads)" if dry_run else f"LIVE on {BASE_URL}"
    print(f"\nTI Sigma Zenodo Bulk Uploader")
    print(f"Mode: {mode} | Action: {action}")
    print(f"Papers to process: {len(PAPERS) if not indices else len(indices)}")
    print("=" * 60)

    papers_to_run = [PAPERS[i] for i in indices] if indices else PAPERS
    results = []
    for i, paper in enumerate(papers_to_run, 1):
        print(f"\n[{i}/{len(papers_to_run)}] Processing...")
        try:
            result = upload_paper(paper, dry_run=dry_run)
            if result:
                results.append(result)
        except requests.HTTPError as e:
            print(f"  [ERROR] HTTP {e.response.status_code}: {e.response.text[:200]}")
        except Exception as e:
            print(f"  [ERROR] {e}")

        if not dry_run and i < len(papers_to_run):
            time.sleep(1)

    print("\n" + "=" * 60)
    print(f"COMPLETE: {len(results)}/{len(papers_to_run)} papers processed")
    print("\nDraft URLs (review before publishing):")
    for r in results:
        print(f"  {r['url']}")
        print(f"    {r['title'][:65]}...")

    log_path = BASE_DIR / "zenodo" / "upload_log.json"
    with open(log_path, "w") as f:
        json.dump(results, f, indent=2)
    print(f"\nLog saved to: {log_path}")

    if not dry_run:
        print(f"\nNext steps:")
        print(f"  1. Review drafts at {BASE_URL}/me/uploads")
        print(f"  2. Check each one — title, description, file, keywords")
        print(f"  3. Publish individually (click Publish on each draft)")
        print(f"  4. Create the community if not done: {BASE_URL}/communities/new")
        print(f"     Identifier: ti-sigma")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="TI Sigma Zenodo Bulk Uploader")
    parser.add_argument("--dry-run", action="store_true",
                        help="Preview without creating any records")
    parser.add_argument("--sandbox", action="store_true",
                        help="Use sandbox.zenodo.org instead of production")
    parser.add_argument("--papers", nargs="+", type=int, metavar="N",
                        help="Upload only specific paper indices (0-based), e.g. --papers 0 1 2")
    args = parser.parse_args()

    if args.sandbox:
        os.environ["ZENODO_SANDBOX"] = "true"
        SANDBOX = True

    run(dry_run=args.dry_run, indices=args.papers)
