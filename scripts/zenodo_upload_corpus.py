#!/usr/bin/env python3
"""
Zenodo corpus upload — Pass 8 (2026-05-08).

Brandon directive: "Upload the entire Corpus to Zenodo."

Strategy: single deposit containing
  (a) PD_COMPLEX_PLANE_RECANONIZATION_PASS_8_2026-05-08.md  (Pass 8 primary publication)
  (b) TI_FOR_EVERYONE_COMPLETE_BOOK.md                       (primary book)
  (c) ti_sigma_corpus_2026-05-08.tar.gz                      (all 914 papers + analyses/)

Default mode: DRAFT (publish=false). Permanent DOI is irreversible —
Brandon must eyes-on the deposition record before greenlight by either
(a) clicking publish in the Zenodo UI on the draft, or
(b) re-running this script with --publish flag.

Usage:
    python scripts/zenodo_upload_corpus.py            # creates DRAFT, prints links
    python scripts/zenodo_upload_corpus.py --publish  # publishes the most-recent draft
    python scripts/zenodo_upload_corpus.py --sandbox  # use Zenodo sandbox (test env)
"""
import os
import sys
import json
import tarfile
import argparse
from pathlib import Path

import requests

REPO_ROOT = Path(__file__).resolve().parent.parent
TARBALL_NAME = "ti_sigma_corpus_2026-05-08.tar.gz"
TARBALL_PATH = REPO_ROOT / TARBALL_NAME
PRIMARY_PAPER = REPO_ROOT / "papers" / "PD_COMPLEX_PLANE_RECANONIZATION_PASS_8_2026-05-08.md"
PRIMARY_BOOK = REPO_ROOT / "papers" / "TI_FOR_EVERYONE_COMPLETE_BOOK.md"


def build_tarball():
    """Build a tarball of papers/ + analyses/ + hardware/."""
    if TARBALL_PATH.exists():
        print(f"[skip] {TARBALL_NAME} already exists ({TARBALL_PATH.stat().st_size / 1e6:.1f} MB)")
        return
    print(f"[tar] Building {TARBALL_NAME} ...")
    with tarfile.open(TARBALL_PATH, "w:gz") as tar:
        for sub in ("papers", "analyses", "hardware", "data"):
            p = REPO_ROOT / sub
            if p.exists():
                tar.add(p, arcname=sub)
        # also include the canonical replit.md as project README context
        if (REPO_ROOT / "replit.md").exists():
            tar.add(REPO_ROOT / "replit.md", arcname="replit.md")
    print(f"[tar] Built {TARBALL_NAME} ({TARBALL_PATH.stat().st_size / 1e6:.1f} MB)")


def metadata():
    return {
        "metadata": {
            "title": "Tralse Informationalism Sigma — Complete Corpus and TI For Everyone (May 2026)",
            "upload_type": "publication",
            "publication_type": "book",
            "description": (
                "Complete research corpus for Tralse Informationalism Sigma (TI Sigma), "
                "the Mood Amplifier Safety & Validation Platform, including: "
                "(a) PD Complex-Plane Recanonization (Pass 8, 2026-05-08) — single source of truth "
                "for the Permissibility Distribution / Double Tralse complex-plane geometry with "
                "threshold constants ±1, ±φ, ±e, ±π and the Emerick Crossover ±1/√2; "
                "(b) TI For Everyone — Complete Book (~10,690 lines, ~225,000 words) with canonical "
                "preface, body, glossary, and appendices A–F (Claim Audit); "
                "(c) full corpus tarball of 914 papers covering MR Truth Labels canonical ruling, "
                "Authority Axis (5th truth-axis), TI Sigma Crystal / TI Sigma Graph projection structure, "
                "Asymmetric Success-Failure Performance theory, GILE Framework foundations (Aug 2022), "
                "Mendi BLE Path B reverse-engineering, Polar H10 baseline data, Riemann zeros analyses, "
                "pharmacology validation (75-83% magnitude correctness, +8 pp margin over best linear baseline), "
                "Authority Axis (AA) operating principle, biographical cluster, and ~334 supporting PDFs.\n\n"
                "Status: pre-publication research corpus. High-stakes empirical claims are status-flagged "
                "in Appendix F (Claim Audit, May 2026) with VERIFIED / FRAMEWORK-INTERNAL / "
                "INTERNAL-PENDING-EXTERNAL-REPLICATION / PRELIMINARY classifications per the Asymmetric-Standards #69 "
                "honesty discipline."
            ),
            "creators": [
                {
                    "name": "Emerick, Brandon Charles",
                    "affiliation": "Independent Researcher",
                }
            ],
            "keywords": [
                "Tralse Informationalism",
                "Permissibility Distribution",
                "Double Tralse",
                "Mood Amplifier",
                "Authority Axis",
                "Myrion Resolution",
                "TI Sigma Crystal",
                "consciousness",
                "Riemann zeros",
                "Perfect Fifth",
                "Euler",
                "fine-structure constant",
                "GILE framework",
            ],
            "access_right": "open",
            "license": "cc-by-4.0",
            "language": "eng",
            "notes": (
                "Pass 8 deposit (2026-05-08). Default upload is DRAFT — see "
                "scripts/zenodo_upload_corpus.py for publish flow. Versioning intended: this is "
                "release 1 of N; subsequent passes will be uploaded as new versions via Zenodo's "
                "version-DOI mechanism."
            ),
        }
    }


def api_base(sandbox: bool) -> str:
    return "https://sandbox.zenodo.org/api" if sandbox else "https://zenodo.org/api"


def create_draft(token: str, sandbox: bool) -> dict:
    base = api_base(sandbox)
    print(f"[api] Creating draft deposition at {base} ...")
    r = requests.post(
        f"{base}/deposit/depositions",
        params={"access_token": token},
        json=metadata(),
        timeout=60,
    )
    if r.status_code not in (200, 201):
        print(f"[err] Create failed: {r.status_code}\n{r.text[:1000]}")
        sys.exit(1)
    dep = r.json()
    print(f"[api] Created draft id={dep['id']}  bucket={dep['links'].get('bucket')}")
    return dep


def upload_file(token: str, bucket_url: str, path: Path):
    print(f"[upl] {path.name} ({path.stat().st_size / 1e6:.1f} MB) -> bucket")
    with path.open("rb") as fh:
        r = requests.put(
            f"{bucket_url}/{path.name}",
            data=fh,
            params={"access_token": token},
            timeout=600,
        )
    if r.status_code not in (200, 201):
        print(f"[err] Upload failed: {r.status_code}\n{r.text[:500]}")
        sys.exit(1)
    print(f"[upl] {path.name} OK")


def publish(token: str, sandbox: bool, dep_id: int):
    base = api_base(sandbox)
    print(f"[api] Publishing deposition id={dep_id} ...")
    r = requests.post(
        f"{base}/deposit/depositions/{dep_id}/actions/publish",
        params={"access_token": token},
        timeout=60,
    )
    if r.status_code not in (200, 202):
        print(f"[err] Publish failed: {r.status_code}\n{r.text[:1000]}")
        sys.exit(1)
    pub = r.json()
    print(f"[api] PUBLISHED. DOI: {pub.get('doi')}  HTML: {pub['links'].get('html')}")
    return pub


def find_latest_draft(token: str, sandbox: bool):
    base = api_base(sandbox)
    r = requests.get(
        f"{base}/deposit/depositions",
        params={"access_token": token, "status": "draft", "size": 25, "sort": "mostrecent"},
        timeout=30,
    )
    if r.status_code != 200:
        print(f"[err] List drafts failed: {r.status_code}\n{r.text[:500]}")
        sys.exit(1)
    drafts = r.json()
    if not drafts:
        print("[err] No drafts found")
        sys.exit(1)
    return drafts[0]


def main():
    ap = argparse.ArgumentParser(description="Upload TI Sigma corpus to Zenodo")
    ap.add_argument("--publish", action="store_true", help="Publish most-recent draft (irreversible)")
    ap.add_argument("--sandbox", action="store_true", help="Use Zenodo sandbox (test env)")
    args = ap.parse_args()

    token = os.environ.get("ZENODO_TOKEN")
    if not token:
        print("ZENODO_TOKEN not set in environment", file=sys.stderr)
        sys.exit(2)

    if args.publish:
        dep = find_latest_draft(token, args.sandbox)
        publish(token, args.sandbox, dep["id"])
        return

    build_tarball()
    dep = create_draft(token, args.sandbox)
    bucket = dep["links"].get("bucket")
    if not bucket:
        print("[err] No bucket URL on draft; cannot upload files.", file=sys.stderr)
        sys.exit(1)

    for f in (PRIMARY_PAPER, PRIMARY_BOOK, TARBALL_PATH):
        if f.exists():
            upload_file(token, bucket, f)
        else:
            print(f"[warn] missing file (skipping): {f}")

    out = {
        "deposition_id": dep["id"],
        "html": dep["links"].get("html"),
        "self": dep["links"].get("self"),
        "publish_url": dep["links"].get("publish"),
        "discard_url": dep["links"].get("discard"),
        "doi_reserved": dep.get("metadata", {}).get("prereserve_doi"),
        "files_uploaded": [PRIMARY_PAPER.name, PRIMARY_BOOK.name, TARBALL_NAME],
    }
    out_path = REPO_ROOT / "zenodo_deposit_dryrun" / "pass_8_draft_record.json"
    out_path.parent.mkdir(exist_ok=True)
    out_path.write_text(json.dumps(out, indent=2))
    print(f"\n[ok] DRAFT created. Record: {out_path}")
    print(f"[ok] Review draft in browser: {out['html']}")
    print(f"[ok] To publish: python scripts/zenodo_upload_corpus.py --publish"
          + ("  --sandbox" if args.sandbox else ""))


if __name__ == "__main__":
    main()
