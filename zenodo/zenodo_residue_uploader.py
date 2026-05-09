"""
TI Sigma Zenodo RESIDUE uploader (Pass 17, f16 directive).

Closes the 200-vs-900 gap (actual: 891 papers in papers/ NOT covered
by zenodo/topic_manifest.py). Bundles the residue into ~18 alphabetical
ZIP-style draft records, all access=closed (PRIVATE), so Brandon can
review per-bundle and selectively publish or delete. Default mode is
DRAFT so nothing goes public without Brandon's UI click.

USAGE:
  python zenodo/zenodo_residue_uploader.py --plan       # show plan only
  python zenodo/zenodo_residue_uploader.py --execute    # actually upload

Per #69:
  - All bundles default to access='closed' (PRIVATE). Brandon edits
    individual records in the Zenodo UI to publish or change access.
  - Bundles are alphabetical to minimize coupling to topic-judgments
    Brandon hasn't made yet. A Pass-18 follow-on could re-bundle by
    topic-clustering once Brandon picks themes.
  - Per-record file count is capped at MAX_FILES_PER_RECORD (default
    60); large alphabetical buckets get split into A1, A2, ...
  - Already-manifested papers are EXCLUDED to avoid duplicates with
    the existing 15 records from Pass 16.
  - Each bundle's description prints the file list; Brandon sees what's
    inside before deciding to publish.
"""
import argparse, json, os, sys, time
from pathlib import Path

import requests

BASE_DIR = Path(__file__).parent.parent
PAPERS_DIR = BASE_DIR / "papers"
LOG_PATH = BASE_DIR / "zenodo" / "residue_upload_log.json"

SANDBOX = os.environ.get("ZENODO_SANDBOX", "").lower() == "true"
BASE_URL = "https://sandbox.zenodo.org" if SANDBOX else "https://zenodo.org"
TOKEN = os.environ.get("ZENODO_TOKEN", "")

MAX_FILES_PER_RECORD = 60

sys.path.insert(0, str(Path(__file__).parent))
from topic_manifest import TOPICS, CREATOR, COMMON_KEYWORDS  # type: ignore

ALREADY_MANIFESTED = set()
for t in TOPICS:
    for f in t.get("files", []):
        ALREADY_MANIFESTED.add(Path(f).name)


def collect_residue():
    all_md = sorted(p.name for p in PAPERS_DIR.glob("*.md"))
    return [p for p in all_md if p not in ALREADY_MANIFESTED]


def build_bundles(files):
    """Group files alphabetically into bundles of <= MAX_FILES_PER_RECORD."""
    bundles = []
    current_letter = None
    current = []
    for f in files:
        letter = f[0].upper() if f and f[0].isalpha() else "_"
        if letter != current_letter:
            if current:
                bundles.append((current_letter, current))
            current_letter = letter
            current = [f]
        else:
            current.append(f)
    if current:
        bundles.append((current_letter, current))

    # Split any oversize bundles
    final = []
    for letter, group in bundles:
        if len(group) <= MAX_FILES_PER_RECORD:
            final.append((letter, "", group))
        else:
            for i in range(0, len(group), MAX_FILES_PER_RECORD):
                sub = group[i:i + MAX_FILES_PER_RECORD]
                tag = f"{i//MAX_FILES_PER_RECORD + 1}"
                final.append((letter, tag, sub))
    return final


def api(method, endpoint, **kw):
    url = f"{BASE_URL}/api/{endpoint}"
    params = kw.pop("params", {}); params["access_token"] = TOKEN
    return getattr(requests, method)(url, params=params, **kw)


def create_deposition():
    r = api("post", "deposit/depositions", json={})
    r.raise_for_status(); return r.json()


def upload_file(bucket_url, filename, filepath):
    with open(filepath, "rb") as fh:
        r = requests.put(f"{bucket_url}/{filename}", data=fh,
                         params={"access_token": TOKEN})
    r.raise_for_status(); return r.json()


def set_meta(dep_id, title, file_list, letter, tag):
    desc = (
        f"<p>TI Sigma residue bundle (Pass 17 f16 close-the-gap upload). "
        f"Alphabetical bundle: <strong>{letter}{('-' + tag) if tag else ''}</strong>, "
        f"{len(file_list)} files. This is a DRAFT in CLOSED access — Brandon "
        f"reviews per-bundle and selectively publishes/deletes via Zenodo UI. "
        f"Files included:</p><ul>"
        + "".join(f"<li><code>{f}</code></li>" for f in file_list[:60])
        + "</ul>"
    )
    body = {
        "title": title,
        "upload_type": "publication",
        "publication_type": "other",
        "description": desc,
        "creators": CREATOR,
        "keywords": COMMON_KEYWORDS + ["residue bundle", f"alphabetical-{letter}"],
        "communities": [{"identifier": "ti-sigma"}],
        "license": "cc-by-4.0",
        "access_right": "closed",
        "journal_title": "TI Sigma Research Series — Residue",
    }
    r = api("put", f"deposit/depositions/{dep_id}", json={"metadata": body})
    r.raise_for_status(); return r.json()


def upload_one_bundle(letter, tag, files, idx, n_total):
    title = f"TI Sigma Residue Bundle {letter}{('-' + tag) if tag else ''} ({len(files)} papers)"
    print(f"\n[{idx+1}/{n_total}] {title}")
    print(f"  Files: {len(files)} (first: {files[0][:60]} ; last: {files[-1][:60]})")
    if not TOKEN:
        print("  NO ZENODO_TOKEN — would fail; skipping."); return None
    dep = create_deposition()
    dep_id = dep["id"]; bucket = dep["links"]["bucket"]
    print(f"  Deposition ID: {dep_id}")
    uploaded = 0
    for f in files:
        path = PAPERS_DIR / f
        if not path.exists():
            print(f"  MISSING {f}"); continue
        try:
            upload_file(bucket, f, path); uploaded += 1
        except Exception as e:
            print(f"  upload err {f}: {e}")
    print(f"  Uploaded {uploaded}/{len(files)} files")
    try: set_meta(dep_id, title, files, letter, tag)
    except Exception as e: print(f"  metadata err: {e}")
    print(f"  Draft URL: {BASE_URL}/deposit/{dep_id}")
    return {"id": dep_id, "url": f"{BASE_URL}/deposit/{dep_id}",
            "title": title, "letter": letter, "tag": tag,
            "n_files": uploaded}


def main():
    p = argparse.ArgumentParser()
    p.add_argument("--plan", action="store_true", help="Show plan only")
    p.add_argument("--execute", action="store_true", help="Actually upload")
    p.add_argument("--limit", type=int, default=0, help="Stop after N bundles")
    a = p.parse_args()
    if not (a.plan or a.execute):
        a.plan = True

    residue = collect_residue()
    bundles = build_bundles(residue)
    print("=" * 70)
    print(f"Zenodo RESIDUE uploader (Pass 17 f16)")
    print("=" * 70)
    print(f"Total papers/*.md: {len(list(PAPERS_DIR.glob('*.md')))}")
    print(f"Already manifested (Pass 16): {len(ALREADY_MANIFESTED)}")
    print(f"Residue (to upload): {len(residue)}")
    print(f"Bundles: {len(bundles)}  (max {MAX_FILES_PER_RECORD} files each)")
    print(f"Mode: {'DRY-PLAN ONLY' if a.plan else 'EXECUTE'}")
    print()
    print(f"{'idx':>3}  {'letter':>6}  {'tag':>4}  {'files':>5}  first")
    for i, (letter, tag, files) in enumerate(bundles):
        print(f"{i:>3}  {letter:>6}  {tag:>4}  {len(files):>5}  {files[0][:60]}")
    if a.plan:
        print("\nDry-plan only. Re-run with --execute to actually upload.")
        return

    if not TOKEN:
        print("\nNO ZENODO_TOKEN env var — cannot execute."); return
    out = []
    if LOG_PATH.exists():
        out = json.loads(LOG_PATH.read_text())
    n_to_run = a.limit if a.limit > 0 else len(bundles)
    print(f"\nExecuting {n_to_run} bundles in CLOSED-DRAFT mode...")
    for i, (letter, tag, files) in enumerate(bundles[:n_to_run]):
        rec = upload_one_bundle(letter, tag, files, i, n_to_run)
        if rec: out.append(rec); LOG_PATH.write_text(json.dumps(out, indent=2))
        time.sleep(1.5)  # gentle pacing for Zenodo API
    print(f"\nDONE. Log: {LOG_PATH}")


if __name__ == "__main__":
    main()
