"""
TI Sigma — Zenodo Bulk Uploader (Topic Edition)
Creates one Zenodo record per topic, with multiple paper files per record.
Privacy tiers: open | restricted | closed

SETUP:
  1. zenodo.org → Account → Applications → Personal access tokens
     Scopes: deposit:write  deposit:actions
  2. Add to Replit secrets:  ZENODO_TOKEN = <your token>
  3. Preview:  python3 zenodo/zenodo_bulk_uploader.py --dry-run
  4. Upload:   python3 zenodo/zenodo_bulk_uploader.py
  5. Review drafts at zenodo.org/me/uploads, then publish each one.

Flags:
  --dry-run          Preview without creating any records
  --sandbox          Use sandbox.zenodo.org (safe testing)
  --tier open        Only upload public (open) entries
  --tier restricted  Only upload restricted entries
  --tier closed      Only upload private (closed) entries
  --topics N [N...]  Upload only specific topic indices (0-based)
"""

import os, sys, json, time, requests, argparse
from pathlib import Path

# ── config ────────────────────────────────────────────────────────────────────
BASE_DIR = Path(__file__).parent.parent
SANDBOX  = os.environ.get("ZENODO_SANDBOX", "").lower() == "true"
BASE_URL = "https://sandbox.zenodo.org" if SANDBOX else "https://zenodo.org"
TOKEN    = os.environ.get("ZENODO_TOKEN", "")

# ── load manifest ─────────────────────────────────────────────────────────────
sys.path.insert(0, str(Path(__file__).parent))
from topic_manifest import TOPICS, CREATOR, COMMON_KEYWORDS

# ── access-right labels for display ──────────────────────────────────────────
ACCESS_LABEL = {"open": "PUBLIC", "restricted": "RESTRICTED", "closed": "PRIVATE"}

# ── zenodo api helpers ────────────────────────────────────────────────────────
def api(method, endpoint, **kwargs):
    url    = f"{BASE_URL}/api/{endpoint}"
    params = kwargs.pop("params", {})
    params["access_token"] = TOKEN
    r = getattr(requests, method)(url, params=params, **kwargs)
    return r

def create_deposition():
    r = api("post", "deposit/depositions", json={})
    r.raise_for_status()
    return r.json()

def upload_file(bucket_url, filename, filepath):
    with open(filepath, "rb") as fh:
        r = requests.put(f"{bucket_url}/{filename}",
                         data=fh, params={"access_token": TOKEN})
    r.raise_for_status()
    return r.json()

def set_metadata(dep_id, topic):
    keywords  = list(dict.fromkeys(topic.get("keywords", []) + COMMON_KEYWORDS))
    access    = topic.get("access", "open")
    meta_body = {
        "title":            topic["title"],
        "upload_type":      topic.get("type", "publication"),
        "publication_type": topic.get("subtype", "article"),
        "description":      topic["description"],
        "creators":         CREATOR,
        "keywords":         keywords,
        "journal_title":    "TI Sigma Research Series",
        "communities":      [{"identifier": "ti-sigma"}],
        "license":          "cc-by-4.0",
        "access_right":     access,
    }
    if access == "embargoed":
        meta_body["embargo_date"] = topic.get("embargoed_date", "2027-01-01")

    r = api("put", f"deposit/depositions/{dep_id}", json={"metadata": meta_body})
    r.raise_for_status()
    return r.json()

# ── per-topic upload ──────────────────────────────────────────────────────────
def upload_topic(topic, dry_run=False):
    access  = topic.get("access", "open")
    label   = ACCESS_LABEL.get(access, access.upper())
    files   = topic.get("files", [])
    present = [f for f in files if (BASE_DIR / f).exists()]
    missing = [f for f in files if not (BASE_DIR / f).exists()]

    print(f"\n  [{label}] {topic['title'][:65]}...")
    print(f"  Files: {len(present)} found, {len(missing)} missing")
    for m in missing:
        print(f"    MISSING: {m}")

    if not present:
        print("  [SKIP] No files available.")
        return None

    if dry_run:
        print(f"  [DRY RUN] Would create {label} draft at {BASE_URL}")
        return {"url": f"{BASE_URL}/me/uploads (dry run)",
                "title": topic["title"], "access": label,
                "files": [Path(f).name for f in present]}

    dep    = create_deposition()
    dep_id = dep["id"]
    bucket = dep["links"]["bucket"]
    print(f"  Deposition ID: {dep_id}")

    for filepath in present:
        p = BASE_DIR / filepath
        upload_file(bucket, p.name, p)
        print(f"  Uploaded: {p.name}")

    set_metadata(dep_id, topic)
    url = f"{BASE_URL}/deposit/{dep_id}"
    print(f"  Draft URL: {url}")
    return {"id": dep_id, "url": url, "title": topic["title"],
            "access": label, "files": [Path(f).name for f in present]}

# ── main ─────────────────────────────────────────────────────────────────────
def run(dry_run=False, tier_filter=None, topic_indices=None):
    if not dry_run and not TOKEN:
        print("ERROR: ZENODO_TOKEN not set.")
        print("  Steps:")
        print("  1. zenodo.org → Account → Applications → Personal access tokens")
        print("  2. New token, scopes: deposit:write + deposit:actions")
        print("  3. Add to Replit secrets as ZENODO_TOKEN")
        print("  Run with --dry-run to preview without a token.")
        sys.exit(1)

    mode   = "SANDBOX" if SANDBOX else "PRODUCTION"
    action = "DRY RUN" if dry_run else f"LIVE on {BASE_URL}"

    # apply filters
    topics_to_run = TOPICS
    if topic_indices:
        topics_to_run = [TOPICS[i] for i in topic_indices]
    if tier_filter:
        topics_to_run = [t for t in topics_to_run
                         if t.get("access", "open") == tier_filter]

    print(f"\nTI Sigma Zenodo Bulk Uploader — Topic Edition")
    print(f"Mode: {mode} | Action: {action}")
    print(f"Topics: {len(topics_to_run)} to process")
    if tier_filter:
        print(f"Filter: {ACCESS_LABEL.get(tier_filter, tier_filter)} only")
    print("=" * 65)

    # summary table before starting
    print(f"\n{'#':>3}  {'ACCESS':>12}  {'FILES':>6}  TITLE")
    for i, t in enumerate(topics_to_run):
        label  = ACCESS_LABEL.get(t.get("access","open"), "?")
        nfiles = len(t.get("files", []))
        print(f"{i:>3}  {label:>12}  {nfiles:>6}  {t['title'][:55]}")
    print()

    results = []
    for i, topic in enumerate(topics_to_run, 1):
        print(f"[{i}/{len(topics_to_run)}]")
        try:
            r = upload_topic(topic, dry_run=dry_run)
            if r:
                results.append(r)
        except requests.HTTPError as e:
            print(f"  [HTTP ERROR] {e.response.status_code}: {e.response.text[:200]}")
        except Exception as e:
            print(f"  [ERROR] {e}")

        if not dry_run and i < len(topics_to_run):
            time.sleep(1.5)      # be kind to the API

    # ── results summary ───────────────────────────────────────────
    print("\n" + "=" * 65)
    print(f"DONE: {len(results)}/{len(topics_to_run)} topics processed\n")

    by_access = {"PUBLIC": [], "RESTRICTED": [], "PRIVATE": []}
    for r in results:
        by_access.get(r["access"], by_access["PUBLIC"]).append(r)

    for tier, items in by_access.items():
        if not items:
            continue
        print(f"── {tier} ({len(items)}) ──")
        for r in items:
            print(f"  {r['url']}")
            print(f"    {r['title'][:60]}")
            print(f"    Files: {', '.join(r['files'][:3])}"
                  + ("..." if len(r["files"]) > 3 else ""))

    log = BASE_DIR / "zenodo" / "upload_log.json"
    with open(log, "w") as f:
        json.dump(results, f, indent=2)
    print(f"\nLog: {log}")

    if not dry_run:
        print(f"\nNext steps:")
        print(f"  1. Review all drafts: {BASE_URL}/me/uploads")
        print(f"  2. For PUBLIC entries: verify content, click Publish")
        print(f"  3. For RESTRICTED: add an access password or contact form")
        print(f"  4. For PRIVATE (closed): do NOT publish — they stay draft")
        print(f"  5. Create community if not done: {BASE_URL}/communities/new")
        print(f"     Identifier: ti-sigma")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="TI Sigma Zenodo Bulk Uploader")
    parser.add_argument("--dry-run",  action="store_true",
                        help="Preview without creating any records")
    parser.add_argument("--sandbox",  action="store_true",
                        help="Use sandbox.zenodo.org")
    parser.add_argument("--tier",     choices=["open", "restricted", "closed"],
                        help="Upload only one privacy tier")
    parser.add_argument("--topics",   nargs="+", type=int, metavar="N",
                        help="Upload only specific indices, e.g. --topics 0 1 3")
    args = parser.parse_args()

    if args.sandbox:
        os.environ["ZENODO_SANDBOX"] = "true"
        SANDBOX  = True
        BASE_URL = "https://sandbox.zenodo.org"

    run(dry_run=args.dry_run, tier_filter=args.tier, topic_indices=args.topics)
