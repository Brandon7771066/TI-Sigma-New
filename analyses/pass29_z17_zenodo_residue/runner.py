"""z17 — Zenodo bulk-publish residue: build classification manifest.

Pass-17 raised z17 with 35/37 bundles tagged: 1 publish / 14 keep / 20 review.
This runner formalizes the inventory as MANIFEST.json + classifies any
remaining files in zenodo_articles/, zenodo_bundle/, zenodo_deposit_dryrun/.

Pre-reg classification:
- PUBLISH: PD/Crystal/4-thirds papers, Pass-21 R-A, Pass-19 residual Sharpe (high-confidence shipped Zenodo records)
- KEEP_INTERNAL: drafts, dry-runs, residue
- NEEDS_REVIEW: anything containing 'sacred'/'god'/'messianic' that wasn't
  scrubbed in Pass 28
"""
import json, re
from pathlib import Path

REVIEW_PATTERN = re.compile(r'\b(sacred|god|messianic|divine)\b', re.IGNORECASE)
PUBLISH_KEYWORDS = ["pd_", "crystal", "four_third", "4_3", "r_a", "residual_sharpe",
                    "lcc_v3", "perfect_fifth"]

def classify(path):
    name = path.name.lower()
    try: text = path.read_text(errors='ignore').lower()
    except Exception: text = ""
    if REVIEW_PATTERN.search(text) or REVIEW_PATTERN.search(name):
        return "NEEDS_REVIEW"
    if any(kw in name for kw in PUBLISH_KEYWORDS):
        return "PUBLISH"
    if "dryrun" in str(path) or "draft" in name:
        return "KEEP_INTERNAL"
    return "KEEP_INTERNAL"

def main():
    inventory = {"PUBLISH": [], "KEEP_INTERNAL": [], "NEEDS_REVIEW": []}
    for d in ["zenodo_articles", "zenodo_bundle", "zenodo_deposit_dryrun"]:
        p = Path(d)
        if not p.exists(): continue
        for f in p.rglob("*.md"):
            cls = classify(f)
            inventory[cls].append(str(f))
    counts = {k: len(v) for k,v in inventory.items()}
    out = {"counts": counts,
           "total_files": sum(counts.values()),
           "pass17_baseline": "1 publish / 14 keep / 20 review (35/37 of 929-file inventory)",
           "manifest": inventory}
    Path("analyses/pass29_z17_zenodo_residue/MANIFEST.json").write_text(json.dumps(out, indent=2))
    print(json.dumps(counts, indent=2))
    print(f"Total: {sum(counts.values())}")

if __name__ == "__main__": main()
