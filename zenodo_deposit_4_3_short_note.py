"""
Zenodo deposit — 4/3 Structural Invariant Short Note (Pass 12).

Creates a Zenodo DRAFT containing:
  - papers/FOUR_THIRDS_INVARIANT_SHORT_NOTE_2026-05-09.md
  - analyses/four_thirds_montecarlo/four_thirds_mc.py
  - analyses/four_thirds_montecarlo/results.txt

Brandon publishes the draft via the Zenodo browser UI (same Pass-9 pattern).

Usage:
  python zenodo_deposit_4_3_short_note.py        # SANDBOX (safe test)
  python zenodo_deposit_4_3_short_note.py --live # LIVE Zenodo (real DOI)
"""
import json, os, pathlib, sys, requests

LIVE = "--live" in sys.argv
BASE = "https://zenodo.org/api" if LIVE else "https://sandbox.zenodo.org/api"
SITE = "https://zenodo.org/deposit" if LIVE else "https://sandbox.zenodo.org/deposit"
TOK  = os.environ.get("ZENODO_TOKEN")
if not TOK:
    sys.exit("ZENODO_TOKEN missing.")
H = {"Authorization": f"Bearer {TOK}"}

FILES = [
    "papers/FOUR_THIRDS_INVARIANT_SHORT_NOTE_2026-05-09.md",
    "analyses/four_thirds_montecarlo/four_thirds_mc.py",
    "analyses/four_thirds_montecarlo/results.txt",
]
META = {
    "title": "A 4/3 Structural Invariant in the PD Geometry of Tralse Informationalism: A Short Note",
    "upload_type": "publication",
    "publication_type": "article",
    "description": (
        "<p>Short note documenting and statistically testing a 4/3 structural invariant that "
        "appears at five geometrically-distinct, independently-derived locations in the PD "
        "(Permissibility Distribution) architecture of Tralse Informationalism. Monte Carlo "
        "(M = 10<sup>6</sup>) and analytic computation under four null specifications give "
        "p &lt;&lt; 10<sup>−3</sup> for any-common-ratio readings and p ~ 10<sup>−7</sup> to "
        "10<sup>−9</sup> for the specific-4/3 reading. Companion to the May 2026 Pass 8.1/8.2 "
        "ratifications and Pass 10 Tier-1 validation. Includes reproducible script + results "
        "(standard CPython 3, standard library only, deterministic seed 20260509).</p>"
        "<p>Manuscript edition. CC BY 4.0. Suitable for arXiv math.HO submission.</p>"
    ),
    "creators": [{"name": "Emerick, Brandon Charles", "affiliation": "Independent Researcher"}],
    "keywords": ["Tralse Informationalism", "Permissibility Distribution", "Monte Carlo",
                 "structural invariant", "4/3 ratio", "PD geometry", "TI Sigma",
                 "Asymmetric Standards", "pre-registration"],
    "communities": [],
    "access_right": "open",
    "license": "cc-by-4.0",
    "language": "eng",
    "notes": "Pass 12 standalone deposit. Companion: Pass 9 Zenodo deposit id=20091187.",
}


def main():
    print(f"\n=== Zenodo deposit — 4/3 short note ===")
    print(f"Endpoint: {'LIVE zenodo.org' if LIVE else 'SANDBOX'}")
    for f in FILES:
        if not pathlib.Path(f).exists(): sys.exit(f"missing: {f}")
    r = requests.post(f"{BASE}/deposit/depositions", json={}, headers=H, timeout=30)
    r.raise_for_status()
    dep = r.json(); dep_id = dep["id"]
    print(f"  Draft created: id={dep_id}")
    bucket = dep["links"]["bucket"]
    for f in FILES:
        p = pathlib.Path(f)
        with open(p, "rb") as fh:
            ru = requests.put(f"{bucket}/{p.name}", data=fh, headers=H, timeout=120)
        ru.raise_for_status()
        print(f"  uploaded: {p.name}  ({p.stat().st_size//1024+1} KB)")
    rm = requests.put(f"{BASE}/deposit/depositions/{dep_id}",
                      json={"metadata": META}, headers=H, timeout=30)
    rm.raise_for_status()
    print(f"  metadata set: {META['title']}")
    print(f"\n  DRAFT URL → {SITE}/{dep_id}")
    print(f"  Brandon: review + click PUBLISH on Zenodo when ready.")
    out = {"deposit_id": dep_id, "draft_url": f"{SITE}/{dep_id}",
           "live": LIVE, "title": META["title"]}
    pathlib.Path("zenodo_4_3_short_note_record.json").write_text(json.dumps(out, indent=2))
    print(f"  Record saved to zenodo_4_3_short_note_record.json")


if __name__ == "__main__":
    main()
