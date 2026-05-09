"""
Zenodo residue per-bundle summary report (Pass 18, z17 staging).

Brandon Pass-17 left 37 CLOSED-access drafts on Zenodo (IDs
20100920-20101111). To make per-bundle review (publish/keep/delete)
fast, this script generates a per-bundle summary:

  - Bundle title + Zenodo ID + URL
  - File count
  - Heuristic sensitivity tag:
      * BIO   = biographical / family
      * SACR  = sensitive (afterlife, soul-bluetooth, OB, sex)
      * URB   = numbered URB papers (mostly safe public)
      * MATH  = formal math papers (safe public)
      * GEN   = general (Brandon should review)
  - First-line preview of each file (first non-empty line)
  - Recommended action: PUBLISH-CANDIDATE / KEEP-CLOSED / REVIEW

Output: zenodo/residue_review_report.md (Markdown table for Brandon).

Per #69:
  - Heuristic tags are agent-judgment, not authoritative. Brandon
    overrides per-bundle.
  - "PUBLISH-CANDIDATE" recommendation does NOT auto-publish; it's a
    suggestion to speed up review.
"""
import json, re
from pathlib import Path

LOG = Path("zenodo/residue_upload_log.json")
PAPERS = Path("papers")
OUT = Path("zenodo/residue_review_report.md")

SACR_PATTERNS = [
    r"AFTERLIFE", r"SOUL_BLUETOOTH", r"SOUL_BB", r"OB_", r"OUT_BODY",
    r"SEX_", r"PORN", r"GROIN", r"PEDOPHIL", r"AGAPE_HOMOPHOBIA",
    r"DEATH_", r"SUICIDE", r"INPATIENT", r"ABUSE",
]
BIO_PATTERNS = [
    r"BRANDON_", r"MIMI_", r"GLORIA_", r"JEFF_", r"RAY_", r"LISA_",
    r"BIOGRAPHY", r"FAMILY", r"REIKI_HEALER", r"DIANE_HILLER",
    r"HOSPITAL_BIRTH", r"GOVERNORS_SCHOLAR", r"RETREAT_",
    r"CRYSTAL_LEE", r"KATIE", r"MAGGIE",
]
URB_PATTERN = re.compile(r"^urb_?\d+", re.IGNORECASE)
MATH_PATTERNS = [
    r"^RIEMANN_", r"^NAVIER", r"^YANG_MILLS", r"^MILLENNIUM",
    r"PROOF", r"THEOREM", r"AFFINE_MAPPING", r"SPECTRAL", r"HAMILTONIAN",
]


def classify(filename, first_line):
    f = filename.upper()
    if any(re.search(p, f) for p in SACR_PATTERNS):
        return "SACR", "KEEP-CLOSED"
    if any(re.search(p, f) for p in BIO_PATTERNS):
        return "BIO", "KEEP-CLOSED"
    if URB_PATTERN.match(filename):
        return "URB", "PUBLISH-CANDIDATE"
    if any(re.search(p, f) for p in MATH_PATTERNS):
        return "MATH", "PUBLISH-CANDIDATE"
    return "GEN", "REVIEW"


def first_meaningful_line(path):
    try:
        with open(path, "r", encoding="utf-8", errors="replace") as fh:
            for line in fh:
                s = line.strip()
                if s and not s.startswith("---"):
                    return s[:140]
    except Exception:
        return "(read error)"
    return "(empty)"


def reconstruct_bundle_files():
    """Re-run build_bundles to get per-bundle file lists."""
    import sys
    sys.path.insert(0, str(Path("zenodo")))
    from zenodo_residue_uploader import collect_residue, build_bundles
    return build_bundles(collect_residue())


def main():
    log = json.loads(LOG.read_text())
    bundles = reconstruct_bundle_files()

    # Match log entries to bundles by (letter, tag, n_files) primary,
    # then by (letter, n_files) for the 2 collision-fixed lowercase bundles
    # uploaded after the main batch (Pass-17 micro-bundles for 'o' & 'p').
    used = set()
    matched = []
    for entry in log:
        L, T, NF = entry["letter"], entry["tag"], entry["n_files"]
        found = False
        for i, (l, t, files) in enumerate(bundles):
            if i in used: continue
            if l == L and t == T and len(files) == NF:
                matched.append((entry, files)); used.add(i); found = True; break
        if not found:
            # fallback: match by (letter, n_files) ignoring tag
            for i, (l, t, files) in enumerate(bundles):
                if i in used: continue
                if l == L and len(files) == NF:
                    matched.append((entry, files)); used.add(i); break

    out = ["# Zenodo Residue Bundle Review Report (Pass 18, z17 staging)",
           "", f"**Total bundles**: {len(matched)} / {len(log)}",
           f"**Source log**: `zenodo/residue_upload_log.json`", "",
           "## Tag legend", "",
           "- **BIO**  — biographical / family material (default KEEP-CLOSED)",
           "- **SACR** — sensitive content (default KEEP-CLOSED)",
           "- **URB**  — numbered URB paper (default PUBLISH-CANDIDATE)",
           "- **MATH** — formal math/theorem paper (default PUBLISH-CANDIDATE)",
           "- **GEN**  — general (Brandon REVIEW)", "",
           "## Action legend", "",
           "- **PUBLISH-CANDIDATE** — agent-suggests promoting to PUBLIC + cc-by-4.0",
           "- **KEEP-CLOSED** — agent-suggests leave as PRIVATE / closed",
           "- **REVIEW** — Brandon decides", "",
           "---", ""]

    counts = {"PUBLISH-CANDIDATE": 0, "KEEP-CLOSED": 0, "REVIEW": 0}
    for entry, files in matched:
        url = entry["url"]; zid = entry["id"]
        title = entry["title"]
        # Bundle-level recommendation = majority of file-level recs;
        # but if ANY SACR/BIO present, default conservatively to KEEP-CLOSED.
        per_file = []
        bundle_action = "REVIEW"
        for f in files:
            tag, action = classify(f, "")
            per_file.append((f, tag, action))
        tags = [t for _, t, _ in per_file]
        if any(t in ("SACR", "BIO") for t in tags):
            bundle_action = "KEEP-CLOSED"
        elif all(t in ("URB", "MATH") for t in tags):
            bundle_action = "PUBLISH-CANDIDATE"
        else:
            bundle_action = "REVIEW"
        counts[bundle_action] += 1

        out.append(f"### Bundle {entry['letter']}{('-'+entry['tag']) if entry['tag'] else ''}  "
                   f"— `{title}`")
        out.append(f"")
        out.append(f"- Zenodo ID: **{zid}**  →  {url}")
        out.append(f"- Files: **{len(files)}**")
        out.append(f"- Tag breakdown: " +
                   ", ".join(f"{t}={tags.count(t)}" for t in sorted(set(tags))))
        out.append(f"- **Recommended action**: `{bundle_action}`")
        out.append("")
        out.append("<details><summary>File list</summary>\n")
        for f, tag, _ in per_file:
            preview = first_meaningful_line(PAPERS / f)
            out.append(f"- `[{tag}]` `{f}` — {preview}")
        out.append("\n</details>\n")
        out.append("---\n")

    out.insert(7, f"\n## Summary counts\n\n"
                  f"- **PUBLISH-CANDIDATE**: {counts['PUBLISH-CANDIDATE']} bundles\n"
                  f"- **KEEP-CLOSED**:       {counts['KEEP-CLOSED']} bundles\n"
                  f"- **REVIEW**:            {counts['REVIEW']} bundles\n")

    OUT.write_text("\n".join(out))
    print(f"Wrote {OUT}  ({len(matched)} bundles, "
          f"{counts['PUBLISH-CANDIDATE']} publish-cand, "
          f"{counts['KEEP-CLOSED']} keep-closed, "
          f"{counts['REVIEW']} review)")


if __name__ == "__main__":
    main()
