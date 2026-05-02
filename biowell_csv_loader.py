#!/usr/bin/env python3
"""
Biowell CSV loader + diff tool.

Parses the semi-structured Biowell summary CSV (semicolon-delimited,
quoted, with section headers) into a flat dict of metric_name -> value.
Diffs a new screening against the 2025-11-25 baseline and prints any
metric with absolute relative change > THRESHOLD (default 30%).

Usage:
  python biowell_csv_loader.py --parse <path-to-csv>
  python biowell_csv_loader.py --diff <YYYY-MM-DD> [--threshold 0.30]
  python biowell_csv_loader.py --diff <YYYY-MM-DD> --against <other-date>

The Nov 25 2025 baseline is read from
attached_assets/BioWell_1764096972523.csv (the original upload).
"""
from __future__ import annotations

import argparse
import csv
import json
import sys
from pathlib import Path
from typing import Dict, Optional, Tuple

BASELINE_CSV = Path("attached_assets/BioWell_1764096972523.csv")
DATA_ROOT = Path("data/biowell")


def parse_biowell_csv(path: Path) -> Tuple[Dict[str, float], Dict[str, str]]:
    """
    Parse a Biowell semicolon-delimited CSV.

    Returns (metrics, meta).
    - metrics: flat dict of disambiguated metric_name -> float value
    - meta:    {date, subject, source_path}

    Disambiguation: when the same label appears in different sections
    (e.g. "Energy" in Lifestyle vs "Energy" in Chakras), the section
    header is prefixed: "<section>::<label>".
    """
    if not path.exists():
        raise FileNotFoundError(f"Biowell CSV not found: {path}")

    metrics: Dict[str, float] = {}
    meta: Dict[str, str] = {"source_path": str(path)}
    current_section: Optional[str] = None
    current_subsection: Optional[str] = None

    with path.open("r", encoding="utf-8", errors="replace") as fh:
        reader = csv.reader(fh, delimiter=";", quotechar='"')
        for raw in reader:
            cells = [c.strip().strip('"') for c in raw]
            if len(cells) < 3:
                continue
            col_a, col_b, col_c = cells[0], cells[1], cells[2]

            if col_b == "" and col_c and "20" in col_c and "-" in col_c:
                meta.setdefault("date", col_c)
                continue
            if col_b == "" and col_c and "(" in col_c and ")" in col_c:
                meta.setdefault("subject", col_c)
                continue
            if col_b == "" and col_c == "":
                continue

            if col_b and col_c == "":
                current_section = col_b
                current_subsection = None
                continue

            if col_b in ("Name", "Organ"):
                current_subsection = col_c.strip() or None
                continue

            if col_b and col_c:
                try:
                    val = float(col_c)
                except ValueError:
                    continue

                key_parts = []
                if current_section:
                    key_parts.append(current_section)
                if current_subsection:
                    key_parts.append(current_subsection)
                key_parts.append(col_b)
                key = "::".join(key_parts)

                if key in metrics:
                    suffix = 2
                    while f"{key}#{suffix}" in metrics:
                        suffix += 1
                    key = f"{key}#{suffix}"

                metrics[key] = val

    return metrics, meta


def find_screening_csv(date_iso: str) -> Path:
    """Return the path to the screening CSV for a given date."""
    folder = DATA_ROOT / date_iso
    candidates = [
        folder / "biowell_summary.csv",
        folder / "biowell.csv",
    ]
    if folder.exists():
        candidates.extend(sorted(folder.glob("BioWell*.csv")))
    for c in candidates:
        if c.exists():
            return c
    raise FileNotFoundError(
        f"No CSV found in {folder}. Expected {folder}/biowell_summary.csv "
        "or a BioWell*.csv file."
    )


def diff_screenings(
    a: Dict[str, float], b: Dict[str, float], threshold: float
) -> list:
    """
    Compute relative change from a (older) to b (newer).
    Returns list of (key, val_a, val_b, rel_change) sorted by |rel_change| desc.
    """
    common = set(a) & set(b)
    rows = []
    for k in common:
        va, vb = a[k], b[k]
        if va == 0 and vb == 0:
            continue
        if va == 0:
            rel = float("inf") if vb > 0 else float("-inf")
        else:
            rel = (vb - va) / abs(va)
        rows.append((k, va, vb, rel))
    rows.sort(key=lambda r: abs(r[3]) if r[3] != float("inf") else 1e9,
              reverse=True)
    return rows


def cmd_parse(path_str: str) -> int:
    metrics, meta = parse_biowell_csv(Path(path_str))
    print(json.dumps({"meta": meta, "metric_count": len(metrics),
                      "metrics": metrics}, indent=2, sort_keys=True))
    return 0


def cmd_diff(date_iso: str, against: Optional[str], threshold: float) -> int:
    new_csv = find_screening_csv(date_iso)
    new_m, new_meta = parse_biowell_csv(new_csv)

    if against is None:
        base_path = BASELINE_CSV
        base_label = "2025-11-25 baseline (attached_assets)"
    else:
        base_path = find_screening_csv(against)
        base_label = f"{against}"
    base_m, base_meta = parse_biowell_csv(base_path)

    print(f"Baseline:  {base_label}  ({len(base_m)} metrics, "
          f"date={base_meta.get('date','?')})")
    print(f"New:       {date_iso}    ({len(new_m)} metrics, "
          f"date={new_meta.get('date','?')})")
    print(f"Threshold: |Δ| > {threshold:.0%}")
    print(f"Common metrics: {len(set(base_m) & set(new_m))}")
    only_base = set(base_m) - set(new_m)
    only_new = set(new_m) - set(base_m)
    if only_base:
        print(f"  In baseline only: {len(only_base)}")
    if only_new:
        print(f"  In new only:      {len(only_new)}")
    print()

    rows = diff_screenings(base_m, new_m, threshold)
    flagged = [r for r in rows if abs(r[3]) >= threshold and r[3] != float("inf")]
    if not flagged:
        print(f"No metrics exceeded ±{threshold:.0%} change. "
              "Both readings within Biowell day-to-day measurement noise.")
        return 0

    print(f"{'metric':<70}  {'baseline':>10}  {'new':>10}  {'rel Δ':>10}")
    print("-" * 105)
    for k, va, vb, rel in flagged:
        sign = "+" if rel >= 0 else ""
        rel_str = "INF" if rel == float("inf") else f"{sign}{rel:.1%}"
        print(f"{k[:70]:<70}  {va:>10.3f}  {vb:>10.3f}  {rel_str:>10}")
    print()
    print(f"Note: N=2 readings only. A {threshold:.0%}+ shift is "
          "*worth investigating*, NOT statistically significant.")
    return 0


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    g = ap.add_mutually_exclusive_group(required=True)
    g.add_argument("--parse", metavar="PATH",
                   help="parse a Biowell CSV and dump JSON")
    g.add_argument("--diff", metavar="YYYY-MM-DD",
                   help="diff this date's screening against baseline")
    ap.add_argument("--against", metavar="YYYY-MM-DD",
                    help="diff against another dated screening "
                         "(default: Nov 25 2025 baseline)")
    ap.add_argument("--threshold", type=float, default=0.30,
                    help="relative change threshold to flag (default 0.30)")
    args = ap.parse_args()

    if args.parse:
        return cmd_parse(args.parse)
    return cmd_diff(args.diff, args.against, args.threshold)


if __name__ == "__main__":
    sys.exit(main())
