#!/usr/bin/env python3
"""
Tiny CLI to append one row to data/subjective_daily_log.csv.

Usage examples:
  python log_daily_subjective.py                          # interactive prompt
  python log_daily_subjective.py --energy 3 --mood 4 --focus 3 --edge 2 \
      --confusion 0 --notes "Adderall day 2. Less tired."

Scales: 1 = very low, 5 = very high. Use whatever you'd say if asked
casually. Honest > precise.
"""
from __future__ import annotations

import argparse
import csv
import datetime as _dt
from pathlib import Path

LOG_PATH = Path("data/subjective_daily_log.csv")
HEADER = [
    "date",
    "energy_1to5",
    "mood_1to5",
    "focus_1to5",
    "edge_1to5",
    "confusion_episodes",
    "notes",
]


def _prompt_int(label: str, lo: int = 1, hi: int = 5) -> int:
    while True:
        raw = input(f"  {label} [{lo}-{hi}]: ").strip()
        if not raw:
            print("    (required)")
            continue
        try:
            v = int(raw)
        except ValueError:
            print(f"    not an integer: {raw!r}")
            continue
        if not lo <= v <= hi:
            print(f"    must be {lo}..{hi}")
            continue
        return v


def main() -> int:
    ap = argparse.ArgumentParser(description="Append one row to subjective_daily_log.csv")
    ap.add_argument("--date", default=_dt.date.today().isoformat(),
                    help="ISO date (default: today)")
    ap.add_argument("--energy", type=int)
    ap.add_argument("--mood", type=int)
    ap.add_argument("--focus", type=int)
    ap.add_argument("--edge", type=int)
    ap.add_argument("--confusion", type=int, default=0,
                    help="count of confusion / dropped-thread episodes today")
    ap.add_argument("--notes", default="")
    args = ap.parse_args()

    interactive = any(v is None for v in (args.energy, args.mood, args.focus, args.edge))
    if interactive:
        print(f"Logging subjective state for {args.date}")
        if args.energy is None:
            args.energy = _prompt_int("energy")
        if args.mood is None:
            args.mood = _prompt_int("mood")
        if args.focus is None:
            args.focus = _prompt_int("focus")
        if args.edge is None:
            args.edge = _prompt_int("edge / stimulation feel", 1, 5)
        if not args.notes:
            args.notes = input("  notes (one line, free text, optional): ").strip()

    for name, val in [("energy", args.energy), ("mood", args.mood),
                      ("focus", args.focus), ("edge", args.edge)]:
        if val is None or not 1 <= val <= 5:
            raise SystemExit(f"--{name} required and must be 1..5 (got {val!r})")
    if args.confusion < 0:
        raise SystemExit("--confusion must be >= 0")

    LOG_PATH.parent.mkdir(parents=True, exist_ok=True)
    new_file = not LOG_PATH.exists()
    with LOG_PATH.open("a", newline="", encoding="utf-8") as fh:
        w = csv.writer(fh)
        if new_file:
            w.writerow(HEADER)
        w.writerow([
            args.date,
            args.energy,
            args.mood,
            args.focus,
            args.edge,
            args.confusion,
            args.notes,
        ])
    print(f"Wrote 1 row to {LOG_PATH}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
