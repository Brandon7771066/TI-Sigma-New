"""
UOP Rigor/Search Calibration — measurement script (Part II executor).

Implements EXACTLY the pre-registered design in
papers/UOP_RIGOR_SEARCH_CALIBRATION_PREREGISTRATION_2026-06-28.md.

Unit = one tactic invocation in a finished Lean 4 proof (same unit for R and S, so the
ratio r = R/S is dimensionless). Tactic names matched as whole words AFTER stripping
-- line comments and /- ... -/ block comments. Tactics in neither class are ignored.

This script does not know, reference, or use the 0.93 cap anywhere. It only counts.
"""

import os
import re
import sys
import statistics
from pathlib import Path


def safe_lean_files(root: Path):
    """Walk root, tolerating broken/dangling dir entries."""
    out = []
    for dirpath, dirnames, filenames in os.walk(root, onerror=lambda e: None):
        for fn in filenames:
            if fn.endswith(".lean"):
                out.append(Path(dirpath) / fn)
    return out

# ---- LOCKED taxonomy (verbatim from pre-registration §4) -------------------
RIGOR = {
    "exact", "exact?", "rfl", "simp", "simp_all", "simpa", "ring", "ring_nf",
    "linarith", "nlinarith", "norm_num", "norm_cast", "push_cast", "omega",
    "decide", "positivity", "field_simp", "assumption", "trivial", "tauto",
    "gcongr", "abel", "linear_combination", "polyrith", "rw", "rewrite",
    "subst", "congr", "calc",
}
SEARCH = {
    "apply", "refine", "intro", "intros", "rintro", "cases", "rcases", "obtain",
    "induction", "constructor", "use", "by_cases", "by_contra", "contrapose",
    "have", "suffices", "set", "let", "choose", "generalize", "wlog",
}

ALL_TACTICS = RIGOR | SEARCH

# whole-word matcher; allow trailing '?' for exact?/etc by including it in the set
# build an alternation, escaping, longest-first so 'simp_all' wins over 'simp'
_alt = sorted((re.escape(t) for t in ALL_TACTICS), key=len, reverse=True)
TACTIC_RE = re.compile(r"(?<![A-Za-z0-9_.])(" + "|".join(_alt) + r")(?![A-Za-z0-9_])")

BLOCK_COMMENT_RE = re.compile(r"/-.*?-/", re.DOTALL)
LINE_COMMENT_RE = re.compile(r"--[^\n]*")


def strip_comments(text: str) -> str:
    text = BLOCK_COMMENT_RE.sub(" ", text)
    text = LINE_COMMENT_RE.sub(" ", text)
    return text


def count_file(path: Path):
    try:
        text = path.read_text(encoding="utf-8", errors="ignore")
    except Exception:
        return None
    text = strip_comments(text)
    counts = {}
    for m in TACTIC_RE.finditer(text):
        tok = m.group(1)
        counts[tok] = counts.get(tok, 0) + 1
    return counts


def classify(counts, rigor_set, search_set):
    R = sum(v for k, v in counts.items() if k in rigor_set)
    S = sum(v for k, v in counts.items() if k in search_set)
    return R, S


def variant_sets(name):
    rigor = set(RIGOR)
    search = set(SEARCH)
    if name == "PRIMARY":
        pass
    elif name == "S1_have_suffices_to_rigor":
        for t in ("have", "suffices"):
            search.discard(t); rigor.add(t)
    elif name == "S2_rw_to_search":
        for t in ("rw", "rewrite"):
            rigor.discard(t); search.add(t)
    elif name == "S3_simp_to_search":
        for t in ("simp", "simp_all", "simpa"):
            rigor.discard(t); search.add(t)
    elif name == "S4_drop_intro":
        for t in ("intro", "intros", "rintro"):
            search.discard(t)
    return rigor, search


def run(corpus_root: Path, label: str):
    files = safe_lean_files(corpus_root)
    per_file_counts = []
    for p in files:
        c = count_file(p)
        if c:
            per_file_counts.append((p, c))

    print(f"\n========== CORPUS: {label} ==========")
    print(f"files scanned: {len(files)}; files with >=1 classified tactic: "
          f"{sum(1 for _, c in per_file_counts if classify(c, RIGOR, SEARCH)[1] > 0 or classify(c, RIGOR, SEARCH)[0] > 0)}")

    # PRIMARY aggregate + per-file distribution
    rigor_set, search_set = variant_sets("PRIMARY")
    totR = totS = 0
    per_file_r = []
    for _, c in per_file_counts:
        R, S = classify(c, rigor_set, search_set)
        totR += R
        totS += S
        if S > 0:
            per_file_r.append(R / S)
    agg = totR / totS if totS else float("nan")
    print(f"\n[PRIMARY taxonomy]")
    print(f"  ΣR = {totR:,}   ΣS = {totS:,}   aggregate r = ΣR/ΣS = {agg:.4f}")
    if per_file_r:
        per_file_r.sort()
        med = statistics.median(per_file_r)
        q1 = per_file_r[len(per_file_r)//4]
        q3 = per_file_r[(3*len(per_file_r))//4]
        in_band = sum(1 for x in per_file_r if 1.5 <= x <= 2.2)
        print(f"  per-file r: n={len(per_file_r)}  median={med:.4f}  IQR=[{q1:.3f}, {q3:.3f}]")
        print(f"  fraction of files with r_i in [1.5, 2.2]: "
              f"{in_band}/{len(per_file_r)} = {in_band/len(per_file_r):.3f}")

    # sensitivity variants (aggregate only)
    print(f"\n[sensitivity variants — aggregate r]")
    for name in ("S1_have_suffices_to_rigor", "S2_rw_to_search",
                 "S3_simp_to_search", "S4_drop_intro"):
        rs, ss = variant_sets(name)
        tR = tS = 0
        for _, c in per_file_counts:
            R, S = classify(c, rs, ss)
            tR += R; tS += S
        rv = tR / tS if tS else float("nan")
        flag = "in-band" if 1.5 <= rv <= 2.2 else "OUT-of-band"
        print(f"  {name:32s} r = {rv:.4f}   [{flag}]")

    # most common tactics for transparency
    tot = {}
    for _, c in per_file_counts:
        for k, v in c.items():
            tot[k] = tot.get(k, 0) + v
    print(f"\n[tactic totals, descending]")
    for k, v in sorted(tot.items(), key=lambda kv: -kv[1]):
        cls = "R" if k in RIGOR else ("S" if k in SEARCH else "?")
        print(f"  {k:20s} {v:>10,}  ({cls})")
    return agg


if __name__ == "__main__":
    base = Path("lean4_ns_uop_pass54_mathlib/.lake/packages/mathlib/Mathlib")
    if base.exists():
        run(base, "PRIMARY (Mathlib)")
    else:
        print(f"PRIMARY corpus not found at {base}", file=sys.stderr)

    # SECONDARY: repo-authored TI Lean files (contrast only, not decisive)
    secondary_roots = [Path("lean4"), Path("lean4_ti_sigma6")]
    sec_files = []
    for r in secondary_roots:
        if r.exists():
            sec_files += [p for p in safe_lean_files(r) if ".lake" not in p.parts]
    if sec_files:
        import tempfile
        # reuse run() by pointing at a synthetic root is awkward; inline instead
        per = []
        for p in sec_files:
            c = count_file(p)
            if c:
                per.append((p, c))
        tR = tS = 0
        for _, c in per:
            R, S = classify(c, RIGOR, SEARCH)
            tR += R; tS += S
        print(f"\n========== CORPUS: SECONDARY (repo TI Lean, contrast only) ==========")
        print(f"files: {len(sec_files)}   ΣR={tR}  ΣS={tS}  "
              f"aggregate r = {tR/tS if tS else float('nan'):.4f}")
