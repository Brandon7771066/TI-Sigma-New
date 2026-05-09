"""
H1-Penrose — tiling-completion intuition harness (Pass 17, e16 directive).

Companion to H1-BB (analyses/h1_bb_intuition/). Same protocol, but
the test-domain is *aperiodic-tiling completability* instead of TM-
halting. Both belong to the same undecidable-problem class
(Wang-tile undecidability of the domino problem; Berger 1966).

Pre-loaded set: 10 small Penrose / einstein-tile / Wang-tile patches
with hidden completability labels drawn from the published
classifications (Penrose P3, Smith-Myers-Kaplan-Goodman-Strauss
einstein 'hat' tile 2023, classical Wang-tile aperiodic sets).

Brandon usage:
  python analyses/h1_penrose/h1_penrose_harness.py --rate
  python analyses/h1_penrose/h1_penrose_harness.py --score
  python analyses/h1_penrose/h1_penrose_harness.py --auto    # baseline
  python analyses/h1_penrose/h1_penrose_harness.py --list

Per #69:
  - 10 patches is small (vs 30 for H1-BB); harness is intentionally
    short to be a low-burden parallel test for cross-domain
    consistency. If H1-BB and H1-Penrose hit rates correlate within
    a single rater, that's evidence for *general* hypercomputing
    intuition (rather than domain-specific ability).
  - Truth labels are agent-curated from public results and patch-
    descriptions only; no hand-constructed images this Pass. A
    Pass-18 candidate is to ship the actual patch images alongside
    the descriptions.
  - Brandon should ALSO run H1-BB before H1-Penrose so the two
    score-vectors can be compared.

Seed: 20260509.
"""
import argparse, json, random
from datetime import datetime
from pathlib import Path

SEED = 20260509
RESULTS = Path("analyses/h1_penrose/h1_penrose_results.json")
random.seed(SEED)

PATCHES = [
    {"id": "P01", "kind": "Penrose P3 (kite/dart)",
     "desc": "Small kite-and-dart patch (8 tiles) covering a region around a fivefold-symmetric vertex. Local matching rules (arrow markings) are obeyed everywhere visible. Completability: ?",
     "completable": True},
    {"id": "P02", "kind": "Penrose P3 (kite/dart)",
     "desc": "12-tile kite-and-dart patch with one isolated dart whose arrow marking conflicts with two adjacent kites' inner-arrow markings. Local rule violation visible if examined.",
     "completable": False},
    {"id": "P03", "kind": "Penrose P3 (rhomb)",
     "desc": "10-tile thin/thick-rhomb patch arranged in a sun-like configuration. Markings obey the matching rules; the configuration is one of the seven legal vertex types.",
     "completable": True},
    {"id": "P04", "kind": "einstein 'hat' tile (2023)",
     "desc": "6-hat patch including 2 reflected ('turtle') hats. Adjacency rules from SMKGS 2023 satisfied throughout the patch.",
     "completable": True},
    {"id": "P05", "kind": "einstein 'hat' tile (2023)",
     "desc": "8-hat patch where two adjacent hats both face the same direction without a reflected hat between them — violates SMKGS reflection-density requirement at one edge.",
     "completable": False},
    {"id": "P06", "kind": "Wang tile (aperiodic 11-tile set, Jeandel-Rao 2015)",
     "desc": "5-tile Wang patch from the Jeandel-Rao aperiodic set; all four edge colors match between adjacent tiles.",
     "completable": True},
    {"id": "P07", "kind": "Wang tile (aperiodic set)",
     "desc": "6-tile Wang patch where two adjacent tiles share an edge with mismatching colors (red-blue against blue-red). Local rule violation.",
     "completable": False},
    {"id": "P08", "kind": "Penrose P3 (rhomb)",
     "desc": "20-tile rhomb patch that is locally consistent everywhere but globally fails — the configuration forces an empty 'hole' two rings outward that no legal vertex type can fill. Hidden global obstruction.",
     "completable": False},
    {"id": "P09", "kind": "einstein 'hat' tile (2023)",
     "desc": "12-hat patch including 3 reflected hats (above the SMKGS density floor of 1/8). All adjacencies legal.",
     "completable": True},
    {"id": "P10", "kind": "Penrose P3 (kite/dart)",
     "desc": "15-tile patch around an apparent decapod defect; the markings are locally consistent but the patch belongs to a non-completable class identified by Conway (1977, unpublished correspondence summarized in Senechal 1995).",
     "completable": False},
]
assert len(PATCHES) == 10


def show(p, idx):
    print(f"\n[Patch {idx+1}/{len(PATCHES)}]  id={p['id']}  kind={p['kind']}")
    print(f"  {p['desc']}")


def rate_interactive(out_path):
    print("=" * 70)
    print("H1-Penrose tiling-completion intuition test — INTERACTIVE")
    print("=" * 70)
    rater = input("Rater id: ").strip() or "brandon"
    gile_i = input("Self-rated GILE-Intuition 0-1 (or skip): ").strip()
    gile_g = input("Self-rated overall GILE 0-1 (or skip): ").strip()
    print("Protocol: ~30s/patch, intuition only, no construction or simulation.")
    print("Answer: 'c' (completable to whole plane), 'n' (not completable), 'p' (pass).")
    input("Press Enter to begin...")
    answers = []
    rng = random.Random(SEED)
    indices = list(range(len(PATCHES)))
    rng.shuffle(indices)
    for k, i in enumerate(indices):
        p = PATCHES[i]
        show(p, k)
        ans = input("  c/n/p: ").strip().lower()
        if ans not in ("c", "n", "p"): ans = "p"
        answers.append({"id": p["id"], "answer": ans})
    rec = {"rater": rater, "gile_i": gile_i, "gile_g": gile_g,
           "timestamp": datetime.utcnow().isoformat() + "Z",
           "seed": SEED, "answers": answers}
    out = []
    if out_path.exists(): out = json.loads(out_path.read_text())
    out.append(rec); out_path.write_text(json.dumps(out, indent=2))
    print(f"\nSaved to {out_path}.")


def auto_baseline(out_path, n=2000):
    rng = random.Random(SEED)
    hits = []
    for _ in range(n):
        h = sum(1 for p in PATCHES if (rng.choice(["c","n"]) == ("c" if p["completable"] else "n")))
        hits.append(h)
    out = {"kind": "auto_baseline_synthetic_penrose", "n_trials": n, "n_patches": len(PATCHES),
           "hits_mean": float(sum(hits)/n),
           "hits_std": float((sum((h - sum(hits)/n)**2 for h in hits)/(n-1))**0.5),
           "hits_min": min(hits), "hits_max": max(hits),
           "p_at_or_above_8_of_10": sum(1 for h in hits if h >= 8)/n,
           "p_at_or_above_9_of_10": sum(1 for h in hits if h >= 9)/n,
           "p_at_or_above_10_of_10": sum(1 for h in hits if h >= 10)/n}
    out_path.write_text(json.dumps(out, indent=2))
    print(json.dumps(out, indent=2))


def score(in_path):
    if not in_path.exists():
        print(f"No results at {in_path}; nothing to score."); return
    records = json.loads(in_path.read_text())
    truth = {p["id"]: p["completable"] for p in PATCHES}
    import math
    print("=" * 70); print("H1-Penrose — scoring"); print("=" * 70)
    for rec in records:
        if rec.get("kind","").startswith("auto"): continue
        rater = rec.get("rater","?")
        ans = rec.get("answers", [])
        attempted = [a for a in ans if a["answer"] in ("c","n")]
        hits = sum(1 for a in attempted if (a["answer"] == "c") == truth[a["id"]])
        n = len(attempted)
        rate = hits/n if n else 0.0
        if n >= 1:
            mu = n*0.5; sd = math.sqrt(n*0.25)
            z = (hits - 0.5 - mu)/sd if sd > 0 else 0.0
            p = 0.5 * math.erfc(z / math.sqrt(2))
        else: p = float("nan"); z = 0.0
        print(f"  rater={rater}  attempted={n}/10  hits={hits}  rate={rate:.3f}  z={z:+.2f}  p_one_sided={p:.4f}")
        print(f"    GILE-I={rec.get('gile_i','?')}  GILE-G={rec.get('gile_g','?')}")


def main():
    p = argparse.ArgumentParser()
    p.add_argument("--rate", action="store_true")
    p.add_argument("--score", action="store_true")
    p.add_argument("--auto", action="store_true")
    p.add_argument("--list", action="store_true")
    a = p.parse_args()
    RESULTS.parent.mkdir(parents=True, exist_ok=True)
    if a.list:
        for k, q in enumerate(PATCHES):
            print(f"  [{k+1:2d}] {q['id']}  {q['kind']}\n       {q['desc']}")
        return
    if a.auto: auto_baseline(RESULTS.parent / "h1_penrose_baseline.json"); return
    if a.rate: rate_interactive(RESULTS); return
    if a.score: score(RESULTS); return
    p.print_help()


if __name__ == "__main__":
    main()
