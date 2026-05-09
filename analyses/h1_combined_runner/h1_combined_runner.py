"""
H1 combined back-to-back runner — H1-BB + H1-Penrose with cross-domain
correlation analysis (Pass 18, p17 directive).

Brandon usage (single sit-down, ~50 min):
  python analyses/h1_combined_runner/h1_combined_runner.py --rate

Order: 50/50 randomized which harness goes first (per session, seeded).
Both harnesses are run end-to-end; rater's GILE-I/G self-rating is
captured ONCE at session start. After both, results are scored
together:
  - H1-BB:        hits/30, p-value vs binomial null
  - H1-Penrose:   hits/10, p-value vs binomial null
  - Cross-domain: do hit-rates correlate within session?

Per #69:
  - "Cross-domain correlation" with N=2 (two domains, one rater) is
    not a statistical test, it's a qualitative-direction read. We
    report whether both clear, both fail, or one of each. A real
    correlation test needs ≥10 raters across both domains.
  - Brandon should NOT peek at H1-BB scoring before completing
    H1-Penrose (or vice versa); the runner enforces this by
    storing answers but only revealing scores after both are done.
  - Randomized ordering avoids order-fatigue / order-prior biasing
    one harness over the other.

Seed: 20260509.
"""
import argparse, json, random, math
from datetime import datetime
from pathlib import Path

SEED = 20260509
RESULTS = Path("analyses/h1_combined_runner/h1_combined_results.json")

import sys
sys.path.insert(0, str(Path("analyses/h1_bb_intuition")))
sys.path.insert(0, str(Path("analyses/h1_penrose")))

# Lazy import of the patch lists (don't trigger their __main__)
def load_bb_patches():
    from h1_bb_intuition_harness import MACHINES as BB
    return BB

def load_penrose_patches():
    from h1_penrose_harness import PATCHES as PEN
    return PEN


def show_bb(p, idx, total):
    print(f"\n[BB {idx+1}/{total}]  id={p['id']}  "
          f"class={p.get('class', p.get('kind','?'))}")
    print(f"  {p.get('desc', p.get('description', ''))}")


def show_penrose(p, idx, total):
    print(f"\n[Penrose {idx+1}/{total}]  id={p['id']}  kind={p['kind']}")
    print(f"  {p['desc']}")


def rate_one(name, patches, show_fn, ans_keys=("h","n","p"), prompt=""):
    print(f"\n{'='*70}\n  {name} — {len(patches)} patches\n{'='*70}")
    print(prompt)
    input("Press Enter to begin...")
    rng = random.Random(SEED + hash(name) % 1000)
    indices = list(range(len(patches)))
    rng.shuffle(indices)
    answers = []
    for k, i in enumerate(indices):
        p = patches[i]; show_fn(p, k, len(patches))
        a = input(f"  {'/'.join(ans_keys)}: ").strip().lower()
        if a not in ans_keys: a = ans_keys[-1]
        answers.append({"id": p["id"], "answer": a})
    return answers


def score_bb(answers, patches):
    truth = {p["id"]: p.get("halts", p.get("completable")) for p in patches}
    attempted = [a for a in answers if a["answer"] in ("h", "n")]
    hits = sum(1 for a in attempted if (a["answer"] == "h") == bool(truth[a["id"]]))
    return len(attempted), hits


def score_pen(answers, patches):
    truth = {p["id"]: p["completable"] for p in patches}
    attempted = [a for a in answers if a["answer"] in ("c", "n")]
    hits = sum(1 for a in attempted if (a["answer"] == "c") == bool(truth[a["id"]]))
    return len(attempted), hits


def binom_p_one_sided(hits, n, p_null=0.5):
    if n == 0: return float("nan"), 0.0
    mu = n * p_null; sd = math.sqrt(n * p_null * (1 - p_null))
    z = (hits - 0.5 - mu) / sd if sd > 0 else 0.0
    p = 0.5 * math.erfc(z / math.sqrt(2))
    return p, z


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--rate", action="store_true")
    parser.add_argument("--score-only", action="store_true")
    args = parser.parse_args()

    RESULTS.parent.mkdir(parents=True, exist_ok=True)

    if args.score_only and RESULTS.exists():
        rec = json.loads(RESULTS.read_text())[-1]
        bb_n, bb_hits = score_bb(rec["bb_answers"], load_bb_patches())
        pen_n, pen_hits = score_pen(rec["pen_answers"], load_penrose_patches())
        print_results(bb_n, bb_hits, pen_n, pen_hits, rec)
        return

    if not args.rate:
        parser.print_help(); return

    print("=" * 70)
    print("H1 combined sit-down — H1-BB (30 patches) + H1-Penrose (10 patches)")
    print("=" * 70)
    rater = input("Rater id: ").strip() or "brandon"
    gile_i = input("Self-rated GILE-Intuition 0-1 (or skip): ").strip()
    gile_g = input("Self-rated overall GILE 0-1 (or skip): ").strip()

    rng = random.Random(SEED ^ int(datetime.utcnow().timestamp()))
    bb_first = rng.random() < 0.5
    print(f"\nOrder this session: {'H1-BB first' if bb_first else 'H1-Penrose first'}")

    bb = load_bb_patches(); pen = load_penrose_patches()

    bb_prompt = ("Protocol: ~30s/patch, intuition only. Answer h (halts), n (never halts), p (pass).")
    pen_prompt = ("Protocol: ~30s/patch, intuition only. Answer c (completable to whole plane), n (not completable), p (pass).")

    if bb_first:
        bb_answers = rate_one("H1-BB", bb, show_bb, ("h","n","p"), bb_prompt)
        pen_answers = rate_one("H1-Penrose", pen, show_penrose, ("c","n","p"), pen_prompt)
    else:
        pen_answers = rate_one("H1-Penrose", pen, show_penrose, ("c","n","p"), pen_prompt)
        bb_answers = rate_one("H1-BB", bb, show_bb, ("h","n","p"), bb_prompt)

    rec = {
        "rater": rater, "gile_i": gile_i, "gile_g": gile_g,
        "timestamp": datetime.utcnow().isoformat() + "Z",
        "session_seed": SEED, "bb_first": bb_first,
        "bb_answers": bb_answers, "pen_answers": pen_answers,
    }
    out = []
    if RESULTS.exists(): out = json.loads(RESULTS.read_text())
    out.append(rec); RESULTS.write_text(json.dumps(out, indent=2))

    bb_n, bb_hits = score_bb(bb_answers, bb)
    pen_n, pen_hits = score_pen(pen_answers, pen)
    print_results(bb_n, bb_hits, pen_n, pen_hits, rec)


def print_results(bb_n, bb_hits, pen_n, pen_hits, rec):
    print("\n" + "=" * 70)
    print("  COMBINED RESULTS")
    print("=" * 70)
    bb_p, bb_z = binom_p_one_sided(bb_hits, bb_n)
    pen_p, pen_z = binom_p_one_sided(pen_hits, pen_n)
    bb_rate = bb_hits / bb_n if bb_n else 0.0
    pen_rate = pen_hits / pen_n if pen_n else 0.0
    print(f"  H1-BB:       {bb_hits:>2}/{bb_n:>2}  rate={bb_rate:.3f}  z={bb_z:+.2f}  p={bb_p:.4f}")
    print(f"  H1-Penrose:  {pen_hits:>2}/{pen_n:>2}  rate={pen_rate:.3f}  z={pen_z:+.2f}  p={pen_p:.4f}")
    print()
    bb_clear = bb_p < 0.05; pen_clear = pen_p < 0.05
    print("  Cross-domain reading (#69 honest, N=1 rater):")
    if bb_clear and pen_clear:
        print("  → BOTH harnesses cleared p<0.05. Evidence consistent with")
        print("    GENERAL hypercomputing intuition rather than domain-specific.")
    elif bb_clear and not pen_clear:
        print("  → BB cleared, Penrose did not. Evidence consistent with")
        print("    DOMAIN-SPECIFIC ability (TM-halting > tiling completability).")
    elif pen_clear and not bb_clear:
        print("  → Penrose cleared, BB did not. Evidence consistent with")
        print("    DOMAIN-SPECIFIC ability (tiling > TM-halting).")
    else:
        print("  → Neither harness cleared. No evidence for hypercomputing")
        print("    intuition this session; consider re-running with different")
        print("    rater or expanded harness.")
    print()
    print(f"  GILE-I self-rating: {rec.get('gile_i','?')}")
    print(f"  GILE-G self-rating: {rec.get('gile_g','?')}")


if __name__ == "__main__":
    main()
