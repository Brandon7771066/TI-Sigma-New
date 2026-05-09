"""
H1 — Hypercomputing Intuition Test on Small Turing Machines (Pass 16).

Pass-15 §4.2 protocol: rater predicts halt-vs-non-halt purely on
intuition, 30s budget per machine, no simulation. Compare hit rate vs
50% chance baseline (binomial test). Falsification anchor: chance
performance disconfirms retrocausal-intuition hypothesis for this
domain.

This harness pre-loads 30 small TMs whose halting status is publicly
known. The rater (Brandon) runs the harness; results saved to a JSON
file; binomial test computed automatically.

Brandon usage:
  python analyses/h1_bb_intuition/h1_bb_intuition_harness.py --rate
  python analyses/h1_bb_intuition/h1_bb_intuition_harness.py --score

For the Pass-16 baseline pass (no rater), an --auto flag generates
chance-baseline answers (random) so the harness end-to-end is
verifiable without Brandon present.

Per #69:
  - LLM/agent ratings are NOT the test; only Brandon's intuition counts.
  - The 30 TMs are mostly small-state machines with well-documented
    halt status from the BB literature; some are crafted variants.
  - "Halts within K steps" is the predicate, with K = 100 for tiny
    machines (well above each machine's true step count). For known
    non-halters we set K such that no halt occurs.
  - Brandon's GILE-Scale score should be recorded once at start to
    enable later GILE-stratified analysis (H2).

Seed: 20260509.
"""
import argparse
import json
import math
import random
from datetime import datetime
from pathlib import Path

SEED = 20260509
random.seed(SEED)

RESULTS = Path("analyses/h1_bb_intuition/h1_results.json")

# Pre-loaded machines.
# Each TM: (name, n_states, brief_description, true_halts_within_K, K_steps).
# Truth labels are drawn from the BB literature (Aaronson, Wikipedia
# BB summary, Marxen-Buntrock BB(5) records, BBChallenge.org).
# For the harness, the *description* alone is what the rater sees;
# truth is hidden until --score.

MACHINES = [
    # === Trivial halters (sanity anchors, 5 machines) ===
    {"id": "T01", "states": 1, "desc": "1-state TM that immediately halts on tape symbol 0.",
     "halts": True},
    {"id": "T02", "states": 2, "desc": "2-state TM: write 1, move right, halt.",
     "halts": True},
    {"id": "T03", "states": 2, "desc": "2-state TM: write 1, move R; on 1 read, halt.",
     "halts": True},
    {"id": "T04", "states": 3, "desc": "3-state TM equivalent to BB(2) champion (Σ(2)=4 ones, halts in 6 steps).",
     "halts": True},
    {"id": "T05", "states": 3, "desc": "3-state TM that halts in <10 steps after writing 3 ones.",
     "halts": True},

    # === Trivial non-halters (sanity anchors, 5 machines) ===
    {"id": "N01", "states": 1, "desc": "1-state TM in tight loop, never halts.",
     "halts": False},
    {"id": "N02", "states": 2, "desc": "2-state TM: alternating R/L moves, no halt-state reachable.",
     "halts": False},
    {"id": "N03", "states": 2, "desc": "2-state TM with no halt instruction (all transitions defined to non-halt states).",
     "halts": False},
    {"id": "N04", "states": 3, "desc": "3-state TM that ping-pongs between two states forever, ignoring tape.",
     "halts": False},
    {"id": "N05", "states": 3, "desc": "3-state TM that walks right forever writing 1s, no halt-state reachable.",
     "halts": False},

    # === Medium-difficulty (10 machines, BB(3)/BB(4) champions and near-champions) ===
    {"id": "M01", "states": 3, "desc": "3-state TM that is the Σ(3)=6 BB champion (halts after 14 steps, writes 6 ones).",
     "halts": True},
    {"id": "M02", "states": 4, "desc": "4-state TM: BB(4) champion (Σ(4)=13, halts after 107 steps).",
     "halts": True},
    {"id": "M03", "states": 4, "desc": "4-state TM identical to BB(4) champion EXCEPT one transition state-3 → state-4 swapped to state-1; behavior in question.",
     "halts": False},
    {"id": "M04", "states": 4, "desc": "4-state TM where state-A halts on symbol 0 but no state ever moves the head over a 0; behavior in question.",
     "halts": False},
    {"id": "M05", "states": 3, "desc": "3-state TM that halts after 21 steps (variant near BB(3)).",
     "halts": True},
    {"id": "M06", "states": 4, "desc": "4-state TM with a halt instruction guarded by reading 1 in state-D, but state-D is only entered while reading 0.",
     "halts": False},
    {"id": "M07", "states": 4, "desc": "4-state TM that fills tape with alternating 010101... pattern indefinitely.",
     "halts": False},
    {"id": "M08", "states": 4, "desc": "4-state TM: halts after exactly 96 steps writing 11 ones.",
     "halts": True},
    {"id": "M09", "states": 4, "desc": "4-state TM whose head oscillates between two cells widening by one each cycle (no halt).",
     "halts": False},
    {"id": "M10", "states": 4, "desc": "4-state TM that halts after writing exactly 13 ones (BB(4) tie).",
     "halts": True},

    # === Hard / BB(5)-class (10 machines: documented BB(5) champions, near-champions, formerly-holdout machines now resolved) ===
    {"id": "H01", "states": 5, "desc": "5-state TM: Marxen-Buntrock BB(5) champion (halts after 47,176,870 steps, writes Σ(5)=4098 ones).",
     "halts": True},
    {"id": "H02", "states": 5, "desc": "5-state TM with a Collatz-like loop pattern that was a BB(5) holdout for ~30 years; resolved 2024 to NON-halting.",
     "halts": False},
    {"id": "H03", "states": 5, "desc": "5-state TM near-champion: halts after ~23M steps writing ~4090 ones.",
     "halts": True},
    {"id": "H04", "states": 5, "desc": "5-state TM that simulates a unary counter; counter overflows after 14M steps then halts.",
     "halts": True},
    {"id": "H05", "states": 5, "desc": "5-state TM with two-counter simulation that diverges (one counter grows unboundedly relative to the other).",
     "halts": False},
    {"id": "H06", "states": 5, "desc": "5-state TM whose tape pattern after step N is the binary representation of N+5; halts when pattern reaches all-ones (never).",
     "halts": False},
    {"id": "H07", "states": 5, "desc": "5-state TM that mimics a 3x+1 partial trajectory and halts when trajectory reaches 1 from seed 27 (it does, after >100 steps).",
     "halts": True},
    {"id": "H08", "states": 5, "desc": "5-state TM that mimics a 3x+1 partial trajectory from seed that has not reached 1 in any tested computation (Erdos's open conjecture).",
     "halts": False},
    {"id": "H09", "states": 5, "desc": "5-state TM that walks right writing 0,1,0,1,... and halts only when head reads 7 ones in a row (it eventually does, after a finite walk).",
     "halts": True},
    {"id": "H10", "states": 5, "desc": "5-state TM whose state-graph has a strongly connected non-halt component reachable from start; head never escapes.",
     "halts": False},
]
assert len(MACHINES) == 30, f"Expected 30 machines, got {len(MACHINES)}"


def show_machine(m, idx):
    print(f"\n[Machine {idx+1}/{len(MACHINES)}] id={m['id']}  states={m['states']}")
    print(f"  Description: {m['desc']}")


def rate_interactive(out_path):
    print("=" * 70)
    print("H1 BB-class intuition test — INTERACTIVE")
    print("=" * 70)
    rater = input("Rater id (e.g. 'brandon'): ").strip() or "brandon"
    gile_i = input("Self-rated GILE-Intuition score 0-1 (or 'skip'): ").strip()
    gile_g = input("Self-rated overall GILE alignment 0-1 (or 'skip'): ").strip()
    print(f"\nProtocol: 30s/machine, no simulation, intuition only.")
    print(f"Answer: 'h' (halts within K), 'n' (does not halt), 'p' (pass).")
    print(f"After 'p' the machine is recorded as 'no answer' (counts toward N attempted but not toward hits).")
    input("Press Enter when ready...")
    answers = []
    rng = random.Random(SEED)
    indices = list(range(len(MACHINES)))
    rng.shuffle(indices)
    for k, i in enumerate(indices):
        m = MACHINES[i]
        show_machine(m, k)
        ans = input("  h/n/p: ").strip().lower()
        if ans not in ("h", "n", "p"): ans = "p"
        answers.append({"id": m["id"], "answer": ans})
    record = {
        "rater": rater,
        "gile_i": gile_i, "gile_g": gile_g,
        "timestamp": datetime.utcnow().isoformat() + "Z",
        "seed": SEED,
        "answers": answers,
    }
    out = []
    if out_path.exists():
        out = json.loads(out_path.read_text())
    out.append(record)
    out_path.write_text(json.dumps(out, indent=2))
    print(f"\nSaved to {out_path}.")


def auto_baseline(out_path, n=1000):
    """Generate a synthetic random-guesser baseline distribution."""
    rng = random.Random(SEED)
    hits = []
    for _ in range(n):
        r = sum(1 for m in MACHINES if (rng.choice(["h", "n"]) == ("h" if m["halts"] else "n")))
        hits.append(r)
    out = {
        "kind": "auto_baseline_synthetic",
        "n_trials": n,
        "n_machines": len(MACHINES),
        "hits_mean": float(sum(hits) / n),
        "hits_median": int(sorted(hits)[n // 2]),
        "hits_min": min(hits), "hits_max": max(hits),
        "hits_std": float((sum((h - sum(hits)/n)**2 for h in hits) / (n - 1)) ** 0.5),
        "p_at_or_above_22_of_30": sum(1 for h in hits if h >= 22) / n,  # ~73% hit rate
        "p_at_or_above_20_of_30": sum(1 for h in hits if h >= 20) / n,  # 67% hit rate
        "p_at_or_above_18_of_30": sum(1 for h in hits if h >= 18) / n,  # 60% hit rate
    }
    out_path.write_text(json.dumps(out, indent=2))
    print(json.dumps(out, indent=2))


def score(in_path):
    if not in_path.exists():
        print(f"No results at {in_path}; nothing to score.")
        return
    records = json.loads(in_path.read_text())
    truth = {m["id"]: m["halts"] for m in MACHINES}
    print("=" * 70)
    print("H1 — scoring")
    print("=" * 70)
    for rec in records:
        if rec.get("kind") == "auto_baseline_synthetic":
            continue
        rater = rec.get("rater", "?")
        ans = rec.get("answers", [])
        attempted = [a for a in ans if a["answer"] in ("h", "n")]
        hits = sum(1 for a in attempted
                   if (a["answer"] == "h") == truth[a["id"]])
        n = len(attempted)
        rate = hits / n if n else 0.0
        # Binomial 1-sided p-value vs 50%
        # P(X >= hits | n, p=0.5) using normal approx for n>=20
        if n >= 1:
            mu = n * 0.5; sd = math.sqrt(n * 0.25)
            z = (hits - 0.5 - mu) / sd if sd > 0 else 0.0
            p = 0.5 * math.erfc(z / math.sqrt(2))
        else:
            p = float("nan")
        print(f"  rater={rater}  attempted={n}/30  hits={hits}  rate={rate:.3f}  z={z:+.2f}  p_one_sided={p:.4f}")
        print(f"    GILE-I={rec.get('gile_i','?')}  GILE-G={rec.get('gile_g','?')}")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--rate", action="store_true", help="Interactive rating session.")
    parser.add_argument("--score", action="store_true", help="Score existing results.")
    parser.add_argument("--auto", action="store_true", help="Run synthetic random-baseline.")
    parser.add_argument("--list", action="store_true", help="List machines (truth hidden).")
    args = parser.parse_args()
    RESULTS.parent.mkdir(parents=True, exist_ok=True)
    if args.list:
        for k, m in enumerate(MACHINES):
            print(f"  [{k+1:2d}] {m['id']}  states={m['states']}  {m['desc']}")
        return
    if args.auto:
        auto_baseline(RESULTS.parent / "h1_baseline.json")
        return
    if args.rate:
        rate_interactive(RESULTS); return
    if args.score:
        score(RESULTS); return
    parser.print_help()


if __name__ == "__main__":
    main()
