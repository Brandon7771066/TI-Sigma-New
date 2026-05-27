"""
Pass-77-B25 analysis: Fleiss kappa + per-category accuracy + confusion matrices.
Compares binary {T,F} vs 5-tier {T,F,I,MI,NA} rating systems on 1000 statements
(500 random Tatoeba casual speech + 500 gold-labeled 100/cat).
"""
import json
from collections import Counter, defaultdict

DIR = "analyses/fleiss_binary_vs_5tier_1000_2026_05_27"

def fleiss_kappa(table, n_raters):
    """table: list of dicts category -> count (sums to n_raters per row)."""
    N = len(table)
    cats = sorted({c for row in table for c in row})
    # P_i for each item
    P_is = []
    for row in table:
        s = sum(c * (c - 1) for c in row.values())
        P_is.append(s / (n_raters * (n_raters - 1)))
    P_bar = sum(P_is) / N
    # marginal probability of each category
    totals = Counter()
    for row in table:
        for c, n in row.items():
            totals[c] += n
    Pe = sum((totals[c] / (N * n_raters)) ** 2 for c in cats)
    if Pe >= 1:
        return float('nan'), P_bar, Pe
    return (P_bar - Pe) / (1 - Pe), P_bar, Pe

def analyze(mode, valid_set):
    with open(f"{DIR}/ratings_{mode}.json") as f:
        rows = json.load(f)
    # Filter: keep rows where all 3 raters returned valid labels
    clean = []
    dropped = 0
    for r in rows:
        rats = list(r["ratings"].values())
        if all(v in valid_set for v in rats) and len(rats) == 3:
            clean.append(r)
        else:
            dropped += 1
    print(f"\n=== MODE: {mode} ===")
    print(f"Total: {len(rows)}, clean (all 3 raters valid): {len(clean)}, dropped: {dropped}")

    # Overall kappa
    table = []
    for r in clean:
        counts = Counter(r["ratings"].values())
        table.append({c: counts.get(c, 0) for c in valid_set})
    kappa, P_bar, Pe = fleiss_kappa(table, 3)
    print(f"Overall Fleiss kappa (n={len(clean)}): k={kappa:.4f}  P_bar={P_bar:.4f}  Pe={Pe:.4f}")

    # Kappa on random-casual subset (no gold label)
    casual_rows = [r for r in clean if r["gold"] == "CASUAL"]
    table_c = [{c: Counter(r["ratings"].values()).get(c, 0) for c in valid_set} for r in casual_rows]
    if casual_rows:
        kappa_c, _, _ = fleiss_kappa(table_c, 3)
        print(f"Random/casual subset kappa (n={len(casual_rows)}): k={kappa_c:.4f}")

    # Kappa on gold subset
    gold_rows = [r for r in clean if r["gold"] != "CASUAL"]
    table_g = [{c: Counter(r["ratings"].values()).get(c, 0) for c in valid_set} for r in gold_rows]
    if gold_rows:
        kappa_g, _, _ = fleiss_kappa(table_g, 3)
        print(f"Gold-labeled subset kappa (n={len(gold_rows)}): k={kappa_g:.4f}")

    # Per-category accuracy on gold (majority vote)
    print(f"\nPer-category majority-vote accuracy (gold subset):")
    cat_correct = defaultdict(int)
    cat_total = defaultdict(int)
    confusion = defaultdict(lambda: Counter())
    for r in gold_rows:
        counts = Counter(r["ratings"].values())
        majority = counts.most_common(1)[0][0]
        cat_total[r["gold"]] += 1
        confusion[r["gold"]][majority] += 1
        if mode == "binary":
            # For binary mode, gold T/F are directly comparable; I/MI/NA cannot match by definition
            if r["gold"] == majority:
                cat_correct[r["gold"]] += 1
        else:
            if r["gold"] == majority:
                cat_correct[r["gold"]] += 1
    for gold_cat in sorted(cat_total.keys()):
        acc = cat_correct[gold_cat] / cat_total[gold_cat] if cat_total[gold_cat] else 0
        print(f"  gold={gold_cat:5s} n={cat_total[gold_cat]:3d}  correct={cat_correct[gold_cat]:3d}  acc={acc:.3f}")

    # Confusion matrix (gold rows only)
    print(f"\nConfusion matrix (gold rows, rows=gold, cols=majority-vote rater label):")
    print(f"  {'gold':>5s} | " + "  ".join(f"{c:>4s}" for c in sorted(valid_set)))
    for gold_cat in sorted(confusion.keys()):
        cells = "  ".join(f"{confusion[gold_cat].get(c, 0):>4d}" for c in sorted(valid_set))
        print(f"  {gold_cat:>5s} | {cells}")

    # Rater distribution
    print(f"\nRater label distribution (all clean rows):")
    rater_dist = defaultdict(Counter)
    for r in clean:
        for rname, label in r["ratings"].items():
            rater_dist[rname][label] += 1
    for rname in sorted(rater_dist.keys()):
        print(f"  {rname}: " + ", ".join(f"{c}={rater_dist[rname][c]}" for c in sorted(valid_set)))

    return {
        "mode": mode,
        "n_clean": len(clean),
        "n_dropped": dropped,
        "kappa_overall": kappa,
        "kappa_casual": kappa_c if casual_rows else None,
        "kappa_gold": kappa_g if gold_rows else None,
        "per_cat_accuracy": {k: cat_correct[k] / cat_total[k] for k in cat_total},
        "per_cat_n": dict(cat_total),
        "confusion": {k: dict(v) for k, v in confusion.items()},
        "rater_distribution": {k: dict(v) for k, v in rater_dist.items()},
    }

results = {}
results["binary"] = analyze("binary", {"T", "F"})
results["5tier"] = analyze("5tier", {"T", "F", "I", "MI", "NA"})

with open(f"{DIR}/results.json", "w") as f:
    json.dump(results, f, indent=2)

print("\n=== COMPARISON ===")
print(f"  Overall kappa:  binary={results['binary']['kappa_overall']:.4f}  5tier={results['5tier']['kappa_overall']:.4f}")
print(f"  Casual kappa:   binary={results['binary']['kappa_casual']:.4f}  5tier={results['5tier']['kappa_casual']:.4f}")
print(f"  Gold kappa:     binary={results['binary']['kappa_gold']:.4f}  5tier={results['5tier']['kappa_gold']:.4f}")
print(f"\nWritten to {DIR}/results.json")
