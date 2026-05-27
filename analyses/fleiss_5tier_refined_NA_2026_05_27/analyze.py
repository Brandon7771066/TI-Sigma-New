"""Pass-77-B30 analyzer: Fleiss κ + per-cat accuracy + MI battery + silhouette,
on refined-NA 5-tier system. Integrate with B26/B27 binary baseline."""
import json, math
from collections import Counter
from itertools import combinations
from pathlib import Path

D = Path(__file__).parent
B26 = Path("analyses/fleiss_binary_vs_5tier_1000_2026_05_27")
test_set = {p["id"]: p for p in json.load(open(D/"test_set.json"))}
ratings = json.load(open(D/"ratings.json"))

# Filter gold only
def to_gold(rows):
    return [r for r in rows if r["gold"] in ("T","F","I","MI","NA")]

# ============ Fleiss κ ============
def fleiss_kappa(rows, labels):
    """rows: list of dicts with 'ratings' (rater_name -> label). labels = label set used."""
    N = len(rows)
    if N == 0: return 0.0
    L = list(labels)
    counts = []
    n_rater = None
    for r in rows:
        rv = [v for v in r["ratings"].values() if v in labels]
        if n_rater is None: n_rater = len(rv)
        if len(rv) < 2: continue
        c = [rv.count(l) for l in L]
        counts.append(c)
    n = max(sum(c) for c in counts)
    p_bar_e = [sum(c[j] for c in counts) / (len(counts) * n) for j in range(len(L))]
    Pe = sum(p*p for p in p_bar_e)
    P_i = [(sum(ci*ci for ci in c) - n) / (n*(n-1)) for c in counts]
    P_bar = sum(P_i) / len(counts)
    if Pe == 1.0: return 1.0
    return (P_bar - Pe) / (1 - Pe)

# ============ Per-cat accuracy via majority vote ============
def per_cat_accuracy(rows, labels):
    cats = Counter(r["gold"] for r in rows)
    correct = Counter()
    confusion = {g: Counter() for g in cats}
    for r in rows:
        rv = [v for v in r["ratings"].values() if v in labels]
        if len(rv) < 2: continue
        maj = Counter(rv).most_common(1)[0][0]
        if maj == r["gold"]: correct[r["gold"]] += 1
        confusion[r["gold"]][maj] += 1
    return {g: (correct[g], cats[g]) for g in cats}, confusion

# ============ MI battery ============
def entropy(counts):
    total = sum(counts)
    if total == 0: return 0.0
    return -sum((c/total)*math.log2(c/total) for c in counts if c > 0)

def joint_entropy(pairs):
    total = len(pairs)
    if total == 0: return 0.0
    c = Counter(pairs)
    return -sum((v/total)*math.log2(v/total) for v in c.values())

def mi_battery(rows, labels, n_perm=200, seed=0):
    """Returns dict of metrics computed from majority-vote rater label vs gold."""
    import random
    rng = random.Random(seed)
    pairs = []
    for r in rows:
        rv = [v for v in r["ratings"].values() if v in labels]
        if len(rv) < 2: continue
        maj = Counter(rv).most_common(1)[0][0]
        pairs.append((r["gold"], maj))
    n = len(pairs)
    golds = [p[0] for p in pairs]
    raters = [p[1] for p in pairs]
    realized_alphabet = sorted(set(raters))
    Hg = entropy(list(Counter(golds).values()))
    Hr = entropy(list(Counter(raters).values()))
    Hgr = joint_entropy(pairs)
    MI = Hg + Hr - Hgr
    NMI = MI / math.sqrt(Hg * Hr) if Hg > 0 and Hr > 0 else 0.0
    # AMI via permutation
    perm_MIs = []
    for _ in range(n_perm):
        shuffled = list(raters); rng.shuffle(shuffled)
        sp = list(zip(golds, shuffled))
        Hsg = entropy(list(Counter(golds).values()))
        Hsr = entropy(list(Counter(shuffled).values()))
        Hsgr = joint_entropy(sp)
        perm_MIs.append(Hsg + Hsr - Hsgr)
    E_MI = sum(perm_MIs) / len(perm_MIs)
    max_H = max(Hg, Hr)
    AMI = (MI - E_MI) / (max_H - E_MI) if max_H > E_MI else 0.0
    # ARI
    def ari(pairs):
        from collections import defaultdict
        contingency = defaultdict(int)
        for a, b in pairs: contingency[(a,b)] += 1
        ai = Counter(p[0] for p in pairs); bj = Counter(p[1] for p in pairs)
        N = len(pairs)
        def comb2(x): return x*(x-1)//2
        sum_nij = sum(comb2(v) for v in contingency.values())
        sum_ai = sum(comb2(v) for v in ai.values())
        sum_bj = sum(comb2(v) for v in bj.values())
        denom_index = comb2(N)
        if denom_index == 0: return 0.0
        expected = sum_ai * sum_bj / denom_index
        max_index = (sum_ai + sum_bj) / 2
        if max_index == expected: return 0.0
        return (sum_nij - expected) / (max_index - expected)
    ARI = ari(pairs)
    # Theil U
    U_gr = MI / Hg if Hg > 0 else 0.0
    U_rg = MI / Hr if Hr > 0 else 0.0
    # Cramer's V
    from collections import defaultdict
    contingency = defaultdict(int)
    for a,b in pairs: contingency[(a,b)] += 1
    ai = Counter(p[0] for p in pairs); bj = Counter(p[1] for p in pairs)
    chi2 = 0.0
    for a in ai:
        for b in bj:
            o = contingency.get((a,b), 0)
            e = ai[a] * bj[b] / n
            if e > 0: chi2 += (o-e)**2 / e
    V = math.sqrt(chi2 / (n * min(len(ai)-1, len(bj)-1))) if min(len(ai)-1, len(bj)-1) > 0 else 0.0
    return {
        "n": n,
        "alphabet_realized": realized_alphabet,
        "channel_capacity_bits": math.log2(len(realized_alphabet)) if len(realized_alphabet) > 0 else 0.0,
        "H_gold": Hg, "H_rater": Hr, "H_joint": Hgr,
        "MI_bits": MI, "NMI": NMI, "AMI": AMI, "ARI": ARI,
        "Theil_U_gold_given_rater": U_gr, "Theil_U_rater_given_gold": U_rg,
        "Cramers_V": V,
    }

# ============ Silhouette via Hamming on 3-rater tuple ============
def silhouette(rows, labels):
    # Build points: each prop -> (gold, tuple of 3 rater labels)
    pts = []
    for r in rows:
        rv = tuple(r["ratings"].get(k) for k in sorted(r["ratings"].keys()))
        if any(v is None for v in rv): continue
        if any(v not in labels for v in rv): continue
        pts.append((r["gold"], rv))
    def hamming(a, b):
        return sum(1 for x,y in zip(a,b) if x != y) / len(a)
    golds = sorted(set(p[0] for p in pts))
    per_gold = {g: [] for g in golds}
    sils_by_gold = {g: [] for g in golds}
    for i, (gi, vi) in enumerate(pts):
        # a = mean intra-cluster
        intra = [hamming(vi, vj) for j,(gj,vj) in enumerate(pts) if j != i and gj == gi]
        a = sum(intra)/len(intra) if intra else 0.0
        # b = min over other clusters of mean inter-cluster distance
        b = float("inf")
        for g in golds:
            if g == gi: continue
            inter = [hamming(vi, vj) for (gj,vj) in pts if gj == g]
            if inter:
                mean_inter = sum(inter)/len(inter)
                if mean_inter < b: b = mean_inter
        if b == float("inf"): b = 0.0
        s = (b - a) / max(a, b) if max(a, b) > 0 else 0.0
        sils_by_gold[gi].append(s)
    mean_all = sum(s for g in sils_by_gold for s in sils_by_gold[g]) / sum(len(v) for v in sils_by_gold.values())
    per_gold_mean = {g: (sum(sils_by_gold[g])/len(sils_by_gold[g]) if sils_by_gold[g] else 0.0) for g in golds}
    return mean_all, per_gold_mean

# =========================
LABELS_5 = {"T","F","I","MI","NA"}

gold_rows = to_gold(ratings)
print(f"\n========== Pass-77-B30: REFINED 5-TIER (n={len(gold_rows)} gold props) ==========")
print(f"\n--- Fleiss κ ---")
k_all = fleiss_kappa(gold_rows, LABELS_5)
print(f"  Fleiss κ (all gold)     = {k_all:.4f}")
# Per-NA-subgold κ
for sg in ("NA-FUT","NA-PST","NA-PRE","NA-CAT"):
    sub = [r for r in gold_rows if r.get("subgold") == sg]
    if sub:
        ks = fleiss_kappa(sub, LABELS_5)
        print(f"  Fleiss κ ({sg}, n={len(sub):>3})  = {ks:.4f}")

print(f"\n--- Per-category accuracy (majority vote) ---")
acc, conf = per_cat_accuracy(gold_rows, LABELS_5)
for g in ("T","F","I","MI","NA"):
    if g in acc:
        c, t = acc[g]
        print(f"  {g:3} : {c:>3}/{t:<3}  ({100*c/t:.1f}%)")
print(f"\n  Confusion matrix (rows=gold, cols=majority rater label):")
print(f"  {'gold':>5} | " + " ".join(f"{l:>4}" for l in ("T","F","I","MI","NA")))
for g in ("T","F","I","MI","NA"):
    if g in conf:
        row = " ".join(f"{conf[g].get(l,0):>4}" for l in ("T","F","I","MI","NA"))
        print(f"  {g:>5} | {row}")

print(f"\n--- NA sub-cell accuracy (majority vote, gold=NA broken out) ---")
for sg in ("NA-FUT","NA-PST","NA-PRE","NA-CAT"):
    sub = [r for r in gold_rows if r.get("subgold") == sg]
    if not sub: continue
    correct = 0; sub_conf = Counter()
    for r in sub:
        rv = [v for v in r["ratings"].values() if v in LABELS_5]
        if len(rv) < 2: continue
        maj = Counter(rv).most_common(1)[0][0]
        sub_conf[maj] += 1
        if maj == "NA": correct += 1
    print(f"  {sg:8} : {correct:>2}/{len(sub):<2}  ({100*correct/len(sub):.1f}%) — labels: {dict(sub_conf)}")

print(f"\n--- MI battery (gold n={len(gold_rows)}, 200 perms for AMI) ---")
mi5 = mi_battery(gold_rows, LABELS_5)
for k,v in mi5.items():
    print(f"  {k:32} = {v}" if isinstance(v, (str,list)) else f"  {k:32} = {v:.4f}")

print(f"\n--- Silhouette (Hamming on 3-rater tuple) ---")
sm, per_g = silhouette(gold_rows, LABELS_5)
print(f"  mean silhouette = {sm:+.4f}")
for g in sorted(per_g):
    print(f"    gold={g:3}: {per_g[g]:+.4f}")

# =========================
# Integrate with B26 binary baseline
# =========================
print(f"\n\n========== INTEGRATION: B26 BINARY vs B30 REFINED 5-TIER ==========")
b26_binary_rows = to_gold(json.load(open(B26/"ratings_binary.json")))
# binary κ on same gold structure as B26 (T,F,I,MI,NA all map to forced T/F)
LABELS_2 = {"T","F"}
binary_k = fleiss_kappa(b26_binary_rows, LABELS_2)
binary_acc, _ = per_cat_accuracy(b26_binary_rows, LABELS_2)
binary_mi = mi_battery(b26_binary_rows, LABELS_2)
binary_sm, binary_per_g = silhouette(b26_binary_rows, LABELS_2)
print(f"\n  metric                          binary(B26)   5tier_refined(B30)   delta")
print(f"  {'Fleiss κ (gold)':<30}  {binary_k:>10.4f}   {k_all:>18.4f}   {k_all-binary_k:+.4f}")
print(f"  {'I(gold;rater) bits':<30}  {binary_mi['MI_bits']:>10.4f}   {mi5['MI_bits']:>18.4f}   {mi5['MI_bits']-binary_mi['MI_bits']:+.4f}")
print(f"  {'NMI':<30}  {binary_mi['NMI']:>10.4f}   {mi5['NMI']:>18.4f}   {mi5['NMI']-binary_mi['NMI']:+.4f}")
print(f"  {'AMI':<30}  {binary_mi['AMI']:>10.4f}   {mi5['AMI']:>18.4f}   {mi5['AMI']-binary_mi['AMI']:+.4f}")
print(f"  {'ARI':<30}  {binary_mi['ARI']:>10.4f}   {mi5['ARI']:>18.4f}   {mi5['ARI']-binary_mi['ARI']:+.4f}")
print(f"  {'Theil U(gold|rater)':<30}  {binary_mi['Theil_U_gold_given_rater']:>10.4f}   {mi5['Theil_U_gold_given_rater']:>18.4f}   {mi5['Theil_U_gold_given_rater']-binary_mi['Theil_U_gold_given_rater']:+.4f}")
print(f"  {'Cramers V':<30}  {binary_mi['Cramers_V']:>10.4f}   {mi5['Cramers_V']:>18.4f}   {mi5['Cramers_V']-binary_mi['Cramers_V']:+.4f}")
print(f"  {'Silhouette mean':<30}  {binary_sm:>10.4f}   {sm:>18.4f}   {sm-binary_sm:+.4f}")

results = {
    "n_gold_5tier_refined": len(gold_rows),
    "fleiss_kappa_5tier_refined_gold": k_all,
    "fleiss_kappa_per_NA_subgold": {sg: fleiss_kappa([r for r in gold_rows if r.get("subgold")==sg], LABELS_5) for sg in ("NA-FUT","NA-PST","NA-PRE","NA-CAT")},
    "per_cat_accuracy": {g: list(acc[g]) for g in acc},
    "confusion": {g: dict(conf[g]) for g in conf},
    "NA_subcell_accuracy": {sg: sum(1 for r in gold_rows if r.get("subgold")==sg and Counter([v for v in r["ratings"].values() if v in LABELS_5]).most_common(1)[0][0]=="NA")/max(1,sum(1 for r in gold_rows if r.get("subgold")==sg)) for sg in ("NA-FUT","NA-PST","NA-PRE","NA-CAT")},
    "MI_battery_5tier_refined": mi5,
    "silhouette_5tier_refined": {"mean": sm, "per_gold": per_g},
    "binary_baseline_B26": {
        "fleiss_kappa": binary_k,
        "per_cat_accuracy": {g: list(binary_acc[g]) for g in binary_acc},
        "MI_battery": binary_mi,
        "silhouette_mean": binary_sm,
        "silhouette_per_gold": binary_per_g,
    },
}
json.dump(results, open(D/"results.json","w"), indent=2, default=str)
print(f"\nResults written to {D/'results.json'}")
