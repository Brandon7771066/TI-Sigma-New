"""Pass-77-B31 unified analyzer: compare 5-tier (B30) vs LP (Priest) vs FDE
(Belnap-Dunn) vs binary (B26 baseline). Same 500 gold props throughout.

Two analytic layers:
  (a) Within-system: Fleiss κ on raters; per-cat accuracy vs system-specific
      gold mapping.
  (b) Uniform comparator: MI(5-tier-gold; rater-majority), AMI, ARI, silhouette
      via Hamming on 3-rater tuple. Uniform = same gold (the 5-tier gold), each
      system gets credit for whatever truth-spectrum info its rater output
      preserves about the underlying 5-tier ground truth.
"""
import json, math
from collections import Counter, defaultdict
from itertools import combinations
from pathlib import Path
import random

D = Path(__file__).parent
B30 = Path("analyses/fleiss_5tier_refined_NA_2026_05_27")
B26 = Path("analyses/fleiss_binary_vs_5tier_1000_2026_05_27")

ratings_5tier = json.load(open(B30/"ratings.json"))
ratings_lp = json.load(open(D/"ratings_lp.json"))
ratings_fde = json.load(open(D/"ratings_fde.json"))
# Reuse B26 binary, but only on the same 500 props (B30 reused B26's T/F/I/MI ids).
binary_all = json.load(open(B26/"ratings_binary.json"))
gold_ids = {r["id"] for r in ratings_5tier}
ratings_binary = [r for r in binary_all if r["id"] in gold_ids]

# Sanity
print(f"n: 5tier={len(ratings_5tier)} LP={len(ratings_lp)} FDE={len(ratings_fde)} bin(B26∩B30)={len(ratings_binary)}")

# =========================================================
# System-specific gold mapping for within-system accuracy
# =========================================================
# 5-tier gold -> what each rival system's "correct" answer should be:
GOLD_MAP = {
    "5TIER":  {"T":"T", "F":"F", "I":"I", "MI":"MI", "NA":"NA"},
    "LP":     {"T":"T", "F":"F", "I":"F",  "MI":"B",  "NA":"F"},
    "FDE":    {"T":"T", "F":"F", "I":"N",  "MI":"BO", "NA":"N"},
    "BIN":    {"T":"T", "F":"F", "I":"F",  "MI":"F",  "NA":"F"},
}
SYS_LABELS = {
    "5TIER": {"T","F","I","MI","NA"},
    "LP":    {"T","F","B"},
    "FDE":   {"T","F","BO","N"},
    "BIN":   {"T","F"},
}

# =========================================================
# Metrics
# =========================================================
def majority(d, labels):
    rv = [v for v in d.values() if v in labels]
    if len(rv) < 2: return None
    return Counter(rv).most_common(1)[0][0]

def fleiss_kappa(rows, labels):
    L = list(labels)
    counts = []
    n_per = None
    for r in rows:
        rv = [v for v in r["ratings"].values() if v in labels]
        if len(rv) < 2: continue
        if n_per is None: n_per = len(rv)
        c = [rv.count(l) for l in L]
        counts.append(c)
    if not counts: return 0.0
    n = max(sum(c) for c in counts)
    p_bar_e = [sum(c[j] for c in counts) / (len(counts) * n) for j in range(len(L))]
    Pe = sum(p*p for p in p_bar_e)
    P_i = [(sum(ci*ci for ci in c) - n) / (n*(n-1)) for c in counts]
    P_bar = sum(P_i) / len(counts)
    return (P_bar - Pe) / (1 - Pe) if Pe < 1 else 1.0

def per_cat_accuracy(rows, labels, gold_map):
    """gold_map: 5-tier gold -> system-specific 'correct' label."""
    cats = Counter(r["gold"] for r in rows)
    correct = Counter()
    for r in rows:
        maj = majority(r["ratings"], labels)
        if maj is None: continue
        expected = gold_map.get(r["gold"])
        if maj == expected: correct[r["gold"]] += 1
    return {g: (correct[g], cats[g]) for g in cats}

def entropy(counts):
    total = sum(counts)
    if total == 0: return 0.0
    return -sum((c/total)*math.log2(c/total) for c in counts if c > 0)

def joint_entropy(pairs):
    total = len(pairs)
    if total == 0: return 0.0
    c = Counter(pairs)
    return -sum((v/total)*math.log2(v/total) for v in c.values())

def mi_uniform(rows, labels, n_perm=200, seed=0):
    """Uniform comparator: I(5-tier-gold ; rater-majority-under-system)."""
    rng = random.Random(seed)
    pairs = []
    for r in rows:
        maj = majority(r["ratings"], labels)
        if maj is None: continue
        pairs.append((r["gold"], maj))
    n = len(pairs)
    if n == 0:
        return {"n":0,"MI_bits":0,"NMI":0,"AMI":0,"ARI":0,"Theil_U_gold_given_rater":0,"Cramers_V":0,"channel_capacity_bits":0,"H_gold":0,"H_rater":0,"alphabet_realized":[]}
    golds = [p[0] for p in pairs]
    raters = [p[1] for p in pairs]
    alphabet = sorted(set(raters))
    Hg = entropy(list(Counter(golds).values()))
    Hr = entropy(list(Counter(raters).values()))
    Hgr = joint_entropy(pairs)
    MI = Hg + Hr - Hgr
    NMI = MI / math.sqrt(Hg * Hr) if Hg > 0 and Hr > 0 else 0.0
    perm_MIs = []
    for _ in range(n_perm):
        sh = list(raters); rng.shuffle(sh)
        sp = list(zip(golds, sh))
        Hsr = entropy(list(Counter(sh).values()))
        Hsgr = joint_entropy(sp)
        perm_MIs.append(Hg + Hsr - Hsgr)
    E_MI = sum(perm_MIs)/len(perm_MIs)
    AMI = (MI - E_MI) / (max(Hg, Hr) - E_MI) if max(Hg, Hr) > E_MI else 0.0
    # ARI
    contingency = defaultdict(int)
    for a,b in pairs: contingency[(a,b)] += 1
    ai = Counter(p[0] for p in pairs); bj = Counter(p[1] for p in pairs)
    def comb2(x): return x*(x-1)//2
    sum_nij = sum(comb2(v) for v in contingency.values())
    sum_ai = sum(comb2(v) for v in ai.values())
    sum_bj = sum(comb2(v) for v in bj.values())
    denom = comb2(n)
    expected = sum_ai*sum_bj/denom if denom else 0
    maxidx = (sum_ai+sum_bj)/2
    ARI = (sum_nij - expected)/(maxidx - expected) if maxidx != expected else 0.0
    # Theil U
    U_gr = MI/Hg if Hg > 0 else 0.0
    # Cramer V
    chi2 = 0.0
    for a in ai:
        for b in bj:
            o = contingency.get((a,b),0)
            e = ai[a]*bj[b]/n
            if e > 0: chi2 += (o-e)**2/e
    V = math.sqrt(chi2/(n*min(len(ai)-1,len(bj)-1))) if min(len(ai)-1,len(bj)-1) > 0 else 0.0
    return {
        "n":n, "alphabet_realized":alphabet, "channel_capacity_bits":math.log2(len(alphabet)) if alphabet else 0.0,
        "H_gold":Hg, "H_rater":Hr,
        "MI_bits":MI, "NMI":NMI, "AMI":AMI, "ARI":ARI,
        "Theil_U_gold_given_rater":U_gr, "Cramers_V":V,
    }

def silhouette(rows, labels):
    pts = []
    for r in rows:
        rv = tuple(r["ratings"].get(k) for k in sorted(r["ratings"].keys()))
        if any(v is None for v in rv) or any(v not in labels for v in rv): continue
        pts.append((r["gold"], rv))
    if not pts: return 0.0, {}
    def hamming(a,b): return sum(1 for x,y in zip(a,b) if x != y)/len(a)
    golds = sorted(set(p[0] for p in pts))
    sils_by_gold = {g: [] for g in golds}
    for i,(gi,vi) in enumerate(pts):
        intra = [hamming(vi,vj) for j,(gj,vj) in enumerate(pts) if j != i and gj == gi]
        a = sum(intra)/len(intra) if intra else 0.0
        b = float("inf")
        for g in golds:
            if g == gi: continue
            inter = [hamming(vi,vj) for (gj,vj) in pts if gj == g]
            if inter:
                mi = sum(inter)/len(inter)
                if mi < b: b = mi
        if b == float("inf"): b = 0.0
        s = (b-a)/max(a,b) if max(a,b) > 0 else 0.0
        sils_by_gold[gi].append(s)
    total_n = sum(len(v) for v in sils_by_gold.values())
    mean_all = sum(s for g in sils_by_gold for s in sils_by_gold[g])/total_n if total_n else 0.0
    per_gold = {g: (sum(sils_by_gold[g])/len(sils_by_gold[g]) if sils_by_gold[g] else 0.0) for g in golds}
    return mean_all, per_gold

# =========================================================
# Run
# =========================================================
SYSTEMS = [
    ("5TIER",  ratings_5tier,  SYS_LABELS["5TIER"], GOLD_MAP["5TIER"]),
    ("FDE",    ratings_fde,    SYS_LABELS["FDE"],   GOLD_MAP["FDE"]),
    ("LP",     ratings_lp,     SYS_LABELS["LP"],    GOLD_MAP["LP"]),
    ("BIN",    ratings_binary, SYS_LABELS["BIN"],   GOLD_MAP["BIN"]),
]

results = {}
for name, rows, labels, gmap in SYSTEMS:
    k = fleiss_kappa(rows, labels)
    acc = per_cat_accuracy(rows, labels, gmap)
    mi  = mi_uniform(rows, labels)
    sm, sper = silhouette(rows, labels)
    results[name] = {"fleiss_kappa": k, "per_cat_accuracy": {g: list(acc[g]) for g in acc},
                     "MI_uniform": mi, "silhouette_mean": sm, "silhouette_per_gold": sper}

# =========================================================
# Print unified table
# =========================================================
print(f"\n========== Pass-77-B31: 5-TIER vs LP vs FDE vs BINARY ==========")
print(f"\n--- WITHIN-SYSTEM Fleiss κ (rater agreement) ---")
for name,_,_,_ in SYSTEMS:
    print(f"  {name:7}: κ = {results[name]['fleiss_kappa']:+.4f}")

print(f"\n--- PER-CATEGORY ACCURACY (rater majority vs system-specific gold) ---")
print(f"  {'syst':<6} | " + " ".join(f"{g:>10}" for g in ("T","F","I","MI","NA")))
for name,_,_,gmap in SYSTEMS:
    cells = []
    for g in ("T","F","I","MI","NA"):
        c,t = results[name]["per_cat_accuracy"].get(g, (0,0))
        target = gmap.get(g, "—")
        cells.append(f"{c:>3}/{t:<3}→{target:<2}")
    print(f"  {name:<6} | " + " ".join(f"{x:>10}" for x in cells))

print(f"\n--- UNIFORM COMPARATOR: I(5tier-gold ; rater-majority) — info preserved about full 5-tier truth spectrum ---")
print(f"  {'syst':<6} | {'alphabet':<22} | {'cap (bits)':>10} | {'MI bits':>8} | {'NMI':>6} | {'AMI':>6} | {'ARI':>6} | {'Theil U':>7} | {'Cramer V':>8}")
for name,_,_,_ in SYSTEMS:
    mi = results[name]["MI_uniform"]
    alph = "{" + ",".join(mi["alphabet_realized"]) + "}"
    print(f"  {name:<6} | {alph:<22} | {mi['channel_capacity_bits']:>10.4f} | {mi['MI_bits']:>8.4f} | {mi['NMI']:>6.4f} | {mi['AMI']:>6.4f} | {mi['ARI']:>6.4f} | {mi['Theil_U_gold_given_rater']:>7.4f} | {mi['Cramers_V']:>8.4f}")

print(f"\n--- SILHOUETTE (Hamming on 3-rater tuple, w.r.t. 5-tier gold clusters) ---")
print(f"  {'syst':<6} | {'mean':>8} | " + " ".join(f"{g:>8}" for g in ("T","F","I","MI","NA")))
for name,_,_,_ in SYSTEMS:
    sm = results[name]["silhouette_mean"]
    per = results[name]["silhouette_per_gold"]
    print(f"  {name:<6} | {sm:>+8.4f} | " + " ".join(f"{per.get(g,0):>+8.4f}" for g in ("T","F","I","MI","NA")))

print(f"\n--- HEADLINE DELTAS vs 5-TIER (positive = 5-tier beats rival) ---")
ref = results["5TIER"]["MI_uniform"]
ref_k = results["5TIER"]["fleiss_kappa"]
ref_s = results["5TIER"]["silhouette_mean"]
for name,_,_,_ in SYSTEMS:
    if name == "5TIER": continue
    mi = results[name]["MI_uniform"]
    k = results[name]["fleiss_kappa"]
    s = results[name]["silhouette_mean"]
    print(f"  vs {name:5}: Δκ={ref_k-k:+.4f}  ΔMI={ref['MI_bits']-mi['MI_bits']:+.4f} bits  ΔAMI={ref['AMI']-mi['AMI']:+.4f}  ΔARI={ref['ARI']-mi['ARI']:+.4f}  ΔSil={ref_s-s:+.4f}")

# =========================================================
# Save
# =========================================================
json.dump(results, open(D/"results_rivals.json","w"), indent=2, default=str)
print(f"\nResults written to {D/'results_rivals.json'}")

# =========================================================
# Specific dialetheism diagnostics: did rival systems' "Both"/"Glut" cells
# actually catch the MI gold (the corpus's dialetheia-analog)?
# =========================================================
print(f"\n--- DIALETHEISM SPECIFIC: did rival 'Both'/'Glut' cells catch MI (incoherent) gold? ---")
for name, rows, labels, gmap in SYSTEMS:
    if name == "BIN": continue
    glut = {"5TIER":"MI", "LP":"B", "FDE":"BO"}[name]
    counts = Counter()
    for r in rows:
        if r["gold"] != "MI": continue
        rv = [v for v in r["ratings"].values() if v in labels]
        if not rv: continue
        for v in rv: counts[v] += 1
    total = sum(counts.values())
    glut_share = counts.get(glut, 0)/total if total else 0
    print(f"  {name:5}: of all rater calls on MI-gold props (n={total}), {counts.get(glut,0)} ({100*glut_share:.1f}%) went to the system's 'glut/incoherent' cell '{glut}'; full dist: {dict(counts)}")
