"""
Pass-77-B108 — Does an INDEPENDENTLY-measured PD-real coordinate reconstruct the
5 truth labels {T,F,I,MI,NA}?

Inputs: ratings_pd.json  (3 raters x 500 gold props; each value = float in [-3,2]
or "OFFAXIS").

Outputs (printed + written to results.json):
  A. Inter-rater reliability of the PD instrument:
     - Fleiss kappa on PD-ZONES (continuous PD binned into {T,F,I,MI,NA} by the
       canonical PD thresholds) -- 3 raters, 5 categories.
     - Mean pairwise Pearson r on the on-axis numeric PD (instrument precision).
  B. PD<->gold LINK (the spectrum-exhaustion battery, vs gold ground truth):
     - Mutual Information (bits), NMI, AMI, ARI, Theil U, Cramer V
       between PD-zone (majority of raters) and gold label.
     - Silhouette of the 4 on-axis gold labels {T,F,I,MI} in 1-D mean-PD space
       (do the labels form distinct clusters ALONG the PD axis?).
     - NA off-axis capture rate (fraction of gold-NA props the raters put OFFAXIS)
       = empirical test of NAO-1 (N/A is off the PD spectrum).
  C. Descriptive: mean/median PD per gold label + monotone-ordering check
     (T > I > F, MI most negative).

Canonical PD zones (URB #728 five-zone architecture, (-3,+2) scale):
    OFFAXIS          -> NA   (off the spectrum, NAO-1)
    pd <= -2.5       -> MI   (the -3 MI cliff zone; F/MI midpoint = -2.5)
    -2.5 < pd <= -2/3-> F    (false zone: soft-false -1 .. false -2)
    -2/3 < pd <= 1/3 -> I    (canonical Indeterminate sub-range)
    pd > 1/3         -> T    (true zone: soft-true +1 .. true +2)
"""
import json, math, statistics
from collections import Counter
from pathlib import Path

D = Path(__file__).parent
rows = json.load(open(D / "ratings_pd.json"))

LO_I, HI_I, MI_CLIFF = -2.0/3.0, 1.0/3.0, -2.5

def zone(v):
    if v == "OFFAXIS":
        return "NA"
    if v is None:
        return None
    if v <= MI_CLIFF:
        return "MI"
    if v <= LO_I:
        return "F"
    if v <= HI_I:
        return "I"
    return "T"

LABELS = ["T", "F", "I", "MI", "NA"]

# ---------- A. Fleiss kappa on PD-zones ----------
def fleiss_kappa(items_zone_lists, cats):
    table = []
    for zlist in items_zone_lists:
        zlist = [z for z in zlist if z is not None]
        if len(zlist) < 2:
            continue
        c = Counter(zlist)
        table.append([c.get(k, 0) for k in cats])
    N = len(table)
    n = sum(table[0])  # raters per item (assume constant; rows w/ <2 dropped)
    # use per-row n (robust to dropped raters)
    P_is = []
    col_tot = [0] * len(cats)
    grand = 0
    for r in table:
        ni = sum(r)
        if ni < 2:
            continue
        P_is.append((sum(x * x for x in r) - ni) / (ni * (ni - 1)))
        for j, x in enumerate(r):
            col_tot[j] += x
        grand += ni
    P_bar = sum(P_is) / len(P_is)
    p_j = [c / grand for c in col_tot]
    Pe = sum(p * p for p in p_j)
    kappa = (P_bar - Pe) / (1 - Pe) if (1 - Pe) != 0 else float("nan")
    return kappa, P_bar, Pe, N

zone_lists = [[zone(v) for v in r["pd"].values()] for r in rows]
kappa, P_bar, Pe, Nk = fleiss_kappa(zone_lists, LABELS)

# instrument precision: mean pairwise Pearson r on on-axis numeric values
def pearson(a, b):
    n = len(a)
    if n < 3:
        return float("nan")
    ma, mb = sum(a)/n, sum(b)/n
    cov = sum((x-ma)*(y-mb) for x, y in zip(a, b))
    va = math.sqrt(sum((x-ma)**2 for x in a)); vb = math.sqrt(sum((y-mb)**2 for y in b))
    return cov/(va*vb) if va > 0 and vb > 0 else float("nan")

rater_names = list(rows[0]["pd"].keys())
pair_rs = []
for i in range(len(rater_names)):
    for j in range(i+1, len(rater_names)):
        xa, xb = [], []
        for r in rows:
            va, vb = r["pd"][rater_names[i]], r["pd"][rater_names[j]]
            if isinstance(va, (int, float)) and isinstance(vb, (int, float)):
                xa.append(va); xb.append(vb)
        pair_rs.append(pearson(xa, xb))
mean_pair_r = statistics.mean([x for x in pair_rs if not math.isnan(x)]) if pair_rs else float("nan")

# ---------- B. PD-zone (majority) vs gold : spectrum battery ----------
pairs = []  # (gold, pd_zone_majority)
for r, zl in zip(rows, zone_lists):
    zl2 = [z for z in zl if z is not None]
    if len(zl2) < 2:
        continue
    maj, cnt = Counter(zl2).most_common(1)[0]
    if cnt >= 2:
        pairs.append((r["gold"], maj))

def entropy(counts):
    tot = sum(counts)
    return -sum((c/tot)*math.log2(c/tot) for c in counts if c > 0) if tot else 0.0

def mutual_info(ps):
    Hx = entropy(list(Counter(p[0] for p in ps).values()))
    Hy = entropy(list(Counter(p[1] for p in ps).values()))
    Hxy = entropy(list(Counter(ps).values()))
    return Hx + Hy - Hxy, Hx, Hy

def cramers_v(ps):
    xs = sorted(set(p[0] for p in ps)); ys = sorted(set(p[1] for p in ps))
    N = len(ps); rx = Counter(p[0] for p in ps); cy = Counter(p[1] for p in ps)
    obs = Counter(ps); chi2 = 0.0
    for x in xs:
        for y in ys:
            exp = rx[x]*cy[y]/N
            if exp > 0:
                chi2 += (obs.get((x, y), 0)-exp)**2/exp
    denom = N*(min(len(xs), len(ys))-1)
    return math.sqrt(chi2/denom) if denom > 0 else 0.0

def adjusted_rand(ps):
    from math import comb
    A = sorted(set(p[0] for p in ps)); B = sorted(set(p[1] for p in ps))
    cont = Counter(ps)
    a_sum = {a: sum(cont.get((a, b), 0) for b in B) for a in A}
    b_sum = {b: sum(cont.get((a, b), 0) for a in A) for b in B}
    sij = sum(comb(n, 2) for n in cont.values())
    sa = sum(comb(n, 2) for n in a_sum.values()); sb = sum(comb(n, 2) for n in b_sum.values())
    Nc2 = comb(len(ps), 2); exp = sa*sb/Nc2 if Nc2 else 0; mx = 0.5*(sa+sb)
    return 1.0 if mx == exp else (sij-exp)/(mx-exp)

def adjusted_mi(ps):
    import random
    I, Hx, Hy = mutual_info(ps); Xs=[p[0] for p in ps]; Ys=[p[1] for p in ps]
    rng = random.Random(20260606); perms=[]
    for _ in range(200):
        s = Ys[:]; rng.shuffle(s)
        Ip,_,_ = mutual_info(list(zip(Xs, s))); perms.append(Ip)
    E = sum(perms)/len(perms); Hm = max(Hx, Hy)
    return 1.0 if Hm == E else (I-E)/(Hm-E)

I, Hx, Hy = mutual_info(pairs)
nmi = I/math.sqrt(Hx*Hy) if Hx > 0 and Hy > 0 else 0.0
ami = adjusted_mi(pairs)
ari = adjusted_rand(pairs)
theil = I/Hx if Hx > 0 else 0.0
cv = cramers_v(pairs)

# zone-majority accuracy vs gold + confusion
acc = sum(1 for g, m in pairs if g == m)/len(pairs)
conf = Counter(pairs)

# ---------- B2. Silhouette of on-axis gold labels in 1-D mean-PD space ----------
def mean_pd(r):
    vals = [v for v in r["pd"].values() if isinstance(v, (int, float))]
    return statistics.mean(vals) if vals else None

onaxis = [("MI" if r["gold"] == "MI" else r["gold"], mean_pd(r))
          for r in rows if r["gold"] in ("T", "F", "I", "MI") and mean_pd(r) is not None]
by_lbl = {}
for g, v in onaxis:
    by_lbl.setdefault(g, []).append(v)

def silhouette_1d(by_lbl):
    sis = []; per = {}
    pts = [(g, v) for g, vs in by_lbl.items() for v in vs]
    for g, vs in by_lbl.items():
        sg = []
        for v in vs:
            same = [abs(v-w) for w in vs if w is not v]
            a = statistics.mean(same) if same else 0.0
            b_cand = []
            for og, ovs in by_lbl.items():
                if og == g:
                    continue
                b_cand.append(statistics.mean([abs(v-w) for w in ovs]))
            b = min(b_cand) if b_cand else 0.0
            s = (b-a)/max(a, b) if max(a, b) > 0 else 0.0
            sg.append(s); sis.append(s)
        per[g] = statistics.mean(sg) if sg else 0.0
    return statistics.mean(sis) if sis else 0.0, per

sil_mean, sil_per = silhouette_1d(by_lbl)

# ---------- B3. NA off-axis capture (NAO-1 test) ----------
na_rows = [r for r in rows if r["gold"] == "NA"]
na_offaxis = sum(1 for r in na_rows
                 if Counter([zone(v) for v in r["pd"].values() if v is not None]).most_common(1)[0][0] == "NA")
na_capture = na_offaxis/len(na_rows) if na_rows else float("nan")
# also: per-rater raw OFFAXIS rate on NA props
na_raw_off = sum(1 for r in na_rows for v in r["pd"].values() if v == "OFFAXIS")
na_raw_tot = sum(1 for r in na_rows for v in r["pd"].values() if v is not None)

# ---------- C. Per-gold-label PD descriptives + ordering ----------
desc = {}
for lbl in ("T", "F", "I", "MI"):
    vs = [mean_pd(r) for r in rows if r["gold"] == lbl and mean_pd(r) is not None]
    if vs:
        desc[lbl] = dict(n=len(vs), mean=round(statistics.mean(vs), 3),
                         median=round(statistics.median(vs), 3),
                         sd=round(statistics.pstdev(vs), 3))
ordering_ok = (desc.get("T", {}).get("mean", -9) > desc.get("I", {}).get("mean", -9)
               > desc.get("F", {}).get("mean", -9) > desc.get("MI", {}).get("mean", -9))

# ---------- report ----------
print(f"n rows rated = {len(rows)}  |  gold dist = {dict(Counter(r['gold'] for r in rows))}")
print("\n== A. PD instrument inter-rater reliability ==")
print(f"  Fleiss kappa (PD-zones, 5-cat, 3 raters) = {kappa:.4f}  (P_bar={P_bar:.4f}, Pe={Pe:.4f}, N={Nk})")
print(f"  mean pairwise Pearson r (on-axis numeric)= {mean_pair_r:.4f}")
print("\n== B. PD-zone(majority) vs GOLD link (spectrum-exhaustion battery) ==")
print(f"  n usable pairs = {len(pairs)}")
print(f"  zone->gold accuracy = {acc:.4f}")
print(f"  Mutual Information  = {I:.4f} bits   (H_gold={Hx:.4f}, H_pd={Hy:.4f})")
print(f"  NMI                 = {nmi:.4f}")
print(f"  AMI (chance-corr)   = {ami:.4f}")
print(f"  ARI                 = {ari:.4f}")
print(f"  Theil U(gold|pd)    = {theil:.4f}")
print(f"  Cramer V            = {cv:.4f}")
print(f"  Silhouette on-axis {{T,F,I,MI}} in mean-PD space = {sil_mean:.4f}")
for g in ("T", "I", "F", "MI"):
    if g in sil_per:
        print(f"      sil[{g:<2s}] = {sil_per[g]:+.4f}")
print(f"  NA off-axis capture (NAO-1) = {na_capture:.4f}  (raw OFFAXIS rate on NA props = {na_raw_off}/{na_raw_tot})")
print("\n== C. mean PD per gold label ==")
for g in ("T", "I", "F", "MI"):
    if g in desc:
        print(f"  {g:<2s}: {desc[g]}")
print(f"  monotone ordering T>I>F>MI holds: {ordering_ok}")
print("\n== confusion (gold -> pd_zone_majority) ==")
for g in LABELS:
    row = {m: conf.get((g, m), 0) for m in LABELS}
    if sum(row.values()):
        print(f"  gold {g:<2s}: {row}")

json.dump(dict(
    n=len(rows), kappa=kappa, P_bar=P_bar, Pe=Pe,
    mean_pairwise_pearson=mean_pair_r,
    n_pairs=len(pairs), zone_gold_accuracy=acc,
    MI_bits=I, H_gold=Hx, H_pd=Hy, NMI=nmi, AMI=ami, ARI=ari,
    theil_U_gold_given_pd=theil, cramers_V=cv,
    silhouette_onaxis_mean=sil_mean, silhouette_per_label=sil_per,
    na_offaxis_capture=na_capture, na_raw_offaxis=na_raw_off, na_raw_total=na_raw_tot,
    per_label_pd=desc, monotone_T_I_F_MI=ordering_ok,
    confusion={f"{g}->{m}": conf.get((g, m), 0) for g in LABELS for m in LABELS if conf.get((g, m), 0)},
), open(D / "results.json", "w"), indent=2, default=str)
print("\nwritten results.json")
