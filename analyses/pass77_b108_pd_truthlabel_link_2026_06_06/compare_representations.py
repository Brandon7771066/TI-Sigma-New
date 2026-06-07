"""
Pass-77-B108 — Comparative benchmark of the PD truth-representations.

Tests how well each PD/GILE representation ENCODES and RECOVERS the 5 truth
labels {T,F,I,MI,NA}, using REUSED data (zero new API calls):
  * 500 gold props x 3 raters, 5-tier categorical labels
    (analyses/fleiss_binary_vs_5tier_1000_2026_05_27/ratings_5tier.json)
  * partial continuous PD-degree ratings as a cross-check
    (analyses/pass77_b108_.../ratings_pd.json)

Representations compared (faithful coords from corpus code):
  1. Scalar PD            real line (-3,+2)            [generate_pd_figures.py fig1]
  2. Complex PD           real=PD axis, imag=MI/Tralse [fig2; NA on -imag per NAO-1 fold]
  3. TI Sigma Graph (TIG) = real-axis projection of the Crystal (fig4) + i vertex
  4. 32D / 64D GILE Matrix  4 GILE x 4 truth-axes x 4 truth-labels, NA folded->MI (b61.py)
  5. TI Sigma Crystal / TECC  8D, urb_630 5-valued code (run_falsifiers.py F2)
        - "table" embedding (DT/TF collinear, the literal urb_630 table)
        - "orthogonal" embedding (sec 2.2 distinct-axis assumption)

Metrics per representation:
  A. representational capacity: # of the 5 labels distinctly encodable + dims + log2 capacity
  B. codeword geometry: min pairwise distance -> error-correction radius (d_min/2)
  C. empirical label recovery on REAL rater noise: per-prop 3-rater centroid ->
     nearest codeword -> accuracy + per-label recall + Fleiss-style confusion
  D. discriminant battery in each rep's embedding: silhouette + NMI + AMI + ARI
  E. controlled noise robustness: Monte-Carlo using the EMPIRICAL confusion matrix
     as the noise model (reused), decode accuracy vs injected disagreement.

All deterministic / seeded. #69: honest about which reps cannot represent NA, and
carries forward the B42 finding that the literal TECC table is collinear (weak EC).
"""
import json, math, random, statistics
from collections import Counter
from itertools import combinations
from pathlib import Path

D = Path(__file__).parent
FIVE = json.load(open("analyses/fleiss_binary_vs_5tier_1000_2026_05_27/ratings_5tier.json"))
GOLD = [r for r in FIVE if r["gold"] in ("T", "F", "I", "MI", "NA")]
LABELS = ["T", "F", "I", "MI", "NA"]

PHI = (1 + 5 ** 0.5) / 2
E = math.e
PI = math.pi
SQRT2 = 2 ** 0.5
C = 1 / (PHI * SQRT2)          # 0.4370  (urb_630 x_min)
T = 2 * 0.685 - C              # 0.9330  (urb_630 (C+T)/2 = 0.685)

# ---------------------------------------------------------------------------
# Each representation: label -> coordinate vector (tuple). None = NOT encodable.
# ---------------------------------------------------------------------------
REPS = {}

# 1. Scalar PD (1D real). NA off-axis = not representable on the real line.
REPS["scalar_PD_1D"] = dict(
    dims=1, coords={"T": (2.0,), "I": (0.0,), "F": (-2.0,), "MI": (-3.0,), "NA": None},
    note="(-3,+2) Perfect-Fifth real axis; NA off-axis (unrepresentable). =TIG real projection.")

# 2. Complex PD (2D): real=PD principal axis, imag=MI/Tralse axis; NA on -imag (NAO-1 fold).
REPS["complex_PD_2D"] = dict(
    dims=2, coords={"T": (2.0, 0.0), "I": (0.0, 0.0), "F": (-2.0, 0.0),
                    "MI": (0.0, E), "NA": (0.0, -E)},
    note="real=PD axis, imag=MI/Tralse axis; MI=+e i, NA=-e i (share imaginary axis).")

# 3. TI Sigma Graph: real-axis projection (scalar) PLUS the i vertex for MI; NA off-graph.
REPS["TIG_graph"] = dict(
    dims=2, coords={"T": (1.0, 0.0), "I": (0.0, 0.0), "F": (-1.0, 0.0),
                    "MI": (0.0, 1.0), "NA": None},
    note="9-constant graph {0,1,i,sqrt2,e,phi,pi,C,T}; chi=4 (B68); MI->i vertex; NA off-graph.")

# 4. 32D/64D GILE Matrix: one-hot over 4 truth-labels {T,F,tau,MI}; NA FOLDED into MI (b61 4^3 closure).
#    GILE x truth-axis context (16 dims) is uniform here (no per-prop GILE ratings) -> label factor only.
REPS["GILE_matrix_64D"] = dict(
    dims=4, coords={"T": (1, 0, 0, 0), "F": (0, 1, 0, 0), "I": (0, 0, 1, 0),
                    "MI": (0, 0, 0, 1), "NA": (0, 0, 0, 1)},
    note="4 truth-labels {T,F,tau(I),MI}; NA folded into MI for 4^3 closure (b61). 32D=Hermitian half, same label-separation.")

# 5a. TECC / Crystal — literal urb_630 table (DT/TF collinear in dim0). dims [C,T,1,sqrt2,phi,e,pi,r0]
REPS["TSC_TECC_table"] = dict(
    dims=8, coords={
        "T":  (0, 0, 0, 0, PHI, 0, 0, 0),   # TT
        "F":  (T, 0, 0, 0, 0, 0, 0, 0),     # TF (collinear w/ MI in dim0)
        "I":  (0, 0, 1, 0, 0, 0, 0, 0),     # TI
        "MI": (C, 0, 0, 0, 0, 0, 0, 0),     # DT
        "NA": (0, 0, 0, 0, 0, 0, PI, 0)},   # EV
    note="urb_630 5-valued code, LITERAL table (B42: DT/TF collinear -> weak EC).")

# 5b. TECC / Crystal — orthogonal embedding (urb_630 sec 2.2 distinct-axis assumption)
REPS["TSC_TECC_orthogonal"] = dict(
    dims=8, coords={
        "T":  (0, 0, 0, 0, PHI, 0, 0, 0),
        "F":  (0, T, 0, 0, 0, 0, 0, 0),     # TF on its OWN dim
        "I":  (0, 0, 1, 0, 0, 0, 0, 0),
        "MI": (C, 0, 0, 0, 0, 0, 0, 0),
        "NA": (0, 0, 0, 0, 0, 0, PI, 0)},
    note="urb_630 5-valued code, ORTHOGONAL embedding (all 5 on distinct axes).")


def dist(a, b):
    return math.sqrt(sum((x - y) ** 2 for x, y in zip(a, b)))

def centroid(vs):
    n = len(vs)
    return tuple(sum(v[i] for v in vs) / n for i in range(len(vs[0])))

def decode(point, coords):
    """nearest representable label-codeword."""
    best, bd = None, 1e18
    for lab, c in coords.items():
        if c is None:
            continue
        d = dist(point, c)
        if d < bd:
            bd, best = d, lab
    return best

# ---------- B. codeword geometry ----------
def codeword_geometry(coords):
    pts = {k: v for k, v in coords.items() if v is not None}
    dmin, pair = 1e18, None
    for a, b in combinations(pts, 2):
        d = dist(pts[a], pts[b])
        if d < dmin:
            dmin, pair = d, (a, b)
    return dmin, pair

# ---------- discriminant battery helpers ----------
def entropy(counts):
    tot = sum(counts)
    return -sum((c / tot) * math.log2(c / tot) for c in counts if c > 0) if tot else 0.0

def mutual_info(pairs):
    Hx = entropy(list(Counter(p[0] for p in pairs).values()))
    Hy = entropy(list(Counter(p[1] for p in pairs).values()))
    Hxy = entropy(list(Counter(pairs).values()))
    return Hx + Hy - Hxy, Hx, Hy

def adjusted_rand(pairs):
    from math import comb
    cont = Counter(pairs)
    A = set(p[0] for p in pairs); B = set(p[1] for p in pairs)
    a_sum = {a: sum(cont.get((a, b), 0) for b in B) for a in A}
    b_sum = {b: sum(cont.get((a, b), 0) for a in A) for b in B}
    sij = sum(comb(n, 2) for n in cont.values())
    sa = sum(comb(n, 2) for n in a_sum.values()); sb = sum(comb(n, 2) for n in b_sum.values())
    Nc2 = comb(len(pairs), 2); exp = sa * sb / Nc2 if Nc2 else 0; mx = 0.5 * (sa + sb)
    return 1.0 if mx == exp else (sij - exp) / (mx - exp)

def adjusted_mi(pairs):
    I, Hx, Hy = mutual_info(pairs)
    Xs = [p[0] for p in pairs]; Ys = [p[1] for p in pairs]
    rng = random.Random(20260606); perms = []
    for _ in range(200):
        s = Ys[:]; rng.shuffle(s)
        Ip, _, _ = mutual_info(list(zip(Xs, s))); perms.append(Ip)
    Ebar = sum(perms) / len(perms); Hm = max(Hx, Hy)
    return 1.0 if Hm == Ebar else (I - Ebar) / (Hm - Ebar)

def silhouette(points_by_label):
    pts = [(g, p) for g, ps in points_by_label.items() for p in ps]
    sis = []
    for g, ps in points_by_label.items():
        for p in ps:
            same = [dist(p, q) for q in ps if q is not p]
            a = statistics.mean(same) if same else 0.0
            bc = []
            for og, qs in points_by_label.items():
                if og == g:
                    continue
                bc.append(statistics.mean([dist(p, q) for q in qs]))
            b = min(bc) if bc else 0.0
            sis.append((b - a) / max(a, b) if max(a, b) > 0 else 0.0)
    return statistics.mean(sis) if sis else 0.0

# ---------- per-rep evaluation on REAL rater data ----------
def eval_rep(name, rep):
    coords = rep["coords"]
    encodable = [l for l in LABELS if coords.get(l) is not None]
    dmin, pair = codeword_geometry(coords)
    pairs = []           # (gold, decoded)
    pts_by_gold = {}     # gold -> [centroid points]
    for r in GOLD:
        labs = [v for v in r["ratings"].values() if v in coords]
        vecs = [coords[v] for v in labs if coords[v] is not None]
        if not vecs:
            # No encodable rater label (e.g. all-NA triplet under a rep that
            # cannot represent NA). #69 fair denominator: count as an explicit
            # MISS (decoded=None), NOT a dropped sample, so every rep is scored
            # on the SAME 500 props (matches the robustness section's treatment).
            pairs.append((r["gold"], None))
            continue
        ctr = centroid(vecs)
        dec = decode(ctr, coords)
        pairs.append((r["gold"], dec))
        pts_by_gold.setdefault(r["gold"], []).append(ctr)
    acc = sum(1 for g, d in pairs if g == d) / len(pairs)
    # per-label recall
    recall = {}
    for lab in LABELS:
        sub = [(g, d) for g, d in pairs if g == lab]
        recall[lab] = round(sum(1 for g, d in sub if d == lab) / len(sub), 3) if sub else None
    I, Hx, Hy = mutual_info(pairs)
    nmi = I / math.sqrt(Hx * Hy) if Hx > 0 and Hy > 0 else 0.0
    sil = silhouette(pts_by_gold)
    conf = {f"{g}->{d}": c for (g, d), c in Counter(pairs).items()}
    return dict(
        name=name, dims=rep["dims"], note=rep["note"],
        n_encodable_labels=len(encodable), encodable=encodable,
        log2_capacity=round(math.log2(len(encodable)), 3),
        codeword_dmin=round(dmin, 4), closest_pair=pair,
        correction_radius=round(dmin / 2, 4),
        accuracy=round(acc, 4), per_label_recall=recall,
        MI_bits=round(I, 4), NMI=round(nmi, 4),
        AMI=round(adjusted_mi(pairs), 4), ARI=round(adjusted_rand(pairs), 4),
        silhouette=round(sil, 4), confusion=conf)

results = {name: eval_rep(name, rep) for name, rep in REPS.items()}

# ---------- E. controlled noise robustness (empirical confusion as noise model) ----------
# Build empirical per-rater noise: P(rater says X | gold G) from the real 5-tier data.
noise = {g: Counter() for g in LABELS}
for r in GOLD:
    for v in r["ratings"].values():
        if v in LABELS:
            noise[r["gold"]][v] += 1
noise_p = {g: {l: noise[g].get(l, 0) / sum(noise[g].values()) for l in LABELS}
           for g in LABELS if sum(noise[g].values())}

def sample_label(g, rng):
    x = rng.random(); cum = 0.0
    for l in LABELS:
        cum += noise_p[g].get(l, 0)
        if x <= cum:
            return l
    return LABELS[-1]

def robustness(rep, n_raters, trials=4000, seed=20260606):
    coords = rep["coords"]; rng = random.Random(seed)
    ok = 0; tot = 0
    for _ in range(trials):
        for g in LABELS:
            if g not in noise_p:
                continue
            labs = [sample_label(g, rng) for _ in range(n_raters)]
            vecs = [coords[v] for v in labs if coords.get(v) is not None]
            if not vecs:
                tot += 1; continue   # unrepresentable -> counts as a miss
            if decode(centroid(vecs), coords) == g:
                ok += 1
            tot += 1
    return round(ok / tot, 4)

robust = {name: {f"{k}_raters": robustness(rep, k) for k in (1, 3, 5, 9)}
          for name, rep in REPS.items()}

# ---------- cross-check: partial continuous PD-degree ratings align with scalar zones ----------
xcheck = None
pdf = D / "ratings_pd.json"
if pdf.exists():
    pdrows = json.load(open(pdf))
    per = {}
    for r in pdrows:
        vals = [v for v in r["pd"].values() if isinstance(v, (int, float))]
        if vals:
            per.setdefault(r["gold"], []).append(statistics.mean(vals))
    xcheck = {g: dict(n=len(v), mean_PD=round(statistics.mean(v), 3),
                      sd=round(statistics.pstdev(v), 3))
              for g, v in sorted(per.items())}

# ---------- report ----------
print(f"n gold props = {len(GOLD)}  | labels = {LABELS}")
print("\n" + "=" * 92)
print(f"{'representation':<22}{'dim':>4}{'#lab':>5}{'cap':>6}{'d_min':>8}{'r_corr':>8}{'acc':>7}{'NMI':>7}{'AMI':>7}{'ARI':>7}{'sil':>7}")
print("-" * 92)
for name in REPS:
    r = results[name]
    print(f"{name:<22}{r['dims']:>4}{r['n_encodable_labels']:>5}{r['log2_capacity']:>6}"
          f"{r['codeword_dmin']:>8.3f}{r['correction_radius']:>8.3f}{r['accuracy']:>7.3f}"
          f"{r['NMI']:>7.3f}{r['AMI']:>7.3f}{r['ARI']:>7.3f}{r['silhouette']:>7.3f}")
print("=" * 92)

print("\nPer-label recall (recovery of each gold label from real 3-rater centroid):")
print(f"{'representation':<22}" + "".join(f"{l:>7}" for l in LABELS))
for name in REPS:
    rc = results[name]["per_label_recall"]
    print(f"{name:<22}" + "".join(f"{(rc[l] if rc[l] is not None else '-'):>7}" for l in LABELS))

print("\nControlled noise robustness (decode accuracy; noise = empirical rater confusion):")
print(f"{'representation':<22}{'1rater':>9}{'3raters':>9}{'5raters':>9}{'9raters':>9}")
for name in REPS:
    rb = robust[name]
    print(f"{name:<22}{rb['1_raters']:>9.3f}{rb['3_raters']:>9.3f}{rb['5_raters']:>9.3f}{rb['9_raters']:>9.3f}")

print("\nClosest codeword pair (binding error-correction constraint):")
for name in REPS:
    print(f"  {name:<22} d_min={results[name]['codeword_dmin']:.3f} between {results[name]['closest_pair']}")

if xcheck:
    print("\nCross-check — partial continuous PD-degree ratings, mean PD per gold label:")
    for g, d in xcheck.items():
        print(f"  {g:<3} n={d['n']:<3} mean_PD={d['mean_PD']:+.3f}  sd={d['sd']:.3f}")

json.dump(dict(n_gold=len(GOLD), reps=results, robustness=robust,
               continuous_pd_crosscheck=xcheck),
          open(D / "comparison_results.json", "w"), indent=2, default=str)
print("\nwritten comparison_results.json")
