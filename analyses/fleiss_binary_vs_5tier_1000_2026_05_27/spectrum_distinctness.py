"""Pass-77-B27: spectrum-distinctness / discriminant-validity battery.
Reuses Pass-77-B26 ratings (zero new API calls).

Metrics:
  1. Mutual Information I(gold; rater_majority)  [bits]
  2. Normalized Mutual Information (NMI)         [0,1]
  3. Adjusted Mutual Information (AMI)           [chance-corrected]
  4. Adjusted Rand Index (ARI)                   [clustering agreement]
  5. Theil's U  U(gold|rater)                    [asymmetric, 0,1]
  6. Cramer's V                                  [chi-square effect size]
  7. Silhouette score on per-proposition 3-rater vector  [-1,1]
  8. Per-system channel capacity (log2 of label alphabet)

All metrics computed on the 500 gold propositions where ground truth exists.
"""
import json, math, os
from collections import Counter
from pathlib import Path

D = Path(__file__).parent
test_set = {p['id']: p for p in json.load(open(D/'test_set.json'))}

def load_majority(path):
    """Return list of (gold_label, majority_rater_label, rater_tuple) over gold props only."""
    rows = json.load(open(D/path))
    pairs = []
    for r in rows:
        if r['gold'] == 'CASUAL' or r['gold'] is None:
            continue
        labels = [v for v in r['ratings'].values() if v]
        if len(labels) < 2:
            continue
        c = Counter(labels)
        maj, n = c.most_common(1)[0]
        if n >= 2:
            pairs.append((r['gold'], maj, tuple(labels)))
    return pairs

def entropy(counts):
    total = sum(counts)
    if total == 0: return 0.0
    return -sum((n/total)*math.log2(n/total) for n in counts if n > 0)

def joint_entropy(pairs_xy):
    c = Counter(pairs_xy)
    return entropy(list(c.values()))

def mutual_info(pairs):
    """I(X;Y) = H(X) + H(Y) - H(X,Y) in bits."""
    Hx = entropy(list(Counter(p[0] for p in pairs).values()))
    Hy = entropy(list(Counter(p[1] for p in pairs).values()))
    Hxy = joint_entropy([(p[0], p[1]) for p in pairs])
    return Hx + Hy - Hxy, Hx, Hy, Hxy

def nmi(I, Hx, Hy):
    if Hx == 0 or Hy == 0: return 0.0
    return I / math.sqrt(Hx * Hy)

def theil_u(I, Hx):
    """U(X|Y) = I(X;Y)/H(X) — fraction of X-entropy resolved by knowing Y."""
    return I / Hx if Hx > 0 else 0.0

def cramers_v(pairs):
    """V = sqrt(chi2 / (N * min(r-1, c-1)))."""
    xs = sorted(set(p[0] for p in pairs))
    ys = sorted(set(p[1] for p in pairs))
    N = len(pairs)
    obs = {(x,y): 0 for x in xs for y in ys}
    rx = Counter(p[0] for p in pairs)
    cy = Counter(p[1] for p in pairs)
    for p in pairs:
        obs[(p[0], p[1])] += 1
    chi2 = 0.0
    for x in xs:
        for y in ys:
            exp = rx[x] * cy[y] / N
            if exp > 0:
                chi2 += (obs[(x,y)] - exp)**2 / exp
    denom = N * (min(len(xs), len(ys)) - 1)
    return math.sqrt(chi2 / denom) if denom > 0 else 0.0

def adjusted_rand(pairs):
    """ARI between gold partition and rater partition."""
    from math import comb
    pairs_list = pairs
    N = len(pairs_list)
    a_labels = sorted(set(p[0] for p in pairs_list))
    b_labels = sorted(set(p[1] for p in pairs_list))
    contingency = {(a,b): 0 for a in a_labels for b in b_labels}
    for p in pairs_list:
        contingency[(p[0], p[1])] += 1
    a_sums = {a: sum(contingency[(a,b)] for b in b_labels) for a in a_labels}
    b_sums = {b: sum(contingency[(a,b)] for a in a_labels) for b in b_labels}
    sum_nij = sum(comb(n, 2) for n in contingency.values())
    sum_ai = sum(comb(n, 2) for n in a_sums.values())
    sum_bj = sum(comb(n, 2) for n in b_sums.values())
    Nc2 = comb(N, 2)
    expected = (sum_ai * sum_bj) / Nc2 if Nc2 > 0 else 0
    max_index = 0.5 * (sum_ai + sum_bj)
    if max_index == expected:
        return 1.0
    return (sum_nij - expected) / (max_index - expected)

def adjusted_mutual_info(pairs):
    """AMI = (I - E[I]) / (max(H(X),H(Y)) - E[I]); E[I] via permutation approx."""
    import random
    I, Hx, Hy, _ = mutual_info(pairs)
    Xs = [p[0] for p in pairs]
    Ys = [p[1] for p in pairs]
    rng = random.Random(20260527)
    perms = []
    for _ in range(200):
        Ys_shuf = Ys[:]
        rng.shuffle(Ys_shuf)
        perm_pairs = list(zip(Xs, Ys_shuf))
        Ip, _, _, _ = mutual_info(perm_pairs)
        perms.append(Ip)
    E_I = sum(perms)/len(perms)
    H_max = max(Hx, Hy)
    if H_max == E_I:
        return 1.0
    return (I - E_I) / (H_max - E_I)

def silhouette_on_rater_vectors(pairs):
    """Each prop's 3-rater label tuple -> Hamming distance vectors.
    Silhouette per gold cluster: a=mean intra-cluster dist, b=mean nearest-other-cluster dist.
    Returns mean silhouette and per-cluster breakdown."""
    by_gold = {}
    for g, _, vec in pairs:
        by_gold.setdefault(g, []).append(vec)
    def hd(a, b):
        return sum(1 for x,y in zip(a,b) if x != y) / len(a)
    all_sil = []
    per_cluster = {}
    for g, vecs in by_gold.items():
        sils = []
        for i, v in enumerate(vecs):
            if len(vecs) > 1:
                a = sum(hd(v, w) for j,w in enumerate(vecs) if j != i) / (len(vecs)-1)
            else:
                a = 0
            b_candidates = []
            for og, ovecs in by_gold.items():
                if og == g: continue
                b_candidates.append(sum(hd(v, w) for w in ovecs) / len(ovecs))
            b = min(b_candidates) if b_candidates else 0
            s = (b - a) / max(a, b) if max(a, b) > 0 else 0
            sils.append(s)
            all_sil.append(s)
        per_cluster[g] = sum(sils)/len(sils) if sils else 0
    return sum(all_sil)/len(all_sil), per_cluster

def run(mode, path):
    print(f"\n=== {mode.upper()} ({path}) ===")
    pairs = load_majority(path)
    print(f"  n_gold_props = {len(pairs)}")
    label_alphabet = sorted(set(p[1] for p in pairs))
    print(f"  rater label alphabet realized = {label_alphabet}  (|alphabet|={len(label_alphabet)})")
    print(f"  channel capacity log2(|alphabet|) = {math.log2(len(label_alphabet)):.4f} bits")
    I, Hx, Hy, Hxy = mutual_info(pairs)
    print(f"  H(gold)       = {Hx:.4f} bits")
    print(f"  H(rater)      = {Hy:.4f} bits")
    print(f"  H(gold,rater) = {Hxy:.4f} bits")
    print(f"  I(gold;rater) = {I:.4f} bits   <-- spectrum-preservation")
    print(f"  NMI           = {nmi(I, Hx, Hy):.4f}")
    print(f"  AMI           = {adjusted_mutual_info(pairs):.4f}   <-- chance-corrected")
    print(f"  ARI           = {adjusted_rand(pairs):.4f}   <-- clustering agreement")
    print(f"  Theil U(gold|rater) = {theil_u(I, Hx):.4f}   <-- 'rater determines gold' fraction")
    print(f"  Theil U(rater|gold) = {theil_u(I, Hy):.4f}")
    print(f"  Cramer's V    = {cramers_v(pairs):.4f}   <-- categorical effect size")
    sil_mean, per_c = silhouette_on_rater_vectors(pairs)
    print(f"  Silhouette (Hamming, mean) = {sil_mean:.4f}   <-- 'CLUSTERED' geometry test")
    for g in sorted(per_c.keys()):
        print(f"    silhouette gold={g:<2s}: {per_c[g]:+.4f}")
    return dict(mode=mode, n=len(pairs), alphabet=label_alphabet,
                channel_capacity=math.log2(len(label_alphabet)),
                H_gold=Hx, H_rater=Hy, H_joint=Hxy, I=I,
                NMI=nmi(I,Hx,Hy), AMI=adjusted_mutual_info(pairs),
                ARI=adjusted_rand(pairs), theil_U_gold_given_rater=theil_u(I,Hx),
                theil_U_rater_given_gold=theil_u(I,Hy),
                cramers_V=cramers_v(pairs),
                silhouette_mean=sil_mean, silhouette_per_gold=per_c)

if __name__ == "__main__":
    r_b = run("binary", "ratings_binary.json")
    r_5 = run("5tier", "ratings_5tier.json")
    print("\n=== HEADLINE COMPARISON ===")
    print(f"  {'metric':<32s} {'binary':>10s} {'5tier':>10s} {'delta':>10s}")
    for k in ['channel_capacity','I','NMI','AMI','ARI',
              'theil_U_gold_given_rater','theil_U_rater_given_gold',
              'cramers_V','silhouette_mean']:
        d = r_5[k] - r_b[k]
        print(f"  {k:<32s} {r_b[k]:>10.4f} {r_5[k]:>10.4f} {d:>+10.4f}")
    json.dump({'binary':r_b,'5tier':r_5},
              open(D/'spectrum_distinctness_results.json','w'),
              indent=2, default=str)
    print("\nWritten to spectrum_distinctness_results.json")
