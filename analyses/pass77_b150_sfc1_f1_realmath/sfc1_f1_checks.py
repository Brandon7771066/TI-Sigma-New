"""
Pass 77 · B150 — The SFC-1-F1 ATTACK: a leakage-audited, real-math test of
non-oracular structural fidelity
====================================================================================

B149 (SFC-1) proved a DICHOTOMY on synthetic data: a non-oracular structural map
G = F(intrinsic structure of P) CAN beat chance (PART A, tautology escaped), but
the instant it does it hits the undecidability wall (PART C), so it is a fallible
heuristic, never a soundness+completeness method. B149 left one falsifier OPEN:

    SFC-1-F1: exhibit a REAL-math, leakage-free, non-oracular F that genuinely
              predicts/constrains mathematical truth from structure alone.

This batch ATTACKS SFC-1-F1 head-on, on REAL settled mathematical statements
(true theorems and settled-false claims, labels not in dispute). The point is to
find out, honestly, whether genuine math carries the kind of structure<->truth
correlation that PART A of B149 assumed — or whether real math behaves like
PART B (chance) the moment leakage is controlled.

HONEST SPINE (#69 both-ways; the result)
----------------------------------------
  PART A  A NAIVE benchmark (famous true theorems vs a separately-collected bag of
          false statements) shows an APPARENT structural signal well above chance.
          This is exactly the trap real ML-for-math benchmarks fall into.
  PART B  The decisive control: a NEGATION-PAIRED corpus, where every statement P
          appears alongside a settled-false counterpart via a near-minimal edit
          (antonym swap / single negation: rational<->irrational, prime<->not
          prime, converges<->diverges, ...) so the two members are structurally
          near-identical (high token overlap, checked) and negation/polarity
          markers are balanced across BOTH labels. Group cross-validation (a pair never spans
          train/test) ⇒ the SAME F collapses to ~chance. There is no leakage-free
          surface structure that tracks truth for these statements: you actually
          have to DO the math.  => SFC-1-F1 NOT met.
  PART C  The decidable arithmetic subclass ("a+b=c"): surface features alone ⇒
          chance, but adding an EVALUATOR feature (does a+b really equal c?) ⇒
          ~1.0. That evaluator IS a decision procedure / oracle for the subclass.
          This is exactly SFC-1-BOUND's escape hatch: fidelity is trivial on a
          decidable subclass precisely because F there = the decider (zero
          predict-before-proof content).
  PART D  Leakage tax = naive_acc - balanced_acc quantifies how much of PART A was
          annotation artifact (a LIVE demonstration of falsifier SFC-1-F3).
          Verdict: SFC-1-F1 stays OPEN; the empirical result is exactly what
          SFC-1-BOUND predicts. We did NOT find a leakage-free predictive F on
          undecidable-flavored real math; we also did NOT prove none can exist
          (this is a small, hand-curated, ILLUSTRATIVE corpus, not a census).

PRE-REGISTERED PREDICTIONS (written before running):
  P1: naive unbalanced benchmark held-out accuracy > 0.70 (apparent signal).
  P2: negation-paired balanced corpus, group-CV accuracy in [0.40, 0.62] (~chance).
  P3a: arithmetic surface-only accuracy <= 0.65 (no real signal from digits).
  P3b: arithmetic + evaluator feature accuracy >= 0.95 (but that feature is an
       oracle/decision procedure — flagged, does NOT count as M1).
  P4: leakage tax (naive - balanced) > 0.15 (PART A was inflated by artifact).
  P5: therefore SFC-1-F1 remains OPEN.

Fixed seed; numpy + zlib only (stdlib); features computed from the STRING ALONE;
no fitted magic constant; cap G* derived from T_d (B147), never typed as 0.93.
"""

import zlib
import numpy as np

SEED = 20260625
rng = np.random.default_rng(SEED)

# ---------------------------------------------------------------------------
# UOP cap from B147 (DERIVED from T_d, never typed as 0.93).
# ---------------------------------------------------------------------------
T_D_CANON = 0.644111
G_STAR = min(1.0, max(0.0, 3.0 * T_D_CANON - 1.0))   # -> 0.93233


# ---------------------------------------------------------------------------
# Structural features — computed from the STATEMENT STRING ALONE.
# No feature here consults a proof, a checker, or the truth label.
# (PART C adds one extra feature that IS an evaluator, clearly flagged.)
# ---------------------------------------------------------------------------
NEG_MARKERS = ("not", "no", "never", "fails", "cannot", "finitely", "un")


def surface_features(s):
    s_low = s.lower()
    toks = s_low.replace("(", " ").replace(")", " ").split()
    n_chars = len(s)
    n_words = max(1, len(toks))
    n_distinct = len(set(s_low))
    comp = len(zlib.compress(s.encode())) / max(1, n_chars)   # MDL/compression proxy
    n_digits = sum(c.isdigit() for c in s)
    neg = 0
    for t in toks:
        for m in NEG_MARKERS:
            if t == m or (m in ("un",) and t.startswith(m)):
                neg += 1
                break
    return [n_chars, n_words, n_distinct, comp, n_digits, neg]


FEAT_NAMES = ["n_chars", "n_words", "n_distinct", "compress_ratio", "n_digits",
              "neg_markers"]


# ---------------------------------------------------------------------------
# F : features -> truth-support G, learned on TRAIN ONLY (pure-numpy logistic).
# ---------------------------------------------------------------------------
class StructuralF:
    def fit(self, X, y, steps=6000, lr=0.2, l2=1e-2):
        X = np.asarray(X, float)
        self.mu = X.mean(0)
        self.sd = X.std(0) + 1e-9
        Xs = (X - self.mu) / self.sd
        n, k = Xs.shape
        self.w = np.zeros(k)
        self.b = 0.0
        y = np.asarray(y, float)
        for _ in range(steps):
            p = 1.0 / (1.0 + np.exp(-(Xs @ self.w + self.b)))
            g = p - y
            self.w -= lr * ((Xs.T @ g) / n + l2 * self.w)
            self.b -= lr * g.mean()
        return self

    def prob(self, X):
        Xs = (np.asarray(X, float) - self.mu) / self.sd
        return 1.0 / (1.0 + np.exp(-(Xs @ self.w + self.b)))

    def verdict(self, X):
        # UOP argmax over {True,False}: since J(B147) is monotone in G on [0,G*],
        # and G = G_STAR * prob, the UOP picks True iff prob > 0.5.
        return (self.prob(X) > 0.5).astype(int)


def accuracy(pred, y):
    return float(np.mean(np.asarray(pred) == np.asarray(y)))


all_ok = True


def check(label, ok):
    global all_ok
    all_ok = all_ok and ok
    print(f"  {'PASS' if ok else 'FAIL'}: {label}")


print("=" * 80)
print("SETUP — cap derived from T_d; features computed from the string alone")
print("=" * 80)
print(f"  G* = {G_STAR:.5f} (= 3*T_d-1 at T_d={T_D_CANON}); no '0.93' typed.")
print(f"  structural features: {FEAT_NAMES} (none reads a proof/checker/label)")


# ===========================================================================
# PART A — NAIVE benchmark (the trap): famous true theorems vs a separately
# collected bag of false statements. Realistically, the false bag is phrased
# with more negations/impossibility wording -> a spurious surface signal.
# ===========================================================================
print("\n" + "=" * 80)
print("PART A — naive unbalanced real-math benchmark (the leakage trap)")
print("=" * 80)

naive_true = [
    "there are infinitely many prime numbers",
    "sqrt(2) is irrational",
    "pi is irrational",
    "e is transcendental",
    "the harmonic series diverges",
    "the real numbers are uncountable",
    "the rational numbers are countable",
    "every continuous function on [0,1] is bounded",
    "7 is prime",
    "13 is odd",
    "the empty set is a subset of every set",
    "the square of any real number is nonnegative",
]
naive_false = [
    "7 is not prime",
    "e is not transcendental",
    "pi is not irrational",
    "sqrt(2) is not irrational",
    "the real numbers are not uncountable",
    "the empty set is a subset of no set",
    "there is no smallest positive integer",
    "5 is not odd",
    "the harmonic series does not diverge",
    "there are not infinitely many primes",
    "no continuous function on [0,1] is bounded",
    "the rationals are not countable",
]

Xn = [surface_features(s) for s in naive_true + naive_false]
yn = [1] * len(naive_true) + [0] * len(naive_false)
Xn = np.array(Xn, float)
yn = np.array(yn)


def repeated_cv(X, y, groups=None, frac=0.55, repeats=400):
    """Average held-out accuracy over many random splits (group-aware if groups)."""
    accs = []
    if groups is None:
        n = len(y)
        for _ in range(repeats):
            idx = rng.permutation(n)
            c = int(frac * n)
            tr, te = idx[:c], idx[c:]
            if len(set(y[tr])) < 2:
                continue
            F = StructuralF().fit(X[tr], y[tr])
            accs.append(accuracy(F.verdict(X[te]), y[te]))
    else:
        uniq = np.unique(groups)
        for _ in range(repeats):
            gp = rng.permutation(uniq)
            c = int(frac * len(uniq))
            gtr, gte = set(gp[:c].tolist()), set(gp[c:].tolist())
            tr = np.array([i for i in range(len(y)) if groups[i] in gtr])
            te = np.array([i for i in range(len(y)) if groups[i] in gte])
            if len(tr) == 0 or len(te) == 0 or len(set(y[tr])) < 2:
                continue
            F = StructuralF().fit(X[tr], y[tr])
            accs.append(accuracy(F.verdict(X[te]), y[te]))
    return float(np.mean(accs)), float(np.std(accs))


naive_acc, naive_sd = repeated_cv(Xn, yn)
print(f"  naive held-out accuracy = {naive_acc:.3f} (sd {naive_sd:.3f})")
print("  the 'neg_markers' feature is doing the work: false statements happen to")
print("  carry more negation/impossibility wording -> spurious structure<->truth link.")
check("P1: naive unbalanced benchmark accuracy > 0.70 (apparent signal)",
      naive_acc > 0.70)


# ===========================================================================
# PART B — DECISIVE control: a negation-PAIRED, polarity-balanced corpus.
# Each pair = (settled-true statement, settled-false counterpart) differing ONLY
# in mathematical content via an antonym swap. Polarity/negation words appear on
# BOTH labels across the corpus, so no surface token tracks truth. Group-CV keeps
# both members of a pair on the same side of the split.
# ===========================================================================
print("\n" + "=" * 80)
print("PART B — negation-paired, polarity-balanced real-math corpus (leakage-free)")
print("=" * 80)

# (true_statement, false_statement) — labels are settled mathematics.
pairs = [
    ("there are infinitely many primes", "there are finitely many primes"),
    ("sqrt(2) is irrational", "sqrt(2) is rational"),
    ("1/3 is rational", "1/3 is irrational"),
    ("pi is irrational", "pi is rational"),
    ("the harmonic series diverges", "the harmonic series converges"),
    ("the geometric series with ratio 1/2 converges",
     "the geometric series with ratio 1/2 diverges"),
    ("the real numbers are uncountable", "the real numbers are countable"),
    ("the rational numbers are countable", "the rational numbers are uncountable"),
    ("7 is prime", "7 is not prime"),
    ("9 is not prime", "9 is prime"),
    ("e is transcendental", "e is algebraic"),
    ("the cube root of 2 is algebraic", "the cube root of 2 is transcendental"),
    ("every continuous function on [0,1] is bounded",
     "every continuous function on [0,1] is unbounded"),
    ("not every continuous function is differentiable",
     "every continuous function is differentiable"),
    ("there is no largest prime", "there is a largest prime"),
    ("the empty set is a subset of every set", "the empty set is a subset of no set"),
    ("13 is odd", "13 is even"),
]

stmts, ylab, grp = [], [], []
for gi, (t, f) in enumerate(pairs):
    stmts.append(t); ylab.append(1); grp.append(gi)
    stmts.append(f); ylab.append(0); grp.append(gi)
Xb = np.array([surface_features(s) for s in stmts], float)
yb = np.array(ylab)
gb = np.array(grp)

# sanity: each pair is a near-minimal edit (high token overlap), so the two
# members are structurally near-identical and differ essentially in the math.
def jaccard(a, b):
    sa, sb = set(a.lower().split()), set(b.lower().split())
    return len(sa & sb) / max(1, len(sa | sb))
pair_overlap = float(np.mean([jaccard(t, f) for (t, f) in pairs]))
print(f"  mean per-pair token overlap (Jaccard) = {pair_overlap:.3f} "
      f"(near-minimal edits -> structurally near-identical members)")
check("P2a: paired members are near-identical (mean Jaccard >= 0.55)",
      pair_overlap >= 0.55)

# sanity: negation/polarity markers really are present on BOTH labels
neg_idx = FEAT_NAMES.index("neg_markers")
neg_true = Xb[yb == 1, neg_idx].sum()
neg_false = Xb[yb == 0, neg_idx].sum()
print(f"  neg_markers mass on TRUE={neg_true:.0f} vs FALSE={neg_false:.0f} "
      f"(balanced -> the PART A artifact is neutralized)")

bal_acc, bal_sd = repeated_cv(Xb, yb, groups=gb)
print(f"  balanced group-CV accuracy = {bal_acc:.3f} (sd {bal_sd:.3f}) ~ chance 0.5")
check("P2: negation-paired balanced accuracy in [0.40, 0.62] (~chance)",
      0.40 <= bal_acc <= 0.62)
print("  => with leakage controlled, NO surface structure tracks truth here.")
print("     To label these you must actually do the mathematics. SFC-1-F1 NOT met.")


# ===========================================================================
# PART C — decidable arithmetic subclass: surface-only -> chance; + evaluator
# feature -> ~1.0, but that feature IS a decision procedure (an oracle).
# ===========================================================================
print("\n" + "=" * 80)
print("PART C — decidable subclass (arithmetic): fidelity only via an evaluator/oracle")
print("=" * 80)

M = 600
arith_X_surf, arith_X_eval, arith_y = [], [], []
for _ in range(M):
    a = int(rng.integers(0, 50))
    b = int(rng.integers(0, 50))
    true_eq = rng.random() < 0.5
    c = a + b if true_eq else a + b + int(rng.integers(1, 9))
    s = f"{a}+{b}={c}"
    surf = surface_features(s)                 # digits/length only: no truth signal
    is_balanced = 1.0 if (a + b == c) else 0.0  # <-- EVALUATOR = decision procedure
    arith_X_surf.append(surf)
    arith_X_eval.append(surf + [is_balanced])
    arith_y.append(int(a + b == c))

arith_X_surf = np.array(arith_X_surf, float)
arith_X_eval = np.array(arith_X_eval, float)
arith_y = np.array(arith_y)

acc_surf, _ = repeated_cv(arith_X_surf, arith_y, repeats=120)
acc_eval, _ = repeated_cv(arith_X_eval, arith_y, repeats=120)
print(f"  surface-only accuracy   = {acc_surf:.3f} (no real signal from digits)")
print(f"  +evaluator accuracy     = {acc_eval:.3f} (solves it — but the evaluator")
print("                            IS the decision procedure / an oracle)")
check("P3a: arithmetic surface-only accuracy <= 0.65 (no structural signal)",
      acc_surf <= 0.65)
check("P3b: arithmetic + evaluator accuracy >= 0.95 (oracle feature; not M1)",
      acc_eval >= 0.95)
print("  => SFC-1-BOUND escape hatch confirmed: fidelity is trivial on a decidable")
print("     subclass ONLY because F there = the decider (zero predict-before-proof).")


# ===========================================================================
# PART D — leakage tax + verdict
# ===========================================================================
print("\n" + "=" * 80)
print("PART D — leakage tax (SFC-1-F3 live) and the SFC-1-F1 verdict")
print("=" * 80)
leak_tax = naive_acc - bal_acc
print(f"  leakage tax = naive {naive_acc:.3f} - balanced {bal_acc:.3f} = {leak_tax:.3f}")
print("  that gap was pure annotation artifact (negation-marker phrasing), not")
print("  access to mathematical truth — a live demonstration of SFC-1-F3.")
check("P4: leakage tax (naive - balanced) > 0.15", leak_tax > 0.15)
check("P5: SFC-1-F1 remains OPEN (no leakage-free non-oracular F predicted truth "
      "on the undecidable-flavored real-math corpus)",
      (0.40 <= bal_acc <= 0.62) and (acc_surf <= 0.65))
print("  HONEST SCOPE: small, hand-curated, ILLUSTRATIVE corpus. This is consistent")
print("  with SFC-1-BOUND (no magic), NOT a census proving no F can ever exist, and")
print("  NOT a claim about RH. SFC-1-F1 stays the open frontier (cf. Ramanujan")
print("  Machine / Davies et al. Nature 2021 — real but heuristic generators).")

print("\n" + "=" * 80)
print("ALL SFC-1-F1 ATTACK CHECKS PASSED" if all_ok else "SOME CHECKS FAILED")
print("=" * 80)
if not all_ok:
    raise SystemExit(1)
