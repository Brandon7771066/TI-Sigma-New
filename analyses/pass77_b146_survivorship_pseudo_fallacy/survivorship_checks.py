"""
PASS-77 B146 — Survivorship as a (possibly/likely) PSEUDO-FALLACY.
Memory-Selection Conditioning (candidate SPF-1). NOT ratified; canonical count stays 79.

WHAT THIS FILE PROVES (and what it does NOT):
  This is a LOGIC / METHOD demonstration, NOT an empirical claim about real human memory.
  It demonstrates the conditional statement:
     IF memory retention is OUTCOME-SYMMETRIC (keeps confident-wins and confident-losses
     at the SAME rate), THEN estimating "P(success | I seriously try)" from remembered
     serious attempts is UNBIASED  ==> calling that move "survivorship bias" is a
     PSEUDO-FALLACY (a misdiagnosis).
     IF retention is OUTCOME-ASYMMETRIC (wins remembered more than losses), the same
     estimate inflates monotonically with the asymmetry  ==> genuine survivorship.

  It SEPARATES two operations the folk move conflates:
     (A) NULL-EXCLUSION   : drop non-serious / low-confidence attempts from the denominator.
                            -> harmless. It correctly answers a DIFFERENT (conditional)
                               question; it is NOT what inflates anything. (B144 result.)
     (B) MISS-DELETION    : forget/drop the SERIOUS attempts that FAILED.
                            -> THIS is the only thing that inflates. It is driven entirely
                               by the outcome-asymmetry parameter alpha (= 1 - memory quality).

  The whole claim therefore "hinges on memory quality" exactly as the author said:
  memory quality == low alpha. alpha is an OPEN empirical question (see paper, #69 both ways);
  this file does NOT assert real humans have alpha~0.

NO numerology. No load-bearing recurring constant. Fixed seed only for reproducibility.
"""

import numpy as np

RNG = np.random.default_rng(20260625)

# -----------------------------------------------------------------------------
# Ground-truth world (STIPULATED — these are modelling choices, not measurements)
# -----------------------------------------------------------------------------
# Each attempt has a prospectively-logged confidence c in [0,1].
# "Serious" attempt := c >= SERIOUS_THRESHOLD.
# TRUE success probability is higher for serious attempts than non-serious ones,
# so the population rate and the serious-conditional rate genuinely DIFFER
# (this is the point of SPF-1a: excluding nulls is a reference-class choice, not a bias).
N = 400_000
SERIOUS_THRESHOLD = 0.60
P_SUCCESS_SERIOUS = 0.55      # the TARGET quantity we want to recover
P_SUCCESS_NONSERIOUS = 0.25   # lower; nulls are a different reference class
TOL = 0.01                    # tolerance band for "unbiased"


def make_world(n=N):
    c = RNG.uniform(0.0, 1.0, size=n)
    serious = c >= SERIOUS_THRESHOLD
    p = np.where(serious, P_SUCCESS_SERIOUS, P_SUCCESS_NONSERIOUS)
    success = RNG.uniform(size=n) < p
    return c, serious, success


def retention_prob(serious, success, alpha, r_serious=0.90, r_nonserious=0.15):
    """
    Outcome-asymmetry model. Base retention depends ONLY on seriousness (pre-outcome).
    alpha in [0,1] tilts retention toward wins:
        remembered-if-win  multiplier = (1 + alpha)
        remembered-if-loss multiplier = (1 - alpha)
    alpha = 0  -> outcome-symmetric (memory keeps committed misses as well as wins).
    alpha -> 1 -> committed misses vanish from memory (classic survivorship).
    """
    base = np.where(serious, r_serious, r_nonserious)
    mult = np.where(success, 1.0 + alpha, 1.0 - alpha)
    return np.clip(base * mult, 0.0, 1.0)


def recalled_serious_success_rate(c, serious, success, alpha):
    r = retention_prob(serious, success, alpha)
    remembered = RNG.uniform(size=c.shape[0]) < r
    sel = remembered & serious
    if sel.sum() == 0:
        return np.nan, 0
    return success[sel].mean(), int(sel.sum())


def check(name, ok, detail=""):
    print(f"[{'PASS' if ok else 'FAIL':4}] {name}: {detail}")
    return ok


def main():
    c, serious, success = make_world()
    all_pass = True

    pop_rate = success.mean()
    true_serious = success[serious].mean()
    true_nonserious = success[~serious].mean()

    print("=" * 78)
    print("GROUND TRUTH (stipulated world)")
    print("=" * 78)
    print(f"  population success rate              = {pop_rate:.4f}")
    print(f"  TRUE P(success | serious)  [target]  = {true_serious:.4f}")
    print(f"  TRUE P(success | non-serious)        = {true_nonserious:.4f}")
    print()

    # ---- SPF-1a: NULL-EXCLUSION is correct reference-class conditioning, not bias ----
    # Dropping non-serious attempts changes the ANSWER (pop_rate -> serious rate),
    # but the serious rate is the CORRECT answer to "what happens when I commit?".
    print("=" * 78)
    print("SPF-1a  --  null-exclusion is conditioning, NOT inflation")
    print("=" * 78)
    gap = true_serious - pop_rate
    all_pass &= check(
        "serious-conditional differs from population (reference classes differ)",
        gap > 0.05,
        f"serious {true_serious:.3f} vs population {pop_rate:.3f} (gap {gap:+.3f})",
    )
    # With PERFECT recall of serious attempts (alpha=0, ignore nulls), we recover the target.
    rate0, n0 = recalled_serious_success_rate(c, serious, success, alpha=0.0)
    all_pass &= check(
        "alpha=0 recall of serious attempts is UNBIASED for the target",
        abs(rate0 - true_serious) < TOL,
        f"recalled {rate0:.4f} vs target {true_serious:.4f} (|err|={abs(rate0-true_serious):.4f}, n={n0})",
    )

    # ---- SPF-1 core: bias is driven ENTIRELY by outcome-asymmetry alpha ----------
    print()
    print("=" * 78)
    print("SPF-1   --  bias vs outcome-asymmetry alpha (= 1 - memory quality)")
    print("=" * 78)
    print(f"  {'alpha':>6} | {'recalled':>9} | {'true':>6} | {'inflation':>9} | n_remembered")
    print("  " + "-" * 60)
    rows = []
    for alpha in [0.0, 0.1, 0.2, 0.3, 0.5, 0.7, 0.9]:
        rate, n = recalled_serious_success_rate(c, serious, success, alpha)
        infl = rate - true_serious
        rows.append((alpha, rate, infl))
        print(f"  {alpha:6.2f} | {rate:9.4f} | {true_serious:6.3f} | {infl:+9.4f} | {n}")

    # Pseudo-fallacy regime: alpha=0 => ~zero inflation.
    a0_infl = rows[0][2]
    all_pass &= check(
        "alpha=0 inflation is ~0 (PSEUDO-FALLACY regime: no survivorship)",
        abs(a0_infl) < TOL,
        f"inflation at alpha=0 = {a0_infl:+.4f}",
    )
    # Fallacy regime: inflation strictly increases with alpha.
    infls = [r[2] for r in rows]
    monotone = all(infls[i + 1] > infls[i] - 1e-9 for i in range(len(infls) - 1))
    all_pass &= check(
        "inflation increases monotonically with alpha (FALLACY regime grows)",
        monotone and infls[-1] > 0.10,
        f"inflation 0->0.9 : {infls[0]:+.4f} -> {infls[-1]:+.4f}",
    )

    # ---- SPF-1: locate the crossover where inflation first exceeds tolerance -----
    print()
    print("=" * 78)
    print("SPF-1   --  crossover alpha* where survivorship becomes non-negligible")
    print("=" * 78)
    alpha_star = None
    for alpha in np.arange(0.0, 0.9001, 0.01):
        rate, _ = recalled_serious_success_rate(c, serious, success, float(alpha))
        if (rate - true_serious) > 2 * TOL:
            alpha_star = float(alpha)
            break
    all_pass &= check(
        "a finite crossover alpha* exists (claim is a REGIME, not absolute)",
        alpha_star is not None and 0.0 < alpha_star < 0.9,
        f"alpha* (inflation>{2*TOL:.0%}) ~ {alpha_star}",
    )

    # ---- SPF-1-F3 anti-cheat: hindsight-corrupted confidence re-creates the bias --
    # If the confidence used to define "serious" is the RETROSPECTIVE (hindsight) value
    # that is itself inflated for wins, even alpha=0 retention yields inflation, because
    # the SELECTION variable is now post-outcome. (Fischhoff 1975.)
    print()
    print("=" * 78)
    print("SPF-1-F3  --  hindsight-corrupted confidence smuggles the bias back in")
    print("=" * 78)
    HIND = 0.25  # wins get their recalled confidence bumped up by this much
    c_hind = np.clip(c + np.where(success, HIND, 0.0), 0.0, 1.0)
    serious_hind = c_hind >= SERIOUS_THRESHOLD
    rate_h, n_h = recalled_serious_success_rate(c_hind, serious_hind, success, alpha=0.0)
    all_pass &= check(
        "hindsight-defined 'serious' inflates even at alpha=0 (selection became post-outcome)",
        (rate_h - true_serious) > 2 * TOL,
        f"recalled {rate_h:.4f} vs target {true_serious:.4f} (+{rate_h-true_serious:.4f}); "
        f"=> confidence MUST be prospectively logged, not recalled",
    )

    print()
    print("=" * 78)
    print("RESONANCE-ONLY (NOT gated, ZERO evidential weight): no '2/3' or numerology")
    print("here. The only structural number is the user-chosen tolerance band; nothing")
    print("load-bearing depends on a recurring constant.")
    print("=" * 78)

    print()
    print(("ALL CHECKS PASSED" if all_pass else "SOME CHECKS FAILED"))
    return 0 if all_pass else 1


if __name__ == "__main__":
    raise SystemExit(main())
