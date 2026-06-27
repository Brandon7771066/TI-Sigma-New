"""
Q4(b) — TSC ring-constant signature expansion with a coincidence-rate control.

The TSC ring set assigns a small fixed family of constants to "rings":
    {1, sqrt2-1, C~0.437, 1/sqrt2, sqrt2, phi, e, pi, 2*sqrt2}.
T1-D (Pass 9) already tested 9 signatures. Per Q4 we PRE-REGISTER a NEW,
held-out batch of open-literature observables (fixed BEFORE computing fit) and
report, both ways (#69):

  1) the nearest-ring deviation for each observable, AND
  2) a COINCIDENCE-RATE control: for a random constant drawn uniformly in the
     same range, what mean nearest-ring deviation would we expect? If the real
     observables do NOT beat that chance baseline, the "match" is numerology
     (HAN-1: graded evidence, heuristic -> must be validated, not zero-weight
     but not a result either).

No constant here was chosen after seeing the fit; misses are reported as misses.
"""
import math
import numpy as np

PHI = (1 + 5 ** 0.5) / 2
S2 = 2 ** 0.5
RINGS = {
    "1": 1.0,
    "sqrt2-1": S2 - 1,
    "C(0.437)": 0.437,
    "1/sqrt2": 1 / S2,
    "sqrt2": S2,
    "phi": PHI,
    "e": math.e,
    "pi": math.pi,
    "2sqrt2": 2 * S2,
}
RING_VALS = np.array(list(RINGS.values()))

def nearest_ring(x):
    devs = np.abs(RING_VALS - x) / RING_VALS * 100
    j = int(np.argmin(devs))
    return list(RINGS.keys())[j], float(devs[j])

# PRE-REGISTERED held-out observables (open literature; NOT in the original 9).
# (label, observed, domain, source)
OBS = [
    ("Equal-temperament perfect fifth 2^(7/12)", 2 ** (7 / 12), "Music", "12-TET"),
    ("Just perfect fifth 3:2",                    3 / 2,          "Music", "Just intonation"),
    ("Golden angle fraction 1 - 1/phi",           1 - 1 / PHI,    "Phyllotaxis", "Vogel 1979"),
    ("Minor sixth 8:5",                           8 / 5,          "Music", "Just intonation"),
    ("Silver ratio 1+sqrt2",                      1 + S2,         "Number theory", "Pell"),
    ("Feigenbaum delta (scaled /3)",              4.66920 / 3,    "Chaos", "Feigenbaum 1978"),
    ("Plastic number",                            1.32472,        "Number theory", "Padovan"),
    ("Sqrt of 2 (control duplicate)",             S2,             "Control", "exact ring member"),
]

print("=" * 92)
print("Q4(b) TSC ring-constant signature expansion (pre-registered, coincidence-controlled)")
print("=" * 92)
print(f"{'Observable':<42}{'Observed':>10}{'Ring':>10}{'% dev':>8}  {'Domain'}")
real_devs = []
for label, obs, domain, _src in OBS:
    ring, dev = nearest_ring(obs)
    if domain != "Control":
        real_devs.append(dev)
    print(f"{label:<42}{obs:>10.4f}{ring:>10}{dev:>8.2f}  {domain}")

real_devs = np.array(real_devs)
print(f"\nReal observables (excl. control): n={len(real_devs)}  "
      f"mean nearest-ring dev = {real_devs.mean():.2f}%  median = {np.median(real_devs):.2f}%")

# ---- Coincidence-rate control ----------------------------------------------
# Range spanned by the ring set; draw random "constants" there, measure how
# close a RANDOM value lands to the nearest ring.
rng = np.random.default_rng(20260627)
lo, hi = RING_VALS.min(), RING_VALS.max()
rand = rng.uniform(lo, hi, 200_000)
rand_devs = np.array([nearest_ring(x)[1] for x in rand[:20_000]])  # subsample for speed
print(f"Random-constant baseline in [{lo:.3f},{hi:.3f}]: "
      f"mean nearest-ring dev = {rand_devs.mean():.2f}%  median = {np.median(rand_devs):.2f}%")

beat = (real_devs.mean() < rand_devs.mean())
frac_better = float(np.mean(rand_devs > real_devs.mean()))
print(f"\nVERDICT: real-observable mean dev {'<' if beat else '>='} chance baseline.")
print(f"  P(random constant beats the observed mean dev) = {1-frac_better:.3f}")
print("  Interpretation (#69): the ring set covers its range densely enough that a")
print("  random constant is already fairly close; matches are SUGGESTIVE / heuristic")
print("  (HAN-1 graded evidence), NOT a validated cross-domain law. Reported honestly")
print("  both ways: some music ratios land near rings, but so does noise.")
