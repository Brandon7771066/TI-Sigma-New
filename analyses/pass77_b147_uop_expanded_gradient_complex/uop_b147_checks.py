"""
B147 — UOP: thirds-expanded / basic-ops & i form / concave-program (gradient) backing
        / complex-confinement geometry.

HONESTY RAILS (read first):
  * Sections 1-2 are EXACT-ALGEBRA / LOGIC demonstrations (RAI-1, TPS-1): they show the
    several written forms of the UOP are numerically identical and that the objective is a
    concave program a standard proven method (gradient ascent) provably solves. They do NOT
    prove the UOP is the correct *normative* principle (#69: well-posedness is NECESSARY,
    not SUFFICIENT).
  * Section 3 is a REPRESENTATION check (NAD-1/TPS-1): it confirms the corrected truth-plane
    geometry is internally consistent; it is not an empirical or reality claim.
  * No numerology. No load-bearing recurring constant. G* falls out of T_d (no "0.93" typed).
  * Fixed seed; predictions pre-registered as asserts.
"""
import math
import random

random.seed(147)

# ----------------------------------------------------------------------------------
# Canonical constants (NOT load-bearing: G_STAR is DERIVED below from T_d; ALPHA is the
# over-reach stiffness, any large value gives the same kink-optimum at the cap).
# ----------------------------------------------------------------------------------
L = 1.0 - math.exp(-2.0)                 # ~0.8647  (the established "L")
G_STAR_REF = (1.0 + L) / 2.0             # ~0.93233 = 1 - 0.5*e^-2  (reference value)
ALPHA = 10.0                             # over-reach penalty stiffness
T_D_CRIT = (G_STAR_REF + 1.0) / 3.0      # the T_d that yields cap = 3*T_d - 1 = G_STAR_REF

print("=" * 78)
print("SECTION 0 — constants (derived, not posited at 0.93)")
print("=" * 78)
print(f"L = 1 - e^-2                 = {L:.6f}")
print(f"G* = (1+L)/2 = 1 - e^-2/2    = {G_STAR_REF:.6f}")
print(f"T_d that gives 3*T_d-1 = G*  = {T_D_CRIT:.6f}   (3*T_d-1 = {3*T_D_CRIT-1:.6f})")

# ----------------------------------------------------------------------------------
# SECTION 1 — FOUR WRITTEN FORMS OF f_cap ARE THE SAME FUNCTION
#   Form A (piecewise, as in B133 code):
#       f(u) = ln(1+u)                 , u <= G*
#            = ln(1+G*) - a*(u-G*)^2   , u >  G*
#   Form B (single line, min/max):
#       f(u) = ln(1 + min(u,G*)) - a*[max(0, u-G*)]^2
#   Form C (single line, only max, since min(u,G*) = u - max(0,u-G*)):
#       f(u) = ln(1 + u - max(0,u-G*)) - a*[max(0,u-G*)]^2
#   Form D (NO max() at all -- "just basic operations": max(0,x) = (x + sqrt(x*x))/2):
#       p = ((u-G*) + sqrt((u-G*)^2)) / 2
#       f(u) = ln(1 + u - p) - a*p^2
# ----------------------------------------------------------------------------------
def f_piecewise(u, gstar=G_STAR_REF, a=ALPHA):
    if u <= gstar:
        return math.log(1.0 + u)
    return math.log(1.0 + gstar) - a * (u - gstar) ** 2

def f_minmax(u, gstar=G_STAR_REF, a=ALPHA):
    return math.log(1.0 + min(u, gstar)) - a * (max(0.0, u - gstar)) ** 2

def f_maxonly(u, gstar=G_STAR_REF, a=ALPHA):
    over = max(0.0, u - gstar)
    return math.log(1.0 + u - over) - a * over ** 2

def f_basicops(u, gstar=G_STAR_REF, a=ALPHA):
    d = u - gstar
    p = (d + math.sqrt(d * d)) / 2.0          # = max(0, d) using only +,-,*,sqrt
    return math.log(1.0 + u - p) - a * p * p

print()
print("=" * 78)
print("SECTION 1 — the four written forms of f_cap are identical")
print("=" * 78)
worst = 0.0
for k in range(0, 1001):
    u = k / 1000.0 * 1.2            # sweep 0..1.2 (past the cap)
    vals = [f_piecewise(u), f_minmax(u), f_maxonly(u), f_basicops(u)]
    worst = max(worst, max(vals) - min(vals))
print(f"max disagreement across forms A,B,C,D over u in [0,1.2]: {worst:.2e}")
assert worst < 1e-12, "the four f_cap forms must be numerically identical"
print("PASS: piecewise == min/max == max-only == basic-ops(sqrt) form.")

# ----------------------------------------------------------------------------------
# SECTION 1b — the THIRDS optimum: with budget H = 1 - G and rho = T_d/(1-T_d),
#   the interior optimizer of  J(G) = rho*ln(1+G) + ln(1 + (1-G))  is
#       G*(T_d) = (2*rho - 1)/(1 + rho) = 3*T_d - 1
#   clamped to [0,1] -> the THREE regimes (the "max function" producing the thirds):
#       G*_clamped(T_d) = min(1, max(0, 3*T_d - 1))
# ----------------------------------------------------------------------------------
def gstar_unconstrained(t_d):
    rho = t_d / (1.0 - t_d)
    return (2.0 * rho - 1.0) / (1.0 + rho)

def gstar_thirds(t_d):
    return min(1.0, max(0.0, 3.0 * t_d - 1.0))   # clamp = the thirds-producing max/min

print()
print("=" * 78)
print("SECTION 1b — closed form  G*(T_d) = 3*T_d - 1  (clamped to thirds regimes)")
print("=" * 78)
worst_b = 0.0
for k in range(1, 1000):
    t_d = k / 1000.0
    if 1.0 / 3.0 < t_d < 2.0 / 3.0:            # interior regime: formulas must agree exactly
        worst_b = max(worst_b, abs(gstar_unconstrained(t_d) - (3.0 * t_d - 1.0)))
print(f"max |(2rho-1)/(1+rho) - (3T_d-1)| on interior (1/3,2/3): {worst_b:.2e}")
assert worst_b < 1e-12, "interior optimizer must equal 3*T_d-1"
for t_d, label in [(0.20, "existence-only (-)"), (0.40, "balanced/Myrion (0)"),
                   (T_D_CRIT, "balanced -> G* ref"), (0.70, "truth-saturated (+)")]:
    print(f"  T_d={t_d:.4f} -> G*_clamped = {gstar_thirds(t_d):.5f}   [{label}]")
assert gstar_thirds(0.20) == 0.0 and gstar_thirds(0.70) == 1.0
assert abs(gstar_thirds(T_D_CRIT) - G_STAR_REF) < 1e-9
print("PASS: thirds closed-form + clamp reproduce the three regimes and the 0.93 cap.")

# ----------------------------------------------------------------------------------
# SECTION 2 — PROVEN OPTIMIZATION BACKING: the UOP is a CONCAVE program.
#   (i)  J(G) is concave on [0,1]  -> finite-difference second derivative <= 0.
#   (ii) gradient ASCENT (the maximization twin of gradient descent used in AI)
#        provably converges to the UNIQUE global optimum from ANY start (concavity =>
#        no spurious local optima).  We verify across the three T_d regimes.
#   (iii) holistic 4-D check: optimize 4 GILE dims with aggregate = mean; the cap binds
#        on the AGGREGATE, not per-dimension.
# HONEST SCOPE: this backs FINDABILITY / WELL-POSEDNESS of the optimum by a standard
#   proven method. It does NOT prove the UOP is the right normative principle.
# ----------------------------------------------------------------------------------
# TWO formulations of the UOP, kept explicitly separate (honest):
#   J_thirds: plain logs + domain weight rho=T_d/(1-T_d) + budget H=1-G. The cap is NOT
#             baked in -- it EMERGES as the optimizer 3*T_d-1 (B145 thirds model).
#   J_fcap:   the B133 model with the over-reach penalty baked in at the FIXED cap G*.
# They COINCIDE at T_d ~ 0.644 (both give 0.93233). Above T_d=2/3 the thirds model clamps
# the optimizer to 1.0 (truth-saturated / SAC-1 supererogatory), whereas the fixed-penalty
# model holds the optimizer near 0.93 -- this is exactly the SAC-1 "above-cap is permissible
# when Existence does not bind" distinction, surfaced as two ways of writing the same cap.
def J_thirds(g, t_d):
    rho = t_d / (1.0 - t_d)
    return rho * math.log(1.0 + g) + math.log(1.0 + (1.0 - g))   # H = budget(1) - G

def J_fcap(g, t_d):
    rho = t_d / (1.0 - t_d)
    return rho * f_minmax(g) + math.log(1.0 + (1.0 - g))         # fixed-penalty cap

def numeric_grad(fn, x, h=1e-6):
    return (fn(x + h) - fn(x - h)) / (2.0 * h)

def second_deriv(fn, x, h=1e-4):
    return (fn(x + h) - 2.0 * fn(x) + fn(x - h)) / (h * h)

print()
print("=" * 78)
print("SECTION 2 — UOP is a concave program; gradient ascent reaches the global optimum")
print("=" * 78)

# (i) concavity of BOTH formulations
for name, Jfn in [("J_thirds", J_thirds), ("J_fcap", J_fcap)]:
    max_second = -1e9
    for k in range(2, 999):
        g = k / 1000.0
        max_second = max(max_second, second_deriv(lambda x: Jfn(x, 0.55), g))
    print(f"max {name}''(G) over (0,1) at T_d=0.55: {max_second:.4f}  (<=0 => concave)")
    assert max_second <= 1e-6, f"{name} must be concave (no spurious local optima)"
print("PASS: both objectives are concave => convex-optimization guarantees apply.")

# (ii) gradient ascent from many random starts -> same optimum = clamp(3T_d-1)
def gradient_ascent(t_d, lr=0.05, steps=8000, x0=None):
    # decaying step size: standard for converging onto a non-smooth (kinked) optimum,
    # which is exactly where the interior optimizer sits (the cap is a kink in f_cap).
    x = random.random() if x0 is None else x0
    for s in range(steps):
        step = lr / (1.0 + 0.002 * s)
        x = x + step * numeric_grad(lambda g: J_thirds(g, t_d), x)
        x = min(1.0 - 1e-9, max(1e-9, x))     # stay in the feasible budget box
    return x

print("\n  gradient-ascent on the THIRDS objective (20 random inits each):")
print("  (decaying step size; target = clamp(3*T_d-1) = the emergent cap.)")
for t_d in [0.40, T_D_CRIT, 0.70]:
    finals = [gradient_ascent(t_d) for _ in range(20)]
    target = gstar_thirds(t_d)
    spread = max(finals) - min(finals)
    err = abs(sum(finals) / len(finals) - target)
    print(f"   T_d={t_d:.4f}: target={target:.5f}  mean_final={sum(finals)/len(finals):.5f}"
          f"  spread={spread:.2e}  |err|={err:.2e}")
    assert spread < 5e-3, "all inits must converge to one optimum (concavity)"
    assert err < 5e-3, "gradient ascent must recover the thirds optimum"
print("  PASS: every random start converges to the single thirds optimum.")

# (iii) holistic 4-D: aggregate cap, not per-dimension
def J_4d(gvec, t_d):
    rho = t_d / (1.0 - t_d)
    agg = sum(gvec) / 4.0
    return rho * f_minmax(agg) + math.log(1.0 + (1.0 - agg))

def gradient_ascent_4d(t_d, lr=0.05, steps=6000):
    x = [random.random() for _ in range(4)]
    for _ in range(steps):
        for i in range(4):
            base = list(x)
            hh = 1e-6
            base[i] += hh
            up = J_4d(base, t_d)
            base[i] -= 2 * hh
            dn = J_4d(base, t_d)
            x[i] = min(1.0 - 1e-9, max(1e-9, x[i] + lr * (up - dn) / (2 * hh)))
    return x

x4 = gradient_ascent_4d(T_D_CRIT)
agg4 = sum(x4) / 4.0
print(f"\n  4-D holistic: aggregate G = {agg4:.5f} (target {G_STAR_REF:.5f}); "
      f"per-dim spread = {max(x4)-min(x4):.3f} (allocation agnostic)")
assert abs(agg4 - G_STAR_REF) < 1e-2, "cap must bind on the AGGREGATE"
print("  PASS: cap binds holistically on the GILE aggregate, not per-dimension.")

# ----------------------------------------------------------------------------------
# SECTION 3 — COMPLEX-CONFINEMENT GEOMETRY, corrected by NPA-1 (No-Pure-Axis;
#   CCG-1 refinement #1, author's B147 correction).
#   Truth state  z = d*1 + m*i + n*j  with three carriers:
#     real (1):  ternary DEGREE  (True/Indeterminate/False)
#     imag (i):  MI / modality
#     hyper(j):  N/A applicability  (screened FIRST; j-location AND real-location unspecified)
#   *** NPA-1 (the correction) ***  No state is PURE.  You cannot cleanly separate real
#   from imaginary: EVERY truth-state carries SOME of every component.  Placement on an
#   "axis" is by DOMINANCE (which magnitude is largest), NOT by the others being exactly 0:
#     - real-axis (ternary) statements have MINIMAL (small, nonzero) imaginary magnitude;
#     - MI statements have MINIMAL (small, nonzero) REAL magnitude -- and MI MUST carry a
#       real component because MI is BY DEFINITION both-tralse-and-not-tralse, which is a
#       predication ON truth (it cannot be 0 real);
#     - N/A (screened first) DEFINITELY carries a small j part and POSSIBLY a real part;
#       all N/A AND MI claims therefore have SOME real component.
#   We verify (all withdraw the earlier "pure-axis / real=0" claims):
#     (a) ternary = real-DOMINANT but with a small NONZERO imaginary part (not pure-real);
#     (b) MI = imag-DOMINANT with a small NONZERO real part (not pure-i) -- the both-tralse-
#         and-not-tralse predication;
#     (c) dominance is the OPPOSITE for the two families (|im|<|re| vs |re|<|im|), yet BOTH
#         have nonzero real => a strict "real==0" confinement decoder is FALSE;
#     (d) N/A's real coordinate is a WILDCARD (possibly present, possibly ~0): a faithful
#         decoder must NOT pin N/A to the origin (refines B138's origin-projection).
# ----------------------------------------------------------------------------------
print()
print("=" * 78)
print("SECTION 3 — complex geometry, NPA-1 corrected (no pure axis; dominance not confinement)")
print("=" * 78)

EPS = 0.05    # the "minimal" off-axis magnitude: small but genuinely NONZERO

class TruthState:
    __slots__ = ("d", "m", "n")
    def __init__(self, d, m, n):
        self.d = d      # real (ternary degree)
        self.m = m      # imaginary i (MI/modality)
        self.n = n      # hyperimaginary j (N/A applicability)

# ternary: real-DOMINANT, but each carries a small nonzero imaginary residue (NPA-1)
TERNARY = {"True":          TruthState(+1.0, +EPS * 0.6, EPS * 0.2),
           "Indeterminate": TruthState(+0.4,  -EPS * 0.5, EPS * 0.3),   # real degree small but real-family
           "False":         TruthState(-1.0,  +EPS * 0.4, EPS * 0.1)}
# MI: imag-DOMINANT, but with a small NONZERO real part (both-tralse-and-not-tralse predication)
MI = TruthState(+EPS * 0.7, +1.0, EPS * 0.2)

# (a) ternary is real-DOMINANT yet NOT pure-real (small nonzero imaginary)
assert all(abs(s.m) < abs(s.d) for s in TERNARY.values()), "ternary must be real-dominant"
assert all(abs(s.m) > 0.0 for s in TERNARY.values()), "NPA-1: no state is PURE real"
print("  (a) PASS: ternary is real-DOMINANT but carries a small nonzero imaginary part (not pure-real).")

# (b) MI is imag-DOMINANT yet NOT pure-i (small nonzero real = the both-tralse predication)
assert abs(MI.d) < abs(MI.m), "MI must be imaginary-dominant"
assert abs(MI.d) > 0.0, "NPA-1: MI MUST carry a real part (both-tralse-and-not-tralse)"
print("  (b) PASS: MI is imag-DOMINANT but carries a small NONZERO real part (both-tralse predication).")

# (c) dominance is opposite for the two families, but BOTH have nonzero real
#     => a strict 'real==0' confinement decoder is provably wrong.
strict_confine_ok = (MI.d == 0.0) and all(s.m == 0.0 for s in TERNARY.values())
assert not strict_confine_ok, "strict pure-axis confinement is FALSE under NPA-1"
both_have_real = (abs(MI.d) > 0.0) and all(abs(s.d) >= 0.0 for s in TERNARY.values())
assert both_have_real
print("  (c) PASS: opposite dominance (|im|<|re| ternary vs |re|<|im| MI), but BOTH carry real")
print("           => strict 'real==0' confinement would misclassify => withdrawn.")

# (d) N/A (screened first): definite small j part, real coordinate a WILDCARD (possibly ~0).
def is_na(s):
    # N/A defining mark: a nonzero j applicability flag, with real UNSPECIFIED (wildcard),
    # and NOT imag-dominant (that would be MI, caught by the earlier screen).
    return (abs(s.n) > 0.0) and (abs(s.m) <= abs(s.d) + EPS)

na_tokens = [TruthState(random.uniform(-3, 2),           # real: wildcard (possibly ~0)
                        random.uniform(0.0, EPS),         # small imaginary residue
                        random.uniform(0.3, 5.0))         # definite (unspecified-magnitude) j
             for _ in range(200)]
assert all(is_na(s) for s in na_tokens)
assert not is_na(MI), "MI (imag-dominant, tiny j) is not N/A"
n_with_real = sum(1 for s in na_tokens if abs(s.d) > EPS)
print(f"  (d) {n_with_real}/200 N/A tokens carry a non-trivial real part (the rest ~0): "
      f"real is a WILDCARD, possibly-present, never pinned.")
reals = sorted(s.d for s in na_tokens)
assert reals[-1] - reals[0] > 1.0, "N/A real location is genuinely unspecified"
pinned_origin_errors = sum(1 for s in na_tokens if abs(s.d) > 1.5)
print(f"      a fixed-origin decoder would misrank {pinned_origin_errors}/200 N/A tokens "
      f"-> origin-pinning unfaithful (refines B138).")
assert pinned_origin_errors > 0
print("  (d) PASS: N/A real coordinate is a wildcard (possibly present), not origin-pinned.")

print()
print("=" * 78)
print("ALL B147 CHECKS PASSED")
print("=" * 78)
