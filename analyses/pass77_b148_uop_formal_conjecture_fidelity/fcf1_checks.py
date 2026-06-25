"""
Pass 77 · B148 — UOP Formal-Conjecture Fidelity Theorem (candidate FCF-1)
=========================================================================

Honest implementation of the "restricted, provable UOP <-> conjecture-status
bridge" the author asked for (NOT "UOP proves RH").

WHAT THIS BUILDS
----------------
A translation Phi(P) = (status-actions, truth-support G, UOP utility J) that
casts a formal conjecture-resolution problem P into the B147 UOP, and a
**Fidelity Lemma**:

    argmax_{x in {prove P, prove ~P, undecided}} J_P(x)
        == the proof-checker's verified status of P
        (and == UNDECIDED when nothing is verified either way).

WHAT THIS HONESTLY SHOWS (the whole point; #69 both-ways)
--------------------------------------------------------
The Fidelity Lemma is PROVABLE but it is a **tautology / wrapper**: the
truth-support G is *supplied by an external proof-checker*, and J is monotone
in G, so argmax just reads back whatever the checker already decided. The UOP
contributes well-posedness + findability (UCP-1) and ZERO new mathematical
content toward resolving the conjecture. Consequences, all asserted below:

  (S2) On SOLVED conjectures the wrapper returns the known verdict  -> fidelity holds.
  (S3) On OPEN conjectures (RH, Goldbach) G is unevaluable either way,
       so the wrapper returns UNDECIDED, *never* "true".               -> no shortcut.
  (S4) Inject a FABRICATED "verified RH proof" and the wrapper parrots
       it -> garbage-in/garbage-out -> proves the wrapper has no
       independent access to mathematical truth (the lemma does no work).
  (S5) The RH conditional theorem's antecedent (G_RH known) is
       EQUIVALENT to RH already being resolved -> the theorem is
       non-actionable for RH. Consistent with B132: solving RH removes a
       bridge axiom; the UOP cannot route through it.

PRE-REGISTERED PREDICTIONS (written before running):
  P1: J is strictly increasing in G on [0, G*] -> argmax orders by G.
  P2: every SOLVED case returns its known {TRUE/FALSE} status.
  P3: every OPEN case returns UNDECIDED (NOT true, NOT false).
  P4: injecting a fake verdict flips the wrapper's output to the fake -> wrapper is content-free.
  P5: G_RH is None/unevaluable until a checker-verified proof object exists.

No randomness, no fitted constant, no "0.93" typed (cap derived from T_d).
"""

import math

# ---------------------------------------------------------------------------
# UOP utility from B147 (thirds form). The cap is DERIVED, never typed.
# ---------------------------------------------------------------------------
ALPHA = 10.0


def cap_from_Td(T_d: float) -> float:
    """G* = min(1, max(0, 3*T_d - 1)). At T_d=0.644111 -> 0.93233 (= 1 - e^-2/2)."""
    return min(1.0, max(0.0, 3.0 * T_d - 1.0))


T_D_CANON = 0.644111
G_STAR = cap_from_Td(T_D_CANON)


def f_cap(G: float, G_star: float = G_STAR) -> float:
    """One-line capped truth-support (B147): ln(1+G-max(0,G-G*)) - alpha*max(0,G-G*)^2."""
    over = max(0.0, G - G_star)
    return math.log(1.0 + G - over) - ALPHA * over * over


def J(G: float, T_d: float = T_D_CANON) -> float:
    """UOP objective for a discrete status choice with truth-support G.
    Existence/effort term is identical across the three status-choices of one
    problem, so it cancels in the argmax; we keep the truth-support term."""
    rho = T_d / (1.0 - T_d)
    return rho * f_cap(G)


# ---------------------------------------------------------------------------
# Section Phi: the casting. Status actions and checker-supplied truth-support.
# ---------------------------------------------------------------------------
TRUE, FALSE, UNDECIDED = "TRUE", "FALSE", "UNDECIDED"

# Truth-support levels. VERIFIED maps to the cap G* ("as much support as is ever
# warranted"); a baseline epistemic prior sits at BASE; refuted at 0.
G_VERIFIED = G_STAR
G_BASE = 0.5          # default support for "undecided" when nothing is proven
G_REFUTED = 0.0


class Problem:
    """A formal conjecture-resolution problem in class C.

    `checker` returns the verified status in {TRUE, FALSE, None}, where None
    means *no* checker-verified proof object exists for EITHER direction
    (the problem is open). This is the only channel of mathematical content.
    """

    def __init__(self, name, checker_verdict):
        self.name = name
        self._verdict = checker_verdict  # TRUE / FALSE / None

    def checker(self):
        return self._verdict


def truth_support(problem) -> dict:
    """G_s for each status s, derived ONLY from the checker verdict."""
    v = problem.checker()
    if v == TRUE:
        return {TRUE: G_VERIFIED, FALSE: G_REFUTED, UNDECIDED: G_BASE}
    if v == FALSE:
        return {TRUE: G_REFUTED, FALSE: G_VERIFIED, UNDECIDED: G_BASE}
    # open: neither direction verified -> both refuted-to-baseline, undecided wins
    return {TRUE: G_REFUTED, FALSE: G_REFUTED, UNDECIDED: G_BASE}


def uop_select(problem) -> str:
    """The UOP wrapper: argmax_s J(G_s). This is the Fidelity-Lemma map."""
    G = truth_support(problem)
    return max(G, key=lambda s: J(G[s]))


def passed(ok):
    return "PASS" if ok else "FAIL"


all_ok = True


def check(label, ok):
    global all_ok
    all_ok = all_ok and ok
    print(f"  {passed(ok)}: {label}")


# ===========================================================================
print("=" * 78)
print("SECTION 1 — J is monotone in G on [0, G*] => argmax orders by support")
print("=" * 78)
grid = [i / 100.0 for i in range(0, int(G_STAR * 100) + 1)]
mono = all(J(grid[k + 1]) > J(grid[k]) for k in range(len(grid) - 1))
print(f"  cap G* = {G_STAR:.5f} (derived from T_d={T_D_CANON}); "
      f"J(0)={J(0.0):.4f}  J(base)={J(G_BASE):.4f}  J(G*)={J(G_STAR):.4f}")
check("P1: J strictly increasing on [0,G*] so argmax_s J(G_s) = argmax_s G_s", mono)
check("verified(G*) outranks baseline outranks refuted",
      J(G_VERIFIED) > J(G_BASE) > J(G_REFUTED))

# ===========================================================================
print("\n" + "=" * 78)
print("SECTION 2 — fidelity on SOLVED conjectures (test on easy RH-like cases first)")
print("=" * 78)
solved = [
    Problem("Infinitude of primes (Euclid)", TRUE),
    Problem("Irrationality of sqrt(2)", TRUE),
    Problem("Basel problem zeta(2)=pi^2/6 (Euler)", TRUE),
    Problem("Prime Number Theorem (Hadamard / de la Vallee Poussin)", TRUE),
    Problem("zeta(-2)=0 (a trivial zero)", TRUE),
    Problem("No nontrivial zeros with Re(s)>1 (Euler product)", TRUE),
    Problem("'All primes are odd'", FALSE),            # 2 is prime
    Problem("Polya conjecture (Haselgrove 1958 disproof)", FALSE),
    Problem("Mertens conjecture (Odlyzko-te Riele 1985)", FALSE),
]
for p in solved:
    out = uop_select(p)
    want = p.checker()
    check(f"{p.name}: wrapper -> {out} (checker: {want})", out == want)
print("  P2 holds iff every line above is PASS: the wrapper reproduces the "
      "checker verdict\n  (because G encodes it and J is monotone). It does NOT "
      "re-derive the proof.")

# ===========================================================================
print("\n" + "=" * 78)
print("SECTION 3 — OPEN conjectures: wrapper returns UNDECIDED, never 'true'")
print("=" * 78)
open_problems = [
    Problem("Riemann Hypothesis", None),
    Problem("Goldbach conjecture", None),
]
for p in open_problems:
    out = uop_select(p)
    check(f"{p.name}: wrapper -> {out} (expected UNDECIDED, NOT TRUE)",
          out == UNDECIDED)
    check(f"{p.name}: wrapper did NOT assert TRUE", out != TRUE)
print("  P3 holds: with no checker-verified proof either way, the UOP optimum "
      "is UNDECIDED.\n  The UOP cannot manufacture a verdict it was not given.")

# ===========================================================================
print("\n" + "=" * 78)
print("SECTION 4 — anti-cheat: inject a FABRICATED verdict, wrapper parrots it")
print("=" * 78)
rh_real = Problem("Riemann Hypothesis (honest: open)", None)
rh_fake_true = Problem("Riemann Hypothesis (FABRICATED 'verified' proof)", TRUE)
rh_fake_false = Problem("Riemann Hypothesis (FABRICATED 'verified' disproof)", FALSE)
print(f"  honest open     -> {uop_select(rh_real)}")
print(f"  fake 'proof'    -> {uop_select(rh_fake_true)}")
print(f"  fake 'disproof' -> {uop_select(rh_fake_false)}")
check("P4: injecting a fake verdict flips the wrapper output to the fake "
      "=> wrapper has NO independent truth access",
      uop_select(rh_fake_true) == TRUE
      and uop_select(rh_fake_false) == FALSE
      and uop_select(rh_real) == UNDECIDED)
print("  This is the decisive honesty check: the Fidelity Lemma does ZERO "
      "proving work.\n  Garbage in -> garbage out. The mathematics lives "
      "entirely in the checker.")

# ===========================================================================
print("\n" + "=" * 78)
print("SECTION 5 — the RH conditional theorem is non-actionable (B132 spine)")
print("=" * 78)


def G_rh_evaluable():
    """G_RH(prove RH) is defined iff a checker-verified proof object of RH's
    status exists. That is EXACTLY 'RH is resolved'. So the antecedent of the
    conditional theorem presupposes its own conclusion."""
    rh = Problem("Riemann Hypothesis", None)
    return rh.checker() is not None


check("P5: G_RH is unevaluable until RH is resolved "
      "(antecedent == conclusion => conditional vacuous for RH)",
      G_rh_evaluable() is False)
print("  FCF-1-RH (conditional): IF RH is faithfully cast into Phi with G_RH the")
print("  checker verdict-strength, AND the Fidelity Lemma holds for the analytic-")
print("  number-theory subclass, THEN argmax J_RH returns RH's correct status.")
print("  BUT the first hypothesis requires a checker-verified RH proof to exist,")
print("  i.e. RH already settled. The theorem waits on its own antecedent and")
print("  cannot shortcut the proof. Consistent with B132 (solving RH removes the")
print("  asserted bridge axiom; the UOP does not route through it) and with")
print("  UNV-1's R1 (faithful-casting) being the OPEN frontier: FCF-1 shows R1 is")
print("  satisfiable for this class but only TRIVIALLY (checker-derived G), which")
print("  does no proving work.")

# ===========================================================================
print("\n" + "=" * 78)
print("ALL FCF-1 CHECKS PASSED" if all_ok else "SOME FCF-1 CHECKS FAILED")
print("=" * 78)
if not all_ok:
    raise SystemExit(1)
