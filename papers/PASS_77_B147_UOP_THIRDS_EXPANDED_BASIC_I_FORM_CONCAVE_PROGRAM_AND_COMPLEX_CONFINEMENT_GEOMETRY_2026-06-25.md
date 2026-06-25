# Pass 77 · B147 — The UOP, fully written out: thirds-expanded with `max`, in basic operations & in `i`, backed by a PROVEN optimization method, plus the complex-confinement geometry refinement

**Date:** 2026-06-25
**Status:** Presentational consolidation (Sections A–B) + TWO candidates (Section C **UCP-1**; Section D **CCG-1**), **NONE ratified**. Canonical principle **count unchanged 79**.
**Package:** `analyses/pass77_b147_uop_expanded_gradient_complex/uop_b147_checks.py` (+ `_output.txt`) — all checks pass.

> **Honesty rails honored throughout.** Sections A–B are exact-algebra / presentation upgrades (RAI-1, TPS-1): the same function written four ways, plus a representation in `i`. They add **zero new content**. Section C's gradient result backs **well-posedness and findability** of the optimum by a standard proven method — it is **necessary, not sufficient** (#69): it does **NOT** prove the UOP is the correct *normative* principle. Section D is a **geometry/representation** refinement (NAD-1 carve-at-joints), not a new principle. No numerology; the cap is **derived from `T_d`**, never typed as "0.93".

---

## Why this batch

The author asked, in plain terms, for four things and one cleanup:

1. The **new (thirds) version** of the UOP **fully expanded with the `max` function, in plain readable notation**.
2. The **full UOP written with just basic operations**, and **using `i`**.
3. To **back the UOP with a PROVEN optimization method** — *"gradient descent, which is used in AI."*
4. To **adjust UOP / PD / TI Sigma Graph / TI Sigma Crystal / 64D-matrix** now that ternary logic is confined to the **real** axis, **MI** to the **complex** plane only, and **N/A** to a **hyperimaginary `j`** with an **unspecified `j`-location AND a completely unspecified real location**.

Plus housekeeping on the `replit.md` ledger.

---

## Section A — the thirds UOP, fully expanded, with the `max`/clamp function (plain notation)

### A.1 The objective

Let an action `x` have a GILE-truth aggregate `G = G(x) ∈ [0,1]` (one number over all four GILE dims) and an existence map `H = H(x)`. Under **HEM-as-residual** with a unit budget, `H = 1 − G`. Let `T_d ∈ (0,1)` be the **domain's fixed truth-importance** (a property of the *field*, distinct from the optimized action-truth `G`), and set the domain weight

```
ρ  =  T_d / (1 − T_d).
```

The **UOP objective** is

```
J(x)  =  ρ · f_cap(G)  +  ln(1 + H),          H = 1 − G.
```

### A.2 `f_cap` written with `max` (one line, no piecewise branch)

The capacity function `f_cap` rewards truth (log-concave) but penalizes *over-reach* above the cap `G*`. Writing `over = max(0, G − G*)` (the amount you exceed the cap, zero below it):

```
f_cap(G)  =  ln( 1 + G − max(0, G − G*) )  −  α · [ max(0, G − G*) ]².
```

* Below the cap (`G ≤ G*`): `max(0, G − G*) = 0`, so `f_cap = ln(1 + G)` — pure log reward.
* Above the cap (`G > G*`): the log term **freezes at `ln(1 + G*)`** and a quadratic penalty `α·(G−G*)²` subtracts. (`α = 10` is the over-reach stiffness; any large `α` gives the same kinked optimum exactly at `G*`.)

This single line is **provably identical** to the original two-branch `f_cap` of B133 — verified to machine precision (max disagreement `2.2e-16`) in `Section 1` of the harness.

### A.3 The cap is the thirds clamp `min(1, max(0, 3·T_d − 1))`

The "new version" (B145) does **not** hard-code `0.93`. Optimizing the *plain* objective `J = ρ·ln(1+G) + ln(1 + (1−G))` over `G` gives the interior optimizer

```
G*(T_d)  =  (2ρ − 1)/(1 + ρ)  =  3·T_d − 1,
```

derived in two lines (substitute `ρ = T_d/(1−T_d)` and simplify; verified to `2.2e-16`). Clamped to the feasible `[0,1]` box, **the `max` function produces the three regimes** — this is the cleanest reading of "the new version with the 3 fully expanded with the max function":

```
G*_clamped(T_d)  =  min( 1,  max( 0,  3·T_d − 1 ) ).
```

| Regime | `T_d` | `G*_clamped` | Reading |
|---|---|---|---|
| Existence-only ("−") | `T_d ≤ 1/3` | `0` | truth irrelevant; spend all budget on Existence |
| Balanced / Myrion ("0") | `1/3 < T_d < 2/3` | `0 … 1` interior | the genuine trade-off |
| Truth-saturated ("+") | `T_d ≥ 2/3` | `1` | SAC-1 supererogatory; Existence does not bind |

At `T_d = 0.644111` the clamp returns `3·(0.644111) − 1 = 0.93233 = 1 − ½e⁻²` — **the canonical cap falls out of `T_d`, with no "0.93" written anywhere.** The "3" is honest structure: `3·T_d − 1 = 2·T_d − (1 − T_d)`, i.e. a two-sided existence floor `(1−T_d)` taken against `2·T_d` of truth pull — *form-contingent on the logs* (logged as contingency C5 in B145; trading the `λ=2 / e⁻²` posit for a `T_d ≈ 0.644` posit is an elegance/coherence upgrade, **not** a new derivation, and is **circular if `T_d` is picked to hit 0.93**).

---

## Section B — the full UOP in just basic operations, and using `i`

### B.1 Just basic operations (no `max`, no `min`)

`max(0, t)` is itself elementary: `max(0, t) = (t + |t|)/2` and `|t| = √(t²) = √(t·t)`. So the **entire UOP needs only `+ − × ÷` and a square root**. With `Δ = G − G*` and `over = (Δ + √(Δ²)) / 2`:

```
J  =  ρ · [ ln(1 + G − over)  −  α · over² ]  +  ln(2 − G),     ρ = T_d/(1 − T_d),

         where  over = ( (G − G*) + √((G − G*)²) ) / 2.
```

and the cap clamp likewise: `max(0,y) = (y + √(y²))/2`, `min(1,z) = 1 − (((1−z) + √((1−z)²))/2)`, so

```
G*  =  1  −  ( (1 − (3T_d − 1))  +  √( (1 − (3T_d − 1))² ) ) / 2 ,   then re-floored at 0 the same way.
```

This **basic-operations form is verified numerically identical** to the piecewise and `max` forms (`Section 1`, disagreement `2.2e-16`). (`ln` is the one transcendental kept; if a fully algebraic reward is ever wanted, any concave increasing surrogate slots in without changing the structure.)

### B.2 Using `i` — the truth argument is complex; the cap reads the **real** projection

The deeper sense of "using `i`" is the geometry (Section D): a proposition's truth-state is a number off the real line. Represent it as

```
z  =  d·1  +  m·i  +  n·j
```

with three orthogonal carriers: **real** `1` = ternary **degree** `d ∈ {−1, 0, +1}` (= {False, Indeterminate, True}); **imaginary** `i` = **MI / modality**; **hyperimaginary** `j` = **N/A / applicability**. The GILE-truth aggregate the UOP optimizes is built from the **real (ternary) projection only** — `G = ℜ-derived` — so the UOP reads `Re(z)`:

```
J  =  ρ · f_cap( Re(z) )  +  ln(1 + H),        Re(z) = d   (the ternary degree).
```

The consequences are exactly the new geometry: **MI = pure `+i`** contributes **nothing** to the capped truth aggregate (a modality clash is not a truth-degree), and **N/A on `j`** is **off the optimized plane entirely** (its real location is unspecified, so it cannot enter `G` at all). This is a faithful *re-statement* of the UOP in the corrected complex coordinates — a presentation, not a new claim (TPS-1/RAI-1).

---

## Section C — backing the UOP with a PROVEN optimization method (candidate **UCP-1**)

**UCP-1 (UOP-as-Concave-Program).** *The UOP objective `J(G)` is **concave** on the feasible budget box; therefore its maximization is (after sign flip) a **convex program**, and standard proven first-order methods — gradient ascent, the maximization twin of the gradient descent used to train AI — provably converge to its **unique global optimum** from **any** starting point, with **no spurious local optima**.*

**Why it's genuinely backed (not hand-waved).** `ln(1 + ·)` is concave; `min(u, G*)` is concave (min of concave/affine); `−α·[max(0,·)]²` is concave (negated convex); a sum of concave functions is concave. The harness confirms `J″(G) ≤ 0` everywhere for **both** formulations (max `J″ = −0.984 < 0`). Convex-optimization theory (Boyd & Vandenberghe 2004) then **guarantees** global convergence — this is a real theorem, not a simulation artifact.

**What the harness shows** (`Section 2`):
* **Concavity** of both `J_thirds` and `J_fcap` (`J″ ≤ 0`).
* **Gradient ascent** from 20 random inits, three regimes: `T_d = 0.40 → 0.20000`, `0.6441 → 0.93233`, `0.70 → 1.00000` — every start lands on the single thirds optimum (spread ≤ `5e-3`; the optimum sits at the `f_cap` **kink**, so a decaying step size is used — residual oscillation is expected non-smooth-optimum behaviour, not divergence).
* **Holistic 4-D**: optimizing four GILE dims with aggregate = mean drives the **aggregate** to `0.93233` while per-dimension allocation stays spread (`0.27`) — confirming the cap binds **holistically on the aggregate**, not per dimension.

**Honest scope (the rail).** This backs three things and **only** three: (i) the optimum **exists**, (ii) it is **unique**, (iii) it is **findable by a standard proven method**. It does **NOT** prove the UOP is the right *ethical/normative* principle — concavity is a property of the *chosen* objective, and a well-posed program with a unique optimum can still encode the wrong values. The normative content lives in the *choice* of `f_cap`, `ρ`, and the budget, which gradient descent takes as given. (#69: necessary, not sufficient.)

**Reconciliation surfaced as a bonus.** The two formulations express the cap two ways: the **thirds** model lets the cap *emerge* as `3T_d − 1`; the **fixed-penalty** `f_cap` model bakes it in at `G*`. They **coincide at `T_d ≈ 0.644`** (both `0.93233`). Above `T_d = 2/3` the thirds model **clamps the optimizer to 1.0** (truth-saturated) while the fixed-penalty model holds near `0.93` — which is precisely the **SAC-1** distinction ("above-cap is permissible when Existence does not bind"), now visible as two ways of writing the same cap.

**Falsifier UCP-1-F1 (OPEN).** Exhibit a faithful, agreed-upon casting of a real UOP decision whose objective is **non-concave** (genuine multiple local optima that gradient methods miss), *without* gerrymandering `f_cap`. If found, the "proven-method backing" weakens to "backing on the concave sub-class only."

---

## Section D — complex-confinement geometry (candidate **CCG-1**, refining TRR-1 / NAH-1)

**CCG-1 (Complex-Confinement Geometry).** *Three orthogonal carriers, each label confined to its own:*

| Carrier | Axis | Labels | Confinement rule |
|---|---|---|---|
| Real `1` | degree | **True `+1`, Indeterminate `0`, False `−1`** | ternary logic lives **here only** (Łukasiewicz-3) |
| Imaginary `i` | modality | **MI `= +i`** (conjugate `−i`) | MI is **pure-imaginary ONLY** — real part **0** |
| Hyperimaginary `j` | applicability | **N/A** | **`j`-location unspecified AND real location completely unspecified** |

This **refines** two prior statements and **corrects** one:

* **Refines B145 TRR-1**: ternary on the real axis ✓ — and now adds the *strict* clauses "MI on the complex plane **only**" and "N/A's real coordinate is **unspecified**".
* **Refines B138 NAH-1**: NAH-1 placed N/A on a hyperimaginary `j` axis but **projected it to the origin `(0,0)`** on the truth plane. CCG-1 **withdraws the origin-pinning**: N/A is "high but imprecise" — its real location is *completely unspecified*, so a faithful decoder must treat the real coordinate as a **wildcard**, not 0.
* **Corrects the 64D matrix**: the `4³` closure **folds N/A → MI**. That is now **doubly wrong** — N/A and MI are on **different axes** (`j` vs `i`), and N/A cannot even be pinned to a fixed point on the truth plane. The matrix's MR slice should carry MI on `i`; N/A is screened *first* (pre-base-4) and sits off-plane on `j`.

**What the harness shows** (`Section 3`): (a) {T,I,F} have zero `i` and zero `j` → real only; (b) MI has real = 0, `j` = 0, `i ≠ 0` → complex-plane only; (c) MI is never classified N/A (different axes); (d) 200 N/A tokens with random real ∈ `[−3, 2]` and random `j` ∈ `[0.3, 5]` are all still N/A, and a fixed-origin decoder would misrank `81/200` as "far from prototype" → origin-pinning is unfaithful.

### D.1 Representation-by-representation adjustments

* **Scalar PD (`−3 … +2`)** — the signed **real** axis now carries **only the ternary degree** {T, I, F}. **MI is NOT on this line** (it was placed "near False" — withdrawn; MI is off-axis on `i`). **N/A is off-axis on `j`** with unspecified real position. So scalar PD is, honestly, a **ternary** instrument; it **cannot** represent MI or N/A (it has no `i` or `j`).
* **Complex PD (`real + i`)** — real = ternary degree, `i` = MI modality. It represents **{T, I, F, MI}** faithfully but **cannot hold N/A** (N/A needs `j`). The old "NA = `−e·i`" placement is **withdrawn** (that put N/A on the `i`-axis; N/A is on `j`).
* **TI Sigma Graph (TIG)** — the real-axis projection plus the `i` vertex: ternary on the real, MI at the `i` vertex; **N/A is not representable** on the 2-D graph (it lives on the third `j` axis).
* **TI Sigma Crystal / TECC** — the codewords for {T, F, I} sit on the real shell, MI on the `i`-plane; the **N/A codeword carries a wildcard real coordinate** (and an unspecified `j` magnitude) rather than a fixed point — the decoder must accept a *region*, not a vertex, for N/A.
* **64D GILE Matrix** — stop folding N/A into MI; the matrix natively covers the on-plane base-4 (real `T/F/I`, imaginary `MI`); **N/A is an off-matrix pre-screen** on `j`.
* **UOP** — unaffected in value (it already optimizes the real GILE aggregate); Section B.2 makes explicit that it reads `Re(z)` only, so MI (`i`) and N/A (`j`) correctly contribute nothing to the capped truth aggregate.

**Falsifier CCG-1-F1 (OPEN).** Exhibit a genuine proposition that is **uncontroversially N/A** yet has a **determinate, agreed real truth-degree** (a fixed non-wildcard real location). If such cases are common, the "completely unspecified real location" clause is too strong and N/A collapses back toward an on-plane point.

---

## Cross-references & consistency

* **B145** (thirds URR-1 / TRR-1): Section A is the requested full expansion of that "new version"; Section D tightens TRR-1.
* **B138** (NAH-1): Section D refines its origin-projection to a wildcard.
* **B133/B134** (UOP grounding, `f_cap`, universality): Section A.2 re-expresses the same `f_cap`; Section C adds the concave-program property as proven-method backing.
* **SAC-1 / HRR-1** (above-cap supererogation, HEM-as-residual): Section C's reconciliation note makes the two cap-formulations' divergence above `T_d = 2/3` *be* the SAC-1 distinction.
* Count stays **79**: UCP-1 and CCG-1 are **candidates**; Sections A–B are presentation (TPS-1/RAI-1).

## Open falsifiers introduced
* **UCP-1-F1** — a faithful non-concave UOP casting (ungerrymandered) would limit the proven-method backing.
* **CCG-1-F1** — a common N/A-with-determinate-real-degree would refute "completely unspecified real location".
