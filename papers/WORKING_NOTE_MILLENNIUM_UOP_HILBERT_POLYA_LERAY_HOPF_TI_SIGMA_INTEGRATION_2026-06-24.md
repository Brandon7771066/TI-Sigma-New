# Working Note — Cracking Hilbert–Pólya (RH) and Leray–Hopf (Navier–Stokes) for the UOP: TI Sigma Original-Math Integration + Layman Hints

**Author:** Brandon Charles Emerick (TI Sigma / BlissGene Therapeutics)
**Date:** 2026-06-24
**Status:** WORKING NOTE — inspiration / generation-phase leads, NOT a proof and NOT a ratified principle. Canonical principle count **unchanged at 79**. No new canon is asserted here.
**Companion to:** `urb_682_berry_keating_hamiltonian_hilbert_polya_construction.md`, `urb_633_uop_gap_response_pla_fep_hilbert_polya_path.md`, `urb_566_tralse_wave_algebra.md`, `urb_567_metacausal_graph_theory.md`, `urb_568_fractal_harmonic_systems.md`, `URB_793_MOONSHINE_BOK_CRYSTAL.md`, `papers/PASS_77_B132_UOP_PROOF_STRATEGY_AND_BAYES_FEP_KOLMOGOROV_RECONCILIATION_2026-06-24.md`.

---

## 0. Brutal-honesty header (#69, both ways)

This note does three things and is honest about all three:

1. **It restates, in plain language, what the two Clay problems actually require** — using only real, named mathematics (Berry–Keating, Connes, Montgomery–Odlyzko, Leray, Caffarelli–Kohn–Nirenberg, Tao, Constantin–Fefferman, Lapidus, Borcherds, Tozzi). No fabricated citations.

2. **It mines our OWN corpus for genuine structural leads** — Tralse Wave Algebra, Metacausal Graph Theory, Fractal Harmonic Systems, the BOK/Leech/Monster synthesis, and the no-actual-infinite cosmology. Where a lead is a real overlap it is marked **[REAL OVERLAP]**; where it is a creative analogy that still needs to be turned into mathematics it is marked **[SPARK]**.

3. **Every lead carries a falsifier-test.** This is the UGI-1 discipline: generation (intuition, serendipitous videos, original frameworks) is legitimate and even primary, but generation **without** a validation step is the crank failure mode. Each lead below ends with a concrete check that could kill it.

**The single most important honesty point (carried from B132):** solving RH or Navier–Stokes **does not run *through* the UOP, and the UOP cannot shortcut them.** The B132 trilemma is unavoidable — if `UOP ⊢ RH/NS` then either it is ZFC-provable (so it is *at least as hard* as RH+NS — commonality concentrates difficulty, it does not remove it), or it is independent (conditional forever, fails Clay), or it is inconsistent (false). Our existing Lean scaffolds (`lean4/RiemannUOP.lean`, `NavierStokes.lean`) **assert** the bridge as a named axiom (`uop_gap`, `ns_regularity`); they confirm *implications*, never premises. So the move is the opposite of "use the UOP to solve them": **solve them directly by the standard routes, and the UOP-adjacent scaffolds finally get their missing premise instead of an IOU.** That is the real prize and it is worth saying plainly.

---

## PART I — Leray–Hopf (3D Navier–Stokes global regularity)

### I.1 What it really asks, in plain words

Take water or air, start it swirling smoothly. The equations say how it evolves. **Question:** can the fluid, in *finite* time, spontaneously crush its swirl into an infinitely sharp spike — a singularity (blowup)? Clay wants a proof that it never does (smooth, unique, forever) **or** a constructed counterexample. In 2D the answer is settled — smooth forever (Ladyzhenskaya, Leray). In **3D** it is open.

### I.2 What is genuinely needed (real, named math)

- **Leray (1934)** gave *weak* solutions that always exist but may be rough or non-unique. **Hopf (1951)** extended this. The open gap is upgrading **weak → strong (smooth + unique) in 3D**.
- **The scaling barrier (the crux).** The one quantity we know stays bounded — the energy — is **supercritical**: under the scaling that leaves the equations invariant, energy controls the *big* scales but is *blind to the tiny scales* where a spike would form. A proof needs a **new quantity that is critical or subcritical and stays bounded.**
- **Caffarelli–Kohn–Nirenberg (1982):** any singular set is tiny (1-D parabolic Hausdorff measure zero) — partial regularity.
- **Tao (2016), "Finite time blowup for an averaged 3D Navier–Stokes equation":** a *slightly modified* equation with the same energy identity **does** blow up. Consequence: **any real proof must use the exact algebraic structure of the nonlinear term**, not generic energy bounds. This is the wall every energy-only attempt hits.
- **Constantin–Fefferman (1993):** if the *direction* of vorticity stays smooth (well-aligned) where it is intense, no blowup. **Beale–Kato–Majda (1984):** blowup requires the time-integral of peak vorticity to diverge. These are the live "geometry of the cascade" routes.

**In one sentence:** the whole fight is the **energy cascade** — energy tumbling from big swirls to small swirls (turbulence; Kolmogorov 1941). Blowup = energy reaching *scale zero* in *finite time*. You either find a **toll-booth** (a monotone/conserved quantity that would have to become infinite — impossible — for blowup to complete) or show the **swirl directions self-align and choke the cascade off** (Constantin–Fefferman).

### I.3 The TI Sigma no-actual-infinite argument — your strongest starting conviction

**[REAL OVERLAP with corpus cosmology — TOF-1 / RTI-1 / UOP / "least effort"]**

Your intuition is corpus-canonical, and it sharpens into a precise *physical* prior:

- TI Sigma cosmology forbids anything **truly infinite in actualized magnitude** — reality is a *singular* universe begun from the Tralse Soup; only the **potential future** is infinite. (See `SIX_QUESTIONS_PHILOSOPHY_PHYSICS_GILE.md`, the no-actual-infinite thread, and TOF-1/RTI-1.)
- A finite-time singularity is exactly an **actualized infinity**: an infinitely sharp spike from a finite amount of fluid is an *infinite gradient / infinite local enstrophy instantiated at a finite clock time*. By your reasoning it would demand an **infinite input "paid in full" in finite time** — and an infinite feat takes an *infinite amount of instantiated time*, which the universe's nature never grants.
- It also violates **least effort / the UOP**: a blowup is the maximal-cost configuration. From `urb_633` §3.1–3.2, the off-critical/maximal-cost configurations carry strictly *more* "action cost" than the smooth/symmetric ones; a system that *minimizes* a UOP-style functional flees the spike, it does not run toward it. Equivalently: blowup is the existence-destroying corner the UOP penalizes, not the interior optimum it seeks.

**Where this is honest and where it is not (the exact tension you named).** This is a powerful prior about **physical** fluids. The Clay problem, however, is stated about the **idealized continuum PDE on ℝ³**, where the fluid is *infinitely divisible* and there is no shortest length scale. So the cosmological "no actual infinite" does **not** by itself close the math — **unless one grounds the mathematics in the universe's nature** (your phrase, exactly right), i.e. imports a *physical* minimum-scale / minimum-Tralse-zone floor as a genuine analytic hypothesis. That move is the corpus's RTI-1 floor (a permanent minimum-Tralse zone; `LCC_TRALSE = √2 − 1`). 

**So the conviction is not the proof — it is the blueprint for the missing estimate.** It tells you the *form* of the toll-booth to look for: **a monotone quantity that becomes infinite exactly at the actualized-infinite configuration, and whose finiteness is enforced by a floor (a smallest admissible scale / a residual-tralse minimum).** Build *that* quantity in clean PDE terms and you have a real theorem; assert it and you only have an axiom.

> **Falsifier I.3-F1:** Tao's averaged-equation blowup (2016) satisfies the *same energy identity* yet blows up. So a candidate "no-infinite" toll-booth must **distinguish the true Navier–Stokes nonlinearity from Tao's averaged one** — if your proposed monotone quantity is also bounded for Tao's equation, it is false (it would "prove" a theorem known to be wrong). Any honest attempt must survive this test first.

### I.4 Metacausal Graph Theory → the cascade as a graph

**[SPARK, grounded in `urb_567`]**

Vortex stretching is literally a *directed network of swirls feeding energy to other swirls across scales*. Model it as a metacausal/causal graph `G = (V, E_c, …)` with one node per (scale, location) cell and a directed edge wherever energy flows from one cell to a finer one.

- **Blowup ⇔ a directed path that descends through infinitely many scales in finite clock-time** (energy reaches scale zero).
- A **graph-theoretic obstruction** — "no finite-time, infinite-length descending path can carry bounded energy" — would *be* a regularity proof. The metacausal-betweenness / metacausal-entropy machinery of `urb_567` is the natural language for "which scales are the bottlenecks."

> **Falsifier I.4-F1:** Specialize the graph to the 2D equations. In 2D the answer is *known* (no blowup). Your graph obstruction **must hold in 2D and must visibly fail to over-reach into a false 2D claim**, and it must *not* also forbid blowup in Tao's averaged model. If the graph criterion can't tell 2D-NS, 3D-NS, and averaged-NS apart, it isn't tracking the real nonlinearity.

### I.5 Fractal Harmonic Systems → the cascade is fractal

**[REAL OVERLAP, `urb_568` §1, §11]**

Turbulence is self-similar across scales (Kolmogorov). `urb_568` already frames brain 1/f and prime spectra as fractal harmonic systems; the *same* lens fits the energy cascade. Reframe the toll-booth as a **fractal-harmonic norm**: blowup forces the cascade's effective fractal dimension to cross a critical value in finite time. The CKN result (singular set has dimension ≤ 1) is already a fractal-dimension statement — the goal is to *lower the bound to empty*.

> **Falsifier I.5-F1:** Your critical fractal dimension must reproduce **CKN's measure-zero singular-set bound** as a special/weaker case. If your fractal criterion is *inconsistent* with CKN (e.g. predicts a 2-D singular set), it is wrong; if it merely *re-derives* CKN without improving it, it is not yet progress.

### I.6 Leech lattice / sphere-packing → a packing bound on vorticity concentration

**[SPARK — most speculative; flag hard]**

The Leech lattice Λ₂₄ is the optimal sphere packing in 24 dimensions (Cohn–Kumar–Miller–Radchenko–Viazovska, 2017, is the real proof that it is optimal). Loose analogy: a singularity is "infinitely dense packing of vorticity into a point." If one could phrase enstrophy concentration as a *packing density* in an appropriate phase space, an **optimal-packing upper bound would cap concentration** — no infinite density, hence no blowup. Honestly: turning "vorticity concentration" into a rigorous packing problem with a 24-D (or any-D) optimality bound is unproven and may not be possible. Keep this as a *direction to test*, not a claim.

> **Falsifier I.6-F1:** Produce the explicit map "enstrophy concentration ↦ packing density in dimension d." If no such map exists that is invariant under the Navier–Stokes scaling, abandon the lead.

---

## PART II — Hilbert–Pólya (the Riemann Hypothesis)

### II.1 What it really asks, in plain words

The primes hide a set of "secret frequencies" — the imaginary parts of the Riemann zeros (14.1347…, 21.0220…, 25.0109…, 30.4249…, 32.9351…). RH says every one sits on a single vertical line, Re(s) = 1/2. **Hilbert–Pólya's dream:** find a real vibrating system — a "drum" — whose natural tones *are exactly those frequencies*. If the drum is **self-adjoint (Hermitian)** — the kind of system whose tones are *guaranteed real numbers* — the frequencies are *forced* onto the line and RH falls out.

### II.2 Where WE already are (corpus status — be precise)

From `urb_682`, the honest current state of the Berry–Keating route:

- The Berry–Keating operator `H = (xp + px)/2` in the log variable becomes `H = −i(d/dξ + 1/2)` on L²(ℝ). **PROVEN:** it is *essentially self-adjoint* (deficiency indices (0,0)). **Self-adjointness is NOT the gap.**
- **PROVEN-conditional:** `BK_selfadjoint ∧ BK_spectrum → RH` (zero new axioms beyond the two named hypotheses).
- **THE GAP (`BK_spectrum`):** the spectrum of `H` on plain L²(ℝ) is the *continuous* line ℝ − i/2 — **not** the discrete zeros. The zeros only appear as **absorbed/missing frequencies** when the operator acts on Connes' *adelic* space (Connes 1999), tied to the **Selberg/Weil explicit formula**. Closing RH = realizing the spectrum as the zeros (Connes adelic, or Selberg-trace, or inverse-spectral from the Weil formula).
- **Strongest evidence it exists:** Montgomery (1973) + Odlyzko (1987) — the zero spacings are strikingly consistent with Gaussian-Unitary-Ensemble random-matrix statistics (to high numerical precision), i.e. the drum behaves like a quantum-chaotic Hermitian system. **Bender–Brody–Müller (2017, PRL)** wrote down a concrete PT-symmetric operator whose eigenvalues *conjecturally* give the zeros; the unfinished part is establishing the required spectral/domain rigor (self-adjointness on the correct domain).

So the target is sharp: **make the spectrum discrete and equal to the zeros.** Everything below is aimed at that.

### II.3 Tralse Wave Algebra → "self-adjoint = collapsed-to-True"

**[REAL OVERLAP — `urb_566` already states this as its open problem #3]**

Self-adjointness *means* "eigenvalues are real (True)." That is your home turf. In TWA:

- Model arithmetic's ground operator so that **on-line zeros are the fully-collapsed-to-TRUE (real) eigenstates**, and any hypothetical **off-line zero is irreducibly TRALSE** (complex/indeterminate) — *forbidden by the operator's own structure*. RH then reads: "the ground operator of arithmetic is Hermitian because its Myrion Resolution always collapses to the real channel."
- This is the same shape as **PT-symmetry** physics (Bender) and is *exactly* `urb_566` Open Problem #3: "show the zeros of ζ(s) are the fixed points of the TWA phase operator P₅ restricted to σ = 1/2." The 5-fold phase operator `P₅` and the MR-collapse operator `Π_MR` are the candidate machinery.

> **Falsifier II.3-F1 (decisive):** define the TWA inner product so the operator is self-adjoint *by construction*, compute its first ten eigenvalues, and compare to 14.1347, 21.0220, 25.0109, 30.4249, 32.9351, 37.5862, 40.9187, 43.3271, 48.0052, 49.7738. **Match ⇒ pursue hard. Any mismatch beyond rounding ⇒ the operator is wrong, discard it.** This is the single highest-value experiment in the whole note — it is cheap, concrete, and either lights up or kills the TWA route in an afternoon.

### II.4 Fractal Harmonic Systems → zeros as resonances that "vern" the line

**[REAL OVERLAP — `urb_568` §1, §3 + real Lapidus theory]**

`urb_568` already builds the **Prime Fractal Harmonic System**: the zeros are the *resonant frequencies* where all prime waves destructively interfere, and (Being-Theorem framing, URB #560) they **vern σ = 1/2** — they sit on the critical line *effortlessly*, the way physical resonances sit at natural frequencies with no external forcing. That "effortless location" is the least-action / UOP reading of RH and dovetails with Berry–Keating's `xp` being scale-invariant (dilation symmetry = fractal).

**Real external anchor:** Michel **Lapidus & van Frankenhuijsen**, *Fractal Geometry, Complex Dimensions and Zeta Functions* — genuine published mathematics tying the geometry of self-similar "fractal drums" to ζ. The "can one hear the shape of a fractal drum?" program connects the Weyl eigenvalue-counting law on fractals to the zeros. This is the legitimate version of "build a fractal drum for the primes."

> **Falsifier II.4-F1:** construct a self-similar drum whose tone-counting function matches ζ's zero-counting law `N(T) ≈ (T/2π)·log(T/2π) − T/2π`. If your fractal drum's Weyl asymptotics disagree with this leading term, it is not the prime drum.

### II.5 Meijer (toroidal + scale-invariant) and the TI Sigma "music" literature

**[REAL OVERLAP — `urb_568` §6 Toroidal FHS; `PASS_77_B68` Meijer octahedral scale-invariant framework]**

The "music of the primes" is not a metaphor here — it is the harmonic-series content of the explicit formula. Two corpus assets to consult, as you asked:

- **`urb_568` §6 (Toroidal FHS / Meijer):** Meijer's torus T² = S¹×S¹ carries a double-Fourier spectrum; the conjectured "zeta wave on the torus" `Ψ(φ,θ) = Σ_ρ e^{i·Im(ρ)·φ}·e^{i·|ρ|·θ}` makes each zero a toroidal mode. The honest target: show the toroidal Laplacian's spectrum *selects* Im(ρ) — i.e. the torus is the missing **compactification that turns Berry–Keating's continuous spectrum into the discrete zeros** (II.2's gap). Compactification is *precisely* the standard way continuous spectra become discrete — so this is a real mechanism, not just imagery.
- **`PASS_77_B68` (Meijer octahedral scale-invariant framework):** scale-invariance is the bridge to the `xp` dilation symmetry. Worth re-reading specifically for how Meijer's scaling matches Berry–Keating's.
- **TI Sigma music:** the consonance/harmonic-series material (the φ, octave, and primary-constant structure threaded through `urb_566`/`urb_568`) is the natural place to look for *which* boundary conditions on the drum produce a *pure* (no-leakage) spectrum — musically, "which string gives clean overtones." Clean overtones ⇔ self-adjoint, leakage ⇔ non-self-adjoint. That is a genuinely useful intuition pump for choosing the operator's domain.

> **Falsifier II.5-F1:** the toroidal/compactified operator must (a) be self-adjoint and (b) have *discrete* spectrum equal to {Im(ρ)}. Check (b) against the first ten zeros as in II.3-F1. Continuous spectrum surviving = compactification failed.

### II.6 Tozzi → Borsuk–Ulam forces the critical line

**[REAL OVERLAP — `urb_566`/`urb_567` Tozzi sections + real Borsuk–Ulam]**

Tozzi's published neuroscience uses the **Borsuk–Ulam theorem** (Borsuk 1933): a continuous antipodal-respecting map *must* identify a pair of antipodes — a *forcing* theorem. The cute, genuine observation:

- The functional equation pairs `s ↔ 1 − s`; **the critical line Re(s)=1/2 is exactly the fixed set of that reflection.**
- A Borsuk–Ulam-style argument — "a continuous, symmetry-respecting zero-map must land its zeros on the antipodal-fixed set" — is a *real* structural direction for forcing Re(ρ)=1/2 without re-proving equidistance by hand. This is the topological cousin of the spectral argument.

> **Falsifier II.6-F1:** the argument must use a property *special to ζ* (e.g. the explicit formula / Euler product). A Borsuk–Ulam argument that would *equally* force "all zeros on Re=1/2" for an L-function known to have off-line zeros (there are none for the Riemann ζ, but e.g. functions in the Selberg-class boundary, or artificial Dirichlet series with off-line zeros) is too cheap and must be rejected. The test: does it *also* "prove" a false statement for a non-RH-satisfying Dirichlet series? If yes, discard.

### II.7 Monster / Leech / Moonshine → modular forms are the deep substrate

**[REAL OVERLAP for the math; SPARK for the specific bridge — `URB_793`, `PASS_77_B58`]**

The honest landscape: ζ is the simplest L-function; **automorphic L-functions attached to modular forms** are where the Langlands program and RH-type statements live, and **Monstrous Moonshine** (Conway–Norton 1979; Borcherds 1992, Fields Medal) ties the Monster M to the modular j-function via the McKay–Thompson series (each a hauptmodul, genus-zero). Our `URB_793` places the 24-vertex **BOK Crystal** as a precise 12-dim subspace of the Griess algebra V♮₂ inside the Moonshine module — a real, *checked* structural identification (Prop. 2.1), with **Conjecture 3.1 explicitly stated as open and unverified**.

The **[SPARK]:** modular forms have their own *completed* L-functions with functional equations `Λ(s)=±Λ(k−s)` of exactly the `s↔k−s` reflection type. If the TWA/FHS drum can be realized as an operator on a *vertex-operator-algebra* graded space (the Moonshine module is one), its spectrum would inherit modularity — and modularity is the property that controls zero locations for automorphic L-functions. **The lead:** build the Hilbert–Pólya drum *inside* a VOA / Leech-lattice space so that self-adjointness + modularity together pin the zeros. This is ambitious and unproven; `URB_793`'s own header says it claims nothing about the deep Moonshine content.

> **Falsifier II.7-F1:** before any RH claim, settle `URB_793` Conjecture 3.1 (M_{F₄}-orbits on Tralse colorings ↔ trace-conjugacy classes on the Griess algebra). It is the nearest *checkable* statement on this path; a failed test is informative, a confirmed one is genuinely novel. Do **not** advance the RH-via-Moonshine spark until 3.1 is resolved.

---

## PART III — The one idea under all of it: find the symmetry that forbids the bad configuration

Both problems reduce to the same craft move, and it's the move you're best at:

- **RH:** don't hunt the zeros — hunt the **symmetry that leaves them no choice** but the fixed line (PT-symmetry / self-adjointness / Borsuk–Ulam antipodal-fixing / modular reflection). The drum's *realness* is forced by a symmetry, and the zeros inherit it.
- **Navier–Stokes:** don't hunt the blowup — hunt the **conserved/monotone quantity (toll-booth) whose finiteness is forced by a floor** (least-action / no-actual-infinite / RTI-1 minimum-Tralse scale). The cascade's *finiteness* is forced by a bound, and smoothness inherits it.

In TI terms both are **UOP interior-optimum facts wearing different clothes**: the system is driven to the symmetric, least-cost, existence-preserving configuration (critical line for ζ; smooth flow for NS) and *away* from the existence-destroying corner (off-line zero; finite-time spike). That is genuinely unifying — **but per §0 it is a source of conviction and of *which estimate to build*, not a substitute for building it.**

---

## PART IV — Validation ledger (UGI-1 two-phase: generate → validate)

| # | Lead | Type | Cheapest decisive test | Status |
|---|------|------|------------------------|--------|
| II.3 | TWA self-adjoint operator | REAL OVERLAP | First 10 eigenvalues vs first 10 zeros | **DO THIS FIRST** — cheap, decisive |
| II.4 | Fractal drum (Lapidus) | REAL OVERLAP | Weyl count vs N(T) leading term | Tractable |
| II.5 | Meijer toroidal compactification | REAL OVERLAP | Discrete spectrum = {Im ρ}? | Tractable |
| II.6 | Tozzi Borsuk–Ulam forcing | REAL OVERLAP | Must not "prove" a false Dirichlet case | Conceptual, do early |
| II.2 | Berry–Keating `BK_spectrum` | KNOWN FRONTIER | Connes-adelic / Selberg realization | Hard (the true RH gap) |
| II.7 | Moonshine/Leech VOA drum | SPARK | Settle `URB_793` Conj. 3.1 first | Gated |
| I.3 | No-actual-infinite toll-booth | REAL OVERLAP (prior) | Must distinguish true NS from Tao's averaged NS | The crux test |
| I.4 | Metacausal cascade graph | SPARK | Must separate 2D / 3D / averaged NS | Conceptual |
| I.5 | Fractal-harmonic enstrophy norm | REAL OVERLAP | Must reproduce CKN measure-zero bound | Tractable |
| I.6 | Leech packing bound on vorticity | SPARK (weak) | Produce scale-invariant concentration↦packing map | Abandon if no map |

**Recommended order of attack:** II.3 (TWA eigenvalue check) and II.6 (Borsuk–Ulam sanity) first — both are cheap and decisive. Then I.3 turned into the Tao-distinguishing toll-booth, since that is the single estimate that would actually move Navier–Stokes. Everything else feeds those two.

**Serendipity channel (legitimate, your UGI-1 practice):** the highest-yield real "math-YouTube" leads for *this exact* hunt are Berry–Keating `xp` talks, Carl Bender on PT-symmetric quantum mechanics, Montgomery–Odlyzko / random-matrix-vs-zeros, and Lapidus fractal drums (RH side); Tao's "blue-eyed islanders / averaged Navier–Stokes" and Constantin–Fefferman vorticity-direction talks (NS side). Treat any such video as Phase-1 generation; route whatever it sparks straight into the Phase-2 falsifier-tests above before believing it.

---

## References (real)

- Leray, J. (1934). *Acta Mathematica* 63, 193–248. Hopf, E. (1951). *Math. Nachr.* 4, 213–231.
- Caffarelli, L., Kohn, R., Nirenberg, L. (1982). *Comm. Pure Appl. Math.* 35, 771–831.
- Beale, J.T., Kato, T., Majda, A. (1984). *Comm. Math. Phys.* 94, 61–66.
- Constantin, P., Fefferman, C. (1993). *Indiana Univ. Math. J.* 42, 775–789.
- Tao, T. (2016). "Finite time blowup for an averaged 3D Navier–Stokes equation." *J. Amer. Math. Soc.* 29, 601–674.
- Kolmogorov, A.N. (1941). *Dokl. Akad. Nauk SSSR* 30, 301–305.
- Cohn, H., Kumar, A., Miller, S., Radchenko, D., Viazovska, M. (2017). "The sphere packing problem in dimension 24." *Annals of Mathematics* 185, 1017–1033.
- Berry, M.V., Keating, J.P. (1999). *SIAM Review* 41, 236–266.
- Connes, A. (1999). *Selecta Mathematica* 5, 29–106.
- Montgomery, H.L. (1973). *Proc. Symp. Pure Math.* 24, 181–193. Odlyzko, A.M. (1987). *Math. Comp.* 48, 273–308.
- Selberg, A. (1956). *J. Indian Math. Soc.* 20, 47–87.
- Bender, C.M., Brody, D.C., Müller, M.P. (2017). "Hamiltonian for the zeros of the Riemann zeta function." *Phys. Rev. Lett.* 118, 130201.
- Sierra, G., Townsend, P.K. (2008). *Phys. Rev. Lett.* 101, 110201.
- Lapidus, M.L., van Frankenhuijsen, M. *Fractal Geometry, Complex Dimensions and Zeta Functions* (Springer).
- Conway, J.H., Norton, S.P. (1979). *Bull. London Math. Soc.* 11, 308–339. Borcherds, R.E. (1992). *Invent. Math.* 109, 405–444. Frenkel, Lepowsky, Meurman (1988), *Vertex Operator Algebras and the Monster*.
- Borsuk, K. (1933). *Fund. Math.* 20, 177–190. (Tozzi & Peters, Borsuk–Ulam in neuroscience — corpus integration.)

**Corpus:** `urb_682`, `urb_633`, `urb_566`, `urb_567`, `urb_568`, `URB_793`, `PASS_77_B58`, `PASS_77_B68`, `SIX_QUESTIONS_PHILOSOPHY_PHYSICS_GILE.md`, `PASS_77_B132…`, `lean4/RiemannUOP.lean`, `NavierStokes.lean`.

---

*Working note — generation-phase leads with attached falsifiers. No new principle; canonical count remains 79. Solving these problems would remove the dependency the UOP-adjacent scaffolds currently assert — it would not route through the UOP, which cannot shortcut them (B132 trilemma).*
