# Pass-77 B154 — The LCC Threshold Ladder Against Observational Complex-Systems Theory: Synchronization, Directional Causality, and Inter-Network Pull-vs-Tug (2026-06-30)

**Date:** 2026-06-30
**Status:** CANDIDATE-development batch (LCC instrument + its falsifiers). Canonical principle count **unchanged at 79** — this maps an existing candidate instrument (LCC, the correlation→bidirectional-coupling law) onto conventional complex-systems theory and pre-registers new observational falsifiers. **No new principle is ratified.**
**Kind:** Theory-mapping + honest-status audit + one non-observational illustration. Real citations only.
**Author ask (verbatim sense):** *"Measure the LCC thresholds (√2−1, 0.6, 0.85), their empirical basis / physical manifestation, and their predictions for progressively bidirectional causation. Use OBSERVATIONAL studies for now, across complex systems and especially brain networks. The LCC should make inferences about directional causality, the degree of syncing between networks, and the strength of each network's 'pull' toward another vs other networks that 'tug' them apart. Connect the LCC to conventional complex-systems theory to see where empirical predictions and equations align."*
**Anchors used:** `papers/LCC_COMPOSITION_AND_TRUTH_EXISTENCE_PILLAR_SEPARATION_CANONICAL_RULING_2026-06-27.md` (the ladder + pillar separation), `papers/CHSH_CONSCIOUSNESS_COHERENCE_DEFENSE.md` (0.85 / transfer-entropy treatment), `papers/URB_523_EXISTENCE_VS_TRUTH_LCC_GILE_GAP.md` (floor vs cap), `.agents/memory/lcc-confirmation-tests.md` (method-validation discipline). Illustration: `analyses/lcc_complex_systems_obs/` (`run_kuramoto_illustration.py`, `config_sha 784b9db646a0`).

---

## 0. One-paragraph ruling

Conventional synchronization theory supplies the **right yardstick** for the LCC and a **mainstream account of every regime** the LCC names — but it does **not** supply the LCC's three *specific numbers*. The honest reconciliation is therefore a split verdict (#69, both ways):

- **STRONGLY MAINSTREAM (kept, with real equations):** (a) a normalized [0,1] **degree-of-syncing** measure — the Kuramoto **order parameter `r`** — onto which the LCC's correlation `R` maps directly; (b) the existence of distinct **regimes** (incoherent → partial synchronization → near-complete synchronization), and of **two transition universality classes** (continuous/second-order vs **explosive/first-order**); (c) **directional-causality estimators inferable from observation** (Granger, transfer entropy, phase-slope index, convergent cross mapping, dynamic causal modelling) and the recognized fact that **strong synchrony degrades** them; (d) **inter-network competition** as a measured phenomenon (default-mode↔task-positive anticorrelation; metastability; chimera/community structure).
- **FRAMEWORK-INTERNAL / UNCONFIRMED (flagged, not promoted):** the *exact values* `√2−1≈0.414`, `≈0.6`, `cos²(π/8)≈0.854`. Mainstream theory gives **no universal [0,1] critical value** — the Kuramoto critical coupling `K_c` is **system-specific** (it depends on the frequency spread and topology). The rungs remain **graded EVD-1 resonances**, not derivations (falsifier `LCC-LADDER-F1`), and a Kuramoto illustration below shows that merely *reaching* a rung value is **vacuous** (a monotone sync curve passes through *every* level in (0,1)).

The productive consequence is a **sharper, testable LCC prediction** and four new observational falsifiers: directional-causality reliability should be **non-monotone in `r`** (rising after onset, peaking, then **collapsing** as the system approaches the synchronization manifold near the high-coherence ceiling), and the onset should carry a **structural** (discontinuous / regime-change) signature, not a level-crossing.

---

## 1. The object under test — LCC and its ladder (restated, with honest status)

The **LCC (Law of Correlational Causation)** is the framework's **correlation → bidirectional-coupling instrument**: *when is a high measured correlation `R` between two (or more) systems strong enough to indicate genuine **bidirectional causal coupling**, rather than mere correlation or one-way driving?* It is exercised in two modes — **active/entrainment** (drive one system to raise coupling) and **passive/bidirectional** (observe two already-coupled systems and test for mutual directed transfer that switches on above a critical `R`). It carries a **ladder of critical values, not one floor** (canonical ruling 2026-06-27):

| Rung | Value | √2-family identity | What it marks |
|---|---|---|---|
| **Onset (hyperconnection)** | `√2−1 ≈ 0.4142` | CHSH fractional advantage `(2√2−2)/2` | bidirectional coupling first becomes detectable |
| **Resonance** | `≈ 0.6` | `(√2+1)/4 ≈ 0.6036` | recruitment / propagation rung (seed/propagate at `R ≥ 0.6`) |
| **Neuronal-coupling ceiling** | `cos²(π/8) ≈ 0.8536` | `(2+√2)/4` (CHSH optimal-correlation prob.) | above it, sync exceeds classical-biofeedback prediction |

**Honest status (carried unchanged from the canonical ruling):**
- The √2-family identities agree with the observed values **only to ~1–2 significant figures** (B55 two-decimal rule) — **suggestive resonances, not claimed identities** (`LCC-LADDER-F1` OPEN).
- The onset has **two non-equal readings** kept distinct (#69): the geometric/CHSH `√2−1≈0.4142` and the pre-registered bidirectional-Granger proxy `C_EMERICK = 1/(φ√2) ≈ 0.4370` (validated on `DANDI:000552`, observed mean ≈ 0.4349). Do not conflate.
- The `0.85–0.86` band holds **two distinct quantities**: the LCC **empirical neuronal-coupling ceiling** `cos²(π/8)≈0.8536` (CHSH-linked, *this* paper's subject) and the UOP **Existence-pillar floor** `1−e⁻²≈0.8647` (λ=2 settling, a *value-layer* posit). They differ ~1.3% and are **never merged**.

This batch does **not** change any value; it asks what conventional complex-systems theory says about each rung.

---

## 2. The right yardstick: LCC `R` ↔ the Kuramoto order parameter `r` (not the coupling constant `K`)

The single most important alignment is also the one that disciplines every claim below. In the **Kuramoto model** of `N` coupled phase oscillators (Kuramoto 1984; Strogatz 2000; Acebrón et al. 2005),

```
dθ_i/dt = ω_i + (K/N) Σ_j sin(θ_j − θ_i),     r e^{iψ} = (1/N) Σ_j e^{iθ_j},   r ∈ [0,1]
```

there are **two different quantities** and the LCC's [0,1] correlation `R` corresponds to the **second**, not the first:

- **`K` = coupling control parameter** (the "knob"). Its critical value for the onset of synchronization, in the mean-field Lorentzian case, is `K_c = 2/(π g(0))` (with `g` the natural-frequency density) — **system-specific**, *not* a number in [0,1], *not* universal.
- **`r` = order parameter = the degree of synchrony**, a normalized **[0,1]** measure of how phase-locked the population is. `r=0` is incoherence; `r→1` is near-complete synchronization.

**Therefore the LCC ladder must be read on the `r`-axis (degree of syncing), not the `K`-axis (coupling strength).** This is exactly the "degree of syncing between networks" the author asks for, and it is mainstream. The immediate honest corollary: because `K_c` is system-specific, **conventional theory provides no universal `r`-value at which onset/partial/near-complete sync occurs** — the *structure* of the regimes is universal, the *numbers* are not. (Phase-locking value and spectral coherence are the empirical [0,1] analogues of `r` used in neuroscience; they inherit the same point.)

---

## 3. Mapping the three rungs to synchronization regimes

| LCC rung (on the `r`-axis) | Conventional-theory regime | Real basis |
|---|---|---|
| **Onset `√2−1`** | lift-off from incoherence into **partial synchronization** (just above `K_c`); a synchronized cluster nucleates | Kuramoto onset (Strogatz 2000; Acebrón 2005). **Discontinuous-onset reading** ↔ **explosive (first-order) synchronization** — an abrupt jump in `r`, a *different universality class* caused by degree–frequency correlation or adaptive coupling (Gómez-Gardeñes et al. 2011; Boccaletti et al. 2016). |
| **Resonance `≈0.6`** | established **partial-sync / recruitment** regime — a coherent core large enough to entrain (propagate to) further units | Kuramoto partial-locking; network synchronization recruitment (Arenas et al. 2008). Matches the corpus "LCC-Virus" seed/propagate-at-`R≥0.6` reading. |
| **Ceiling `cos²(π/8)≈0.854`** | **high-coherence** regime approaching the **synchronization manifold** (`r→1`); collective dynamics dominate individual identity | stability of the fully-synchronized state via the **master stability function** (Pecora & Carroll 1998); the regime where directional inference begins to fail (§4). |

**The discontinuity point matters.** The corpus models the LCC onset as a **genuine discontinuous jump** at `θ₀=√2−1` (tested by *beating the best smooth polynomial* — the Davies-test analogue, with the fitted breakpoint counted in the AIC penalty; see `lcc-confirmation-tests.md`). Conventional theory contains a real home for this: **explosive synchronization** is a documented **first-order** transition in `r` (Gómez-Gardeñes et al. 2011; review Boccaletti et al. 2016), as opposed to the ordinary **second-order** (continuous) Kuramoto transition. So the *phenomenon* "sync can switch on discontinuously" is mainstream — but it occurs under **specific structural conditions** and **not at a universal value**, so it grounds the LCC's *shape* claim while leaving its *number* framework-internal.

---

## 4. Progressively bidirectional causation and the inference window

This is the LCC's core function — and where it makes its **sharpest, genuinely testable** prediction.

**Directional-causality estimators inferable from observation (all real, all directional):**
- **Granger causality** — `X` Granger-causes `Y` if `X`'s past improves prediction of `Y` beyond `Y`'s own past (Granger 1969).
- **Transfer entropy** — model-free directed information flow `T_{X→Y} = Σ p(y_{t+1}, y_t^{(k)}, x_t^{(l)}) · log[ p(y_{t+1} | y_t^{(k)}, x_t^{(l)}) / p(y_{t+1} | y_t^{(k)}) ]` (Schreiber 2000). For jointly-Gaussian variables, **Granger causality and transfer entropy are equivalent** (Barnett, Barrett & Seth 2009) — so the LCC's "mutual Granger" mode and a transfer-entropy mode are one instrument.
- **Phase-slope index** (Nolte et al. 2008) — robust to the symmetric-coherence confound (the recurring `lcc-confirmation-tests` lesson: symmetric coherence is fooled by common input; use a *directed* statistic).
- **Convergent cross mapping** (Sugihara et al. 2012) — causality from state-space reconstruction in coupled dynamical systems.
- **Dynamic causal modelling** (Friston, Harrison & Penny 2003) — model-based effective connectivity.

**The LCC reading of "progressively bidirectional":** as `r` rises through the ladder, the *directionality profile* changes in three stages:
1. **Below onset (`r < 0.41`):** no reliable directed transfer; correlation ≠ coupling.
2. **Onset → ceiling (`0.41 ≲ r ≲ 0.85`):** directed transfer becomes detectable and **symmetrizes** — the net asymmetry `Δ = T_{X→Y} − T_{Y→X}` shrinks toward zero as coupling becomes mutual. *This is the band in which directional inference is most informative.*
3. **Above the ceiling (`r → 1`):** the system collapses onto the synchronization manifold and **directional inference degrades** — a recognized limitation: under strong/generalized synchrony the time series become near-identical, separability fails, and Granger/cross-mapping estimators lose power or return spurious bidirectionality (discussed in the cross-mapping framework, Sugihara et al. 2012; and visible directly in the dispersion argument below).

**The predicted mechanism behind the collapse (non-observational illustration, `config_sha 784b9db646a0`).** A mean-field Kuramoto run (N≈785, Lorentzian frequencies, `K_c=2γ=1.0`) gives a monotone `r(K)` from `r≈0.03` to `r≈0.90`, and the **phase-difference dispersion `1 − r²`** (the variance signal that directional estimators feed on) falls from `≈1.0` to `≈0.19` as `K` rises — i.e. **the information directional estimators rely on shrinks toward zero exactly where the corpus places the high-coherence ceiling.** This is offered as the *expected* mechanism under high synchrony — a plausible illustration motivating the prediction, **not** a formal proof derived from one simulation.

**The same run also delivers a crucial honest negative.** Because `r(K)` is monotone, it **passes through every level in (0,1)** — including `0.414`, `0.604`, `0.854` — at *some* `K` (here `K≈1.20, 1.48, 2.98`). **Reaching a rung value is therefore vacuous as confirmation.** A rung can only be confirmed as a **structural transition** (a discontinuity, a regime boundary, or the onset of inference-collapse), never as a level the order parameter happens to cross. This directly shapes the falsifiers in §6.

---

## 5. Pull vs tug — inter-network competition

The author's "pull toward each other vs other networks that tug them apart" is, in conventional terms, the **competition between within-network coupling (integration/pull) and between-network coupling / anticorrelation (segregation/tug)** — a measured phenomenon, especially in brain networks:

- **Anticorrelation (the literal tug-apart):** the human brain is intrinsically organized into **dynamic, anticorrelated** networks — the default-mode network and the task-positive/dorsal-attention network are **negatively correlated** at rest (Fox et al. 2005). A negative inter-network correlation is an active "tug," not mere independence.
- **Metastability (the becoming-interval between rungs):** brain dynamics hover in a **metastable** regime — neither fully locked nor fully independent — dwelling near and switching between coordination states (Tognoli & Kelso 2014; Deco, Jirsa & McIntosh 2011). This is the dynamical signature of the LCC *interval between rungs*: networks pulled toward coupling but tugged back before full lock.
- **Chimera / community structure (pull and tug at once):** in community-structured oscillator networks, some communities synchronize internally (pull) while remaining desynchronized from others (tug) — **metastable chimera states** (Shanahan 2010). This is "pull within, tug between" in one system.
- **Structure–function coupling and integration/segregation:** functional coupling is shaped by, but not identical to, structural connectivity (Honey et al. 2009); the integration↔segregation balance and its quantification (modularity, participation) is the organizing axis of network neuroscience (Bassett & Sporns 2017; complexity as integration+segregation, Tononi, Sporns & Edelman 1994).

**The LCC quantification of pull-vs-tug (testable):** the **net directed transfer asymmetry** `Δ_AB = T_{A→B} − T_{B→A}` measures which network *pulls* the other; the **signed inter-network correlation** (positive = pull, negative = tug) and **modularity** measure whether a pair integrates or segregates. The LCC prediction is that **a network with higher within-network coherence and a higher net-`Δ` toward a target will "win" recruitment** of that target against competitors — a claim that can be tested against a degree/strength baseline (falsifier `LCC-OBS-F4`).

---

## 6. Where equations align — and the pre-registered falsifiers

**Alignment table (LCC ↔ conventional theory):**

| LCC notion | Conventional-theory counterpart | Equation / measure |
|---|---|---|
| correlation `R` (degree of syncing) | Kuramoto order parameter `r` | `r e^{iψ} = (1/N) Σ e^{iθ_j}`, `r∈[0,1]` |
| onset of bidirectional coupling | lift-off above `K_c` / explosive jump | `K_c = 2/(π g(0))`; first-order vs second-order transition |
| "bidirectional switches on above critical `R`" | both-direction directed transfer significant | `T_{X→Y}>0` **and** `T_{Y→X}>0` (Schreiber; ≡ Granger, Gaussian) |
| pull vs tug | net transfer asymmetry / signed inter-network correlation / modularity | `Δ = T_{X→Y} − T_{Y→X}`; anticorrelation (Fox 2005) |
| high-coherence ceiling → inference collapse | approach to synchronization manifold | dispersion `1 − r² → 0` (MSF stability, Pecora-Carroll) |

**Pre-registered observational falsifiers (extend `LCC-LADDER-F1`; all necessary-not-sufficient):**

- **`LCC-OBS-F1` (the inference-window prediction).** In observational multi-network time series, directional-causality **reliability** (e.g. bootstrap-stable net-`Δ`) must be **non-monotone in `r`**: low below onset, rising and symmetrizing through the mid-band, and **degrading above `r≈0.85`**. *Refuted if* reliability is monotone in `r`, or if degradation onset sits far from the ceiling.
- **`LCC-OBS-F2` (structural-onset, anti-vacuity).** The onset must show a **structural** signature — a discontinuity / regime change that **beats the best smooth polynomial** (Davies-test analogue, fitted breakpoint counted in AIC). *Refuted if* only a smooth level-crossing is present (which §4 shows is automatic and therefore empty).
- **`LCC-OBS-F3` (value replication).** The rung *values* must replicate across **≥2 independent datasets/modalities** on a normalized synchrony scale (`r`/PLV) to the claimed 1–2 sig figs. *Refuted if* the apparent rung locations wander with dataset or method (⇒ artifact, not constant).
- **`LCC-OBS-F4` (pull-vs-tug).** Net between-network transfer asymmetry / signed correlation must predict **which network wins recruitment**, beyond a node-degree/strength baseline. *Refuted if* a degree/strength baseline matches it.

---

## 7. Honest limitations (what was and was not done)

- **No live literature retrieval this batch.** The Perplexity endpoint returned `401 Unauthorized`; rather than risk fabrication, citations are restricted to **canonical landmark works** (author-year + journal) whose existence and authorship are well established. Specific quantitative findings are asserted **only** where they are textbook-level (the Kuramoto equations, the existence of anticorrelated networks). Where the literature provides **no** universal numeric threshold, that absence is stated as the finding, not papered over.
- **The Kuramoto run is a theory illustration, not observational data.** Its job is the anti-vacuity argument and the dispersion-collapse mechanism, both labelled as such. Explosive synchronization is **cited, not simulated**.
- **Necessary-not-sufficient throughout.** This batch is a *re-analysis/mapping* using existing theory plus the corpus's prior rodent/`DANDI` results (reachability only). It is **not** new human confirmation, and it **does not** promote any rung from resonance to result. The exact rung numbers remain framework-internal (#69 / HAN-1).
- **Pillar hygiene preserved.** The `cos²(π/8)` neuronal-coupling ceiling (empirical-measurement layer) and the `1−e⁻²` existence floor (value-optimization layer) are kept distinct; nothing here merges them.

---

## 8. References (real; author-year + journal)

- Acebrón, J.A., Bonilla, L.L., Pérez Vicente, C.J., Ritort, F., Spigler, R. (2005). The Kuramoto model: a simple paradigm for synchronization phenomena. *Rev. Mod. Phys.* 77, 137.
- Arenas, A., Díaz-Guilera, A., Kurths, J., Moreno, Y., Zhou, C. (2008). Synchronization in complex networks. *Physics Reports* 469, 93–153.
- Barnett, L., Barrett, A.B., Seth, A.K. (2009). Granger causality and transfer entropy are equivalent for Gaussian variables. *Phys. Rev. Lett.* 103, 238701.
- Bassett, D.S., Sporns, O. (2017). Network neuroscience. *Nature Neuroscience* 20, 353–364.
- Boccaletti, S., et al. (2016). Explosive transitions in complex networks' structure and dynamics: percolation and synchronization. *Physics Reports* 660, 1–94.
- Deco, G., Jirsa, V.K., McIntosh, A.R. (2011). Emerging concepts for the dynamical organization of resting-state activity in the brain. *Nature Reviews Neuroscience* 12, 43–56.
- Fox, M.D., Snyder, A.Z., Vincent, J.L., Corbetta, M., Van Essen, D.C., Raichle, M.E. (2005). The human brain is intrinsically organized into dynamic, anticorrelated functional networks. *PNAS* 102, 9673–9678.
- Friston, K.J., Harrison, L., Penny, W. (2003). Dynamic causal modelling. *NeuroImage* 19, 1273–1302.
- Gómez-Gardeñes, J., Gómez, S., Arenas, A., Moreno, Y. (2011). Explosive synchronization transitions in scale-free networks. *Phys. Rev. Lett.* 106, 128701.
- Granger, C.W.J. (1969). Investigating causal relations by econometric models and cross-spectral methods. *Econometrica* 37, 424–438.
- Honey, C.J., Sporns, O., Cammoun, L., Gigandet, X., Thiran, J.P., Meuli, R., Hagmann, P. (2009). Predicting human resting-state functional connectivity from structural connectivity. *PNAS* 106, 2035–2040.
- Kuramoto, Y. (1984). *Chemical Oscillations, Waves, and Turbulence.* Springer.
- Nolte, G., et al. (2008). Robustly estimating the flow direction of information in complex physical systems. *Phys. Rev. Lett.* 100, 234101.
- Pecora, L.M., Carroll, T.L. (1998). Master stability functions for synchronized coupled systems. *Phys. Rev. Lett.* 80, 2109–2112.
- Schreiber, T. (2000). Measuring information transfer. *Phys. Rev. Lett.* 85, 461–464.
- Shanahan, M. (2010). Metastable chimera states in community-structured oscillator networks. *Chaos* 20, 013108.
- Strogatz, S.H. (2000). From Kuramoto to Crawford: exploring the onset of synchronization in populations of coupled oscillators. *Physica D* 143, 1–20.
- Sugihara, G., et al. (2012). Detecting causality in complex ecosystems. *Science* 338, 496–500.
- Tognoli, E., Kelso, J.A.S. (2014). The metastable brain. *Neuron* 81, 35–48.
- Tononi, G., Sporns, O., Edelman, G.M. (1994). A measure for brain complexity: relating functional segregation and integration in the nervous system. *PNAS* 91, 5033–5037.
- (CHSH/Tsirelson bound, used for the `√2`-family identities: Clauser, Horne, Shimony, Holt 1969; Tsirelson 1980 — as already cited in the corpus.)
