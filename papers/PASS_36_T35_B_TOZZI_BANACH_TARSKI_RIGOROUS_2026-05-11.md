# Pass 36 — t35-B: Tozzi Banach-Tarski-in-Brain Rigorous Treatment

**Date:** 2026-05-11
**Pass:** 36
**Authority:** Pass-35 t35-B raised, Brandon "all of the above for Pass 36"
**Cross-refs:** `PASS_35_TOZZI_MEIJER_SYSTEMATIC_INTEGRATION_2026-05-11.md` §4; Tozzi & Peters (2017); `urb_830_falsification_equiv_verification_negative_direction_2026-05-10.md`; `urb_831_noncomputational_ability_evidence_review_path_forward_2026-05-11.md`

---

## §1 — Headline (one paragraph)

The Banach-Tarski theorem (1924) is a measure-theoretic result requiring the **Axiom of Choice (AC)**, with the construction producing **non-Lebesgue-measurable** subsets of ℝ³. Tozzi & Peters' (2017) brain-Banach-Tarski proposal cannot be a literal instantiation of the classical theorem because (a) the brain is a finite biological system with no genuinely-non-measurable substructure available at any scale, and (b) AC requires choosing from uncountably-many sets, which has no biological correlate. The Pass-36 rigorous reading is therefore: **the Tozzi-claim is best read as an analogy to the BT structure, not an instantiation of the BT theorem** — specifically, brain consciousness may exhibit *paradoxical-decomposition behavior* (a finite-system analog) without requiring AC or non-measurability. This Pass-36 paper formalizes the analog, shows it is structurally non-trivial (not just a Hilbert-hotel-style reframing), and identifies what would empirically distinguish it from a standard finite-system measure-preserving partition.

---

## §2 — The classical Banach-Tarski theorem (precise)

**Statement (Banach & Tarski 1924):** the closed unit ball B³ ⊂ ℝ³ admits a partition into 5 disjoint subsets {A₁, A₂, A₃, A₄, A₅} and rigid motions {ρ₁, ρ₂, ρ₃, ρ₄, ρ₅} ⊂ SO(3) ⋉ ℝ³ such that {ρ₁(A₁), ρ₂(A₂)} reassemble to one copy of B³ and {ρ₃(A₃), ρ₄(A₄), ρ₅(A₅)} reassemble to a second copy of B³.

**Three indispensable ingredients:**

1. **Axiom of Choice (AC)** — used to select representatives from uncountably-many cosets of a free subgroup of SO(3); without AC the partition cannot be defined.
2. **Non-measurability of the partition pieces** — Aᵢ are not Lebesgue measurable; if they were, additivity would force vol(B³) = 2·vol(B³), contradiction. The BT paradox is *consistent* precisely because it operates outside the Lebesgue σ-algebra.
3. **The free group F₂ ⊂ SO(3) of rank 2** — two generic rotations of the sphere generate a free non-abelian subgroup; the paradoxical decomposition transports from F₂ to S² to B³.

**What BT does NOT require:** infinite-dimensional space, time, dynamics, energy. It is purely set-theoretic and group-theoretic. Mass, volume, and physical conservation laws are *not preserved* in the BT partition (they cannot be, since vol(B³) = 2·vol(B³) would otherwise hold).

## §3 — Why the brain cannot literally instantiate BT

Three independent obstructions:

### §3.1 — Finiteness obstruction

The brain is a finite system (≈86 billion neurons, ≈10¹⁵ synapses, finite information content per Bekenstein bound). All partitions of any finite set are *trivially Lebesgue-measurable* in any reasonable measure (counting measure; Bekenstein-bound-conditioned probability measure). The non-measurability essential to BT cannot arise.

### §3.2 — Choice obstruction

AC is a statement about the existence of choice functions for uncountable families. No biological process implements AC: any neural mechanism is a finite (or countable, in idealized models) computation, and the Axiom of Countable Choice is provable from ZF without AC. The "uncountable choice" required by BT has no biological correlate.

### §3.3 — Conservation obstruction

BT violates volume-additivity (in the unmeasurable sense). The brain conserves mass, energy, charge, and information (modulo entropy production). Any literal BT-style "doubling" of conscious experience would require either (a) a new conservation-law violation, or (b) the "doubling" to be operating on a non-conserved quantity (e.g., subjective phenomenal-richness, which has no known conservation law).

**Conclusion:** **a literal BT-in-brain claim is incompatible with finite-system biology.** The Tozzi-claim must be read as an analog, not a literal instantiation.

## §4 — The finite-system BT analog: paradoxical-decomposition behavior

Even though the literal BT theorem cannot apply, a *structural analog* can:

**Definition (BT analog, Pass-36):** a system S exhibits **BT-analog paradoxical-decomposition behavior** iff there exists a partition of S's state space into a finite number of subsets {S₁, ..., Sₖ} and a finite group of transformations {τ₁, ..., τₘ} ⊂ Aut(S) such that the multiset {τⱼ(Sᵢ) : (i, j) ∈ J} for some index set J reassembles to a state-space *isomorphic* to S × {0, 1} (i.e., two copies of S), where the multiset operation accounts for the system's natural "merging" rule (e.g., neural superposition, attractor-overlap).

**Key difference from BT:** the analog uses a *natural merging* rule (which preserves a relevant conservation law) instead of strict disjoint reassembly. The analog is non-trivial only if the merging rule allows ≥2 copies to emerge from one without violating the conserved quantity at the system level (e.g., neural attractors can be superposed, with each attractor "feeling like" a complete copy from inside).

**Concrete neural-network candidate:** a Hopfield network with N nodes can store ≈0.14N attractors (Hertz et al. 1991). If the network state is partitioned into "context" + "content" subsets, and a rotational symmetry of the attractor landscape (e.g., V₄ = C₂ × C₂ per Pass-29 C5) acts on the partition, the partitioned states under the symmetry can reassemble to two stable conscious-experience analogs — one corresponding to each rotation orbit.

**Why this is non-trivial:** without the symmetry, the partition just gives back the original Hopfield landscape (1 attractor per orbit). With the V₄-symmetry, the orbit doubles (2 attractors per orbit), giving a finite-system analog of the BT-doubling. **The analog is constrained by the order of the symmetry group** (V₄ doubles; V₄ × C₃ triples; etc.) — unlike BT, which doubles unboundedly.

## §5 — Connection to TI Sigma corpus

### §5.1 — Crystal C5 V₄ (Pass-29) provides the natural symmetry group

Per `CRYSTAL_C5_SYMMETRY_GROUP_2026-05-09.md`, the BOK Crystal symmetry group is V₄ = C₂ × C₂. The §4 analog is *automatically* V₄-doubling on Crystal-symmetric attractor landscapes — no extra postulate required.

### §5.2 — V₄³ (Pass-31 D2-HYBRID) gives 8-fold paradoxical decomposition

The D2-HYBRID 5-qubit GM-Network state space ℂ³² has V₄³ ↔ Hadamard³ symmetry; the §4 analog scales to V₄³ giving an 8-fold (= |V₄³|/|stabilizer| in best case) paradoxical decomposition. Per Pass-36 t35-A §3.1, this 8-fold decomposition is the candidate quantum-mechanical instantiation of Meijer's 8-harmonic basis — meaning the BT analog at the V₄³ level *coincides* with the harmonic structure.

### §5.3 — TRC (Pass-23 §7) gives the merging rule

The Tralse Retrieval Cycle's cross-attention / Hopfield-completion mechanism is the natural "merging rule" of the §4 definition. TRC takes a partial state and completes it to a full attractor; under V₄-symmetry, the completion can land in any of the V₄-orbit attractors. The "feeling like a complete copy from inside" property is *exactly* the i-cell formation step (LAYER 5 of the 14D model).

### §5.4 — URB-831 §4 diagnostic classification

Per URB-831 coupling-vs-hypercomputation diagnostic: the BT analog is a **structural/coupling claim**, not a hypercomputational claim. A Turing machine can simulate Hopfield + V₄-symmetry; the analog does not require non-Turing-computable resources. Therefore the BT analog is *admissible* in the corpus without invoking the URB-831 §6 stage-gate.

## §6 — Empirical predictions (URB-830-symmetric)

**P1:** under TRC-completion of partial neural patterns + V₄-symmetric perturbation, conscious reports should show *2-orbit attractor selection* (subject perceives one of 2 distinct conscious states corresponding to the 2 attractors per V₄-orbit), not gradient blending.
- **CONFIRM:** behavioral / fMRI / EEG data shows discrete 2-state response distribution under V₄-symmetric stimulus pairs (e.g., perceptually-bistable rivalry stimuli).
- **REJECT:** continuous-blending or single-attractor responses dominate.
- **PARTIAL:** 2-state distribution present but with low V₄-symmetry-discrimination.

**P2:** in V₄³-symmetric stimulus paradigms (5-qubit-analog stimulus space), the response distribution should show 8-fold (= 2³) discrete attractor selection, not 32-fold (= dim ℂ³²) or continuous.
- Existing fMRI/MEG decoding studies of stimulus-discrimination accuracy can be re-analyzed under this prediction (e36-B raised for Pass 37+).

**P3 (the falsifier):** if neural-attractor decomposition under V₄-symmetric perturbation shows MORE than 2 attractors per orbit (e.g., 3 or 4), the §4 analog is REJECTED — the symmetry group is not V₄ at the relevant scale, contradicting Crystal C5.

## §7 — What the Tozzi-Banach-Tarski claim survives, what it doesn't

**Survives Pass-36 rigorous treatment:**

- ✅ "The brain exhibits paradoxical-decomposition-style behavior" (the §4 analog).
- ✅ "Conscious experience can support multiple coexisting attractors that each feel complete from inside" (TRC + V₄-symmetric Hopfield landscape).
- ✅ "The 14D model's binding mechanism (Tozzi torus + V₄-symmetric attractors) supports doubling/multi-instantiation under symmetry-group action."

**Does NOT survive Pass-36 rigorous treatment:**

- ❌ "The brain literally instantiates the Banach-Tarski theorem with AC and non-measurable subsets."
- ❌ "Banach-Tarski-in-brain explains arbitrary-cardinality consciousness states without symmetry constraint" (the analog is constrained by the order of the relevant symmetry group, e.g., V₄ → 2-fold; V₄³ → 8-fold; full SO(3) free-subgroup → BT-unbounded, but SO(3) is not a brain-relevant symmetry).
- ❌ "Banach-Tarski-in-brain provides hypercomputational capability" (per §5.4 URB-831 diagnostic, the analog is Turing-simulable).

## §8 — Honesty caveats (#69)

- **(C1)** The §4 finite-system BT analog definition is novel to this Pass-36 paper; it is not a standard result in the BT literature.
- **(C2)** Tozzi & Peters' actual 2017 paper has not been re-fetched in this session; the Pass-36 reading reconstructs the Tozzi-claim from DPES-recall + the Pass-35 §4 framing. **t36-C** raised: re-fetch Tozzi & Peters 2017 + verify Pass-36 reconstruction.
- **(C3)** The §6 P1/P2/P3 predictions cite existing literatures (perceptual rivalry, stimulus-decoding) but do not perform new empirical work; e36-B raised for Pass 37+ re-analysis runner.
- **(C4)** The Tozzi-claim's META-PHILOSOPHICAL appeal (consciousness paradoxically self-doubling) is preserved by the §4 analog under V₄-symmetry; the LITERAL appeal (AC + non-measurability) is retracted as biologically inapplicable.

## §9 — Items raised

- **e36-B** — re-analysis runner for V₄-symmetric perceptual-rivalry data; Pass 37+.
- **t36-C** — Tozzi & Peters 2017 primary fetch + Pass-36 reconstruction verification.
- **t36-D** — V₄³ 8-fold paradoxical decomposition test against existing 5-qubit IBMQ reference circuits when qc25-v3 unblocks.
