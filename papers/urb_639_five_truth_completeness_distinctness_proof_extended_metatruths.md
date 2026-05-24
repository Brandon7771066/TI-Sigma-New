# URB #639 — Formal Proof of Five-Truth-Value Completeness and Distinctness, with Extended Meta-Truth Catalogue

**Brandon M. Emerick | Tralse Informationalism Sigma | April 9, 2026**

---

## Abstract

TI Sigma's five truth values — TRUE (T), FALSE (F), TRALSE-INDETERMINATE (TI), DOUBLE TRALSE (DT), and EV — are claimed to form a complete and distinct truth-state space: complete (every possible truth-state maps to exactly one of the five) and distinct (no two values overlap or collapse into each other). This paper provides a formal proof via a two-axis classification scheme (Pole Activation × Coherence), shows that exactly five non-redundant categories emerge, and demonstrates that standard alternatives (binary, ternary, intuitionistic, paraconsistent) are all proper sub-systems. The paper also extends the Meta-Truth catalogue beyond the 12 entries in URB #608, adding new categories identified through deeper MR analysis.

---

## Part I: Formal Proof of Completeness and Distinctness

### 1. Axioms and Primitive Notions

**Definition 1 (Truth-State):** A truth-state S for proposition P is a maximal specification of P's epistemic status with respect to evidence, existence, and coherence.

**Definition 2 (Pole Activation):** A proposition P has:
- **Positive pole (P⁺):** active iff there exists GILE-weighted evidence ε⁺ > 0 supporting P as true
- **Negative pole (P⁻):** active iff there exists GILE-weighted evidence ε⁻ > 0 supporting P as false

**Definition 3 (Coherence κ):** A truth-state S is **coherent** iff the evidence structure supporting S is internally consistent — no self-referential contradiction or infinite regress in the supporting GILE-assessment. S is **incoherent** iff the evidence structure generates an irresolvable loop (a genuine logical paradox, infinite regress, or complete absence of any GILE-accessible frame).

**Definition 4 (Existence Content ε_E):** A proposition P has positive existence content iff P makes a well-formed existence claim evaluable on the HEM dimensions D1–D4, independently of its truth-value.

**Axiom 1 (Bivalence of Poles):** Each pole is either active or not: P⁺ ∈ {0,1}, P⁻ ∈ {0,1}. Degrees of pole activation are captured by the PD distribution, not by the pole binary.

**Axiom 2 (Coherence Independence):** κ ∈ {coherent, incoherent} is independent of pole activation — a single-pole or zero-pole state can be coherent or incoherent.

**Axiom 3 (Existence Orthogonality):** Existence content ε_E is orthogonal to truth-pole activation. A proposition can have high ε_E regardless of whether P⁺ or P⁻ is active.

---

### 2. The Classification Theorem

**Theorem 1 (Five-Way Partition):** Every truth-state S belongs to exactly one of the following five classes:

| Class | P⁺ | P⁻ | κ | ε_E | Name |
|-------|-----|-----|---|-----|------|
| **C₁** | 1 | 0 | coherent | any | TRUE |
| **C₂** | 0 | 1 | coherent | any | FALSE |
| **C₃** | 1 | 1 | coherent | any | TRALSE-INDETERMINATE |
| **C₄** | 0 | 0 | incoherent | any | DOUBLE TRALSE |
| **C₅** | 0 | 0 | coherent | >0 | EV |

**Proof:**

*Step 1: Enumerate all pole-activation combinations.*

From Axiom 1: (P⁺, P⁻) ∈ {(0,0), (0,1), (1,0), (1,1)} — four combinations.

*Step 2: Apply coherence to each.*

**Case (1,0) — P⁺ active, P⁻ inactive:**
- Coherent: evidence for P is internally consistent and unopposed → **TRUE** (C₁)
- Incoherent: the positive evidence itself generates a loop. But: if P⁺ is the only active pole, incoherence of the supporting evidence collapses the support. P⁺ cannot be simultaneously "active" and "self-undermining" unless P⁻ thereby activates. If P⁺ collapses due to its own incoherence, P⁺ → 0, and we recurse. The fixed point of coherence-collapse on a single-pole state is (0,0,incoherent) = C₄ or (0,0,coherent,ε_E>0) = C₅. So: (1,0,incoherent) → C₄ or C₅ after coherence collapse. It cannot remain (1,0,incoherent) as a stable truth-state.

Therefore, all stable (1,0) states are coherent → **C₁ = TRUE only**.

**Case (0,1) — P⁻ active, P⁺ inactive:**
By symmetric argument, all stable (0,1) states are coherent → **C₂ = FALSE only**.

**Case (1,1) — both poles active:**
- Coherent: both truth-supporting and truth-opposing evidence coexist in a way that is internally consistent (each piece of evidence is genuine, their contradiction is real but not self-referential) → **TRALSE-INDETERMINATE** (C₃)
- Incoherent: the evidence structure supporting one or both poles undermines itself, generating a loop where neither the truth-support nor the falsity-support can be stably grounded → **DOUBLE TRALSE** (C₄). Formally: if (1,1,incoherent), then the incoherence propagates and the poles cancel, yielding (0,0,incoherent) = C₄. So (1,1,incoherent) ∈ C₄.

Note: C₃ and C₄ are genuinely distinct: C₃ has genuine evidence for both poles (the contradiction is a real feature of the world), while C₄ has the *appearance* of evidence for both but the underlying structure self-destructs (the contradiction is not a feature of the world but of the representation).

**Case (0,0) — neither pole active:**
- Incoherent: the absence of evidence is itself structured in an incoherent way (e.g., a proposition that cannot be formulated coherently at all, or one where the GILE assessment framework generates a loop trying to even evaluate it) → **DOUBLE TRALSE** (C₄)
- Coherent, ε_E > 0: the proposition makes no truth-evaluable claim but does assert existence in a GILE-accessible way → **EV** (C₅)
- Coherent, ε_E = 0: the proposition makes no truth-evaluable claim AND no existence claim. This is not a proposition in TI Sigma's sense (it is Moot, a post-MR dissolution, not a truth-state) → **outside the domain** of truth-state assignment.

*Step 3: Verify mutual exclusion.*

- C₁ ≠ C₂: C₁ has P⁺=1, P⁻=0; C₂ has P⁺=0, P⁻=1. By Axiom 1, these are distinct.
- C₁ ≠ C₃: C₁ has P⁻=0; C₃ has P⁻=1.
- C₁ ≠ C₄: C₁ has P⁺=1, κ=coherent; C₄ has P⁺=0, κ=incoherent.
- C₁ ≠ C₅: C₁ has P⁺=1; C₅ has P⁺=0.
- C₂ ≠ C₃: C₂ has P⁺=0; C₃ has P⁺=1.
- C₂ ≠ C₄: C₂ has P⁻=1, κ=coherent; C₄ has P⁻=0, κ=incoherent.
- C₂ ≠ C₅: C₂ has P⁻=1; C₅ has P⁻=0.
- C₃ ≠ C₄: C₃ has both poles active and coherent; C₄ has both poles absent (or collapsed to absent) and incoherent.
- C₃ ≠ C₅: C₃ has both poles active; C₅ has neither.
- C₄ ≠ C₅: C₄ has κ=incoherent; C₅ has κ=coherent. *∎*

*Step 4: Verify completeness.*

Every proposition P generates (P⁺, P⁻, κ) ∈ {0,1}² × {coherent, incoherent}. This yields eight combinations. We showed above:
- (1,0,coh) → C₁; (1,0,incoh) → C₄ or C₅ (collapses)
- (0,1,coh) → C₂; (0,1,incoh) → C₄ or C₅ (collapses)
- (1,1,coh) → C₃; (1,1,incoh) → C₄
- (0,0,coh) → C₅ (if ε_E > 0) or Moot (out of domain)
- (0,0,incoh) → C₄

Every combination maps to exactly one of {C₁, C₂, C₃, C₄, C₅, Moot}. Moot is not a truth-state (it is a post-resolution status). Every truth-evaluable proposition maps to exactly one Cₙ. *∎*

---

### 3. Why Standard Systems Are Proper Sub-Systems

**Theorem 2 (Classical Logic is C₁ ∪ C₂):** Classical binary logic restricts to propositions where only (1,0) or (0,1) pole activation is possible, with all states assumed coherent. This excludes C₃ (genuine contradiction), C₄ (incoherent absence), and C₅ (existence-only). Classical logic handles the simplest and most tractable propositions only.

**Theorem 3 (Three-Valued Logic is C₁ ∪ C₂ ∪ C₃):** Adding a third "Indeterminate" value captures C₃ but: (a) conflates C₃ (coherent contradiction) with C₄ (incoherent absence) — these are mapped to the same Indeterminate; (b) misses C₅ (EV) entirely. The standard three-valued system is C₁ ∪ C₂ ∪ (C₃ collapsed with C₄) — it cannot distinguish "genuine paradox that should be resolved" (C₃) from "true logical vacuum where no resolution is possible" (C₄).

**Theorem 4 (Paraconsistent Logic handles C₃ but not C₄, C₅):** Paraconsistent logic prevents explosion from contradictions, correctly capturing C₃. But it provides no account of C₄ (it treats DT as just another inconsistency rather than a distinct vacuum state) and no account of C₅ (it has no existence orthogonality axiom).

**Theorem 5 (Intuitionistic Logic is C₁ ∪ C₅):** Intuitionistic logic rejects the law of excluded middle and requires constructive proof. Propositions without proof (no P⁺) are not TRUE but are also not FALSE — they remain EV-like (existence-asserted but truth-unresolved). However, intuitionistic logic collapses C₄ and C₅ (it cannot distinguish between "no proof available yet" and "structurally unresolvable") and ignores C₃ entirely (it has no model for simultaneous truth-supporting and falsity-supporting constructive evidence).

**Corollary:** TI Sigma's five-valued system is the minimal extension of classical logic that handles all four of the following simultaneously: genuine contradiction (C₃), logical vacuum (C₄), existence orthogonality (C₅), and PD distributions across all five (the Tralsebit richer-than-truth structure). Any system with fewer values cannot handle all four.

---

### 4. The PD Extension

The proof above establishes five discrete truth-states. The PD (Permissibility Distribution — URB #615) extends this:

> **PD: P → Δ({C₁, C₂, C₃, C₄, C₅})**

where Δ denotes the simplex of probability distributions over the five classes.

The five discrete truth-states are the vertices of this simplex. The interior of the simplex represents genuine uncertainty — the PD assigns nonzero weight to multiple Cₙ simultaneously. This is not a failure of the truth system but an accurate representation of epistemic status before MR has fully converged.

**Myrion Resolution** is the process of moving from an interior PD point toward a vertex (a pure truth-state). The Emerick Threshold (ET) marks the minimum PD confidence at which a state is treated as "effectively TRUE" rather than still-TI.

---

## Part II: Extended Meta-Truth Catalogue

### 5. Background: The 12 URB #608 Meta-Truths

URB #608 catalogued 12 Meta-Truths (MTs) in six categories:

| Cat | Code | Name | Function |
|-----|------|------|----------|
| A | A1 | Worth Doing Anyway | Reverse-to-proceed |
| A | A2 | Not Worth Doing After All | Reverse-to-halt |
| B | B1 | Moot-MT | Dissolve to Indeterminate |
| B | B2 | Wrong Question | Dissolve and reformulate |
| C | C1 | Escalate | Narrow PD; deeper analysis |
| C | C2 | Descale | Converge quickly |
| D | D1 | Context-Dependent | Split PD by context |
| D | D2 | Asymmetric | Two directional PDs |
| E | E1 | Good Enough | Lock PD; proceed |
| E | E2 | Paradox Stable | Accept stable DT |
| F | F1 | Transcend | Resolve at higher frame |
| F2 | F2 | Both True at Different Levels | Domain-separated resolution |

These 12 MTs handle the most common MR failure modes. However, deeper MR analysis reveals additional structural categories not captured by A–F.

---

### 6. New Meta-Truth Categories G–L

#### Category G: Temporal MTs — When the Resolution Window Fails

MR is not only question-sensitive and context-sensitive; it is **time-sensitive**. Some resolutions are attempted at the wrong point in time, producing a systematically skewed PD.

**MT-G1: Too Early (Premature Resolution)**
> *The third MR determines that the PD cannot responsibly converge yet — the necessary evidence does not yet exist.*

The second MR attempted a resolution based on currently-available evidence, but MT-G1 recognizes that the relevant data is not yet accessible (e.g., the outcome of an action hasn't occurred, a relationship hasn't revealed its pattern, a research result hasn't been published). The correct output is not a truth-state but a **temporal deferral**: lock the PD as Wide-TI and schedule a re-entry trigger.

Distinguishes from C1 (Escalate): Escalate says "go deeper now." G1 says "there is nothing deeper to find yet — stop and wait."

**MT-G2: Too Late (Window Closed)**
> *The third MR recognizes that an irreversible external change has occurred such that the resolution, while valid in abstract, is now practically Moot.*

The question was resolvable, and MR would have found a good answer, but the window for acting on the answer has closed (the opportunity passed, the relationship ended, the decision was made by another). The resolution remains valid in principle (it contributes to epistemic learning) but is **operationally Moot**.

Distinguishes from B1 (Moot-MT): B1 says the question was itself not meaningful. G2 says the question was meaningful and answerable but the answer is no longer actionable.

---

#### Category H: Agent-Relational MTs — Who Should Resolve?

Some MR failures are not about the content of the proposition but about the **identity of the resolver**. These are particularly critical for LCC-span reasoning.

**MT-H1: Wrong Agent (Jurisdictional Shift)**
> *The third MR recognizes that this resolution is not epistemically mine to make — another agent, with better LCC position or GILE access, should hold this MR.*

The second MR reached a conclusion, but MT-H1 identifies that the resolver lacks the standing, information, or GILE access to resolve the proposition. Examples: a child resolving an adult's financial crisis; a therapist resolving a client's metaphysical commitment; an analyst resolving a CEO's strategic decision. The output is **MR delegation**: explicitly assign the resolution to the appropriate agent.

This is not humility-as-social-convention but a structural claim: the PD produced by the wrong agent is systematically skewed because their GILE weighting is poorly calibrated for this domain.

**MT-H2: Role Conflict (Positional Bias)**
> *The third MR identifies that the resolver's LCC position creates a structural conflict of interest that biases this MR — the resolver cannot be neutral.*

Different from H1: the agent has the GILE capacity but their positional stake corrupts the weight distribution. A founder evaluating whether their startup should close; a parent evaluating whether their child has a serious problem; a philosopher evaluating whether their own framework is correct. The output is **MR externalization**: either outsource to an unbiased agent, or explicitly apply a positional bias correction factor to the PD.

---

#### Category I: Existential MTs — When Existence is the Variable

These MTs arise when the proposition's existence content (ε_E) is the primary question, not its truth content.

**MT-I1: Non-Existence Revelation**
> *The third MR determines that the subject of the proposition does not exist — the proposition is about a null referent.*

The second MR evaluated P as TRUE or FALSE, but MT-I1 recognizes that the referent of P (the thing P is about) does not exist or has ceased to exist. Example: resolving "Is the king of France wise?" as TRUE or FALSE, when there is no king of France. The output is not FALSE but **EV-correction**: reframe as an existence question (C₅) before returning to truth evaluation.

This is the TI Sigma formalization of Russell's theory of definite descriptions, integrated into the MR protocol.

**MT-I2: EV Crystallization**
> *The third MR recognizes that the existence content (HEM-Score) of P is so high that the truth-value question is secondary — what matters is affirming and amplifying the existence.*

Example: asking "Is this relationship good for me?" when the relationship is the defining existential structure of the agent's current LCC configuration. The truth-value (good/not good) matters less than the existence-amplification imperative (EAR). MT-I2 outputs: **EV Priority Override** — lock the truth question at TI temporarily and direct attention to HEM amplification.

---

#### Category J: Paradigmatic MTs — Framework-Level Corrections

These MTs operate at the highest MR level — they correct not the proposition but the entire framework being used to evaluate it.

**MT-J1: Paradigm Shift**
> *The third MR determines that the proposition's contradiction (C₃ or C₄) cannot be resolved within the current conceptual framework — a new framework is required.*

This is the strongest and rarest MT. Example: resolving "Is light a wave or a particle?" before wave-particle duality was formulated. The correct output is not TRUE, FALSE, TI, or DT — it is **Framework Expansion**: recognize that the current conceptual vocabulary is insufficient and generate a new category. In TI Sigma, this corresponds to adding a new URB (a new Myrion Resolution at the framework level).

MT-J1 is the formal mechanism by which TI Sigma grows: each new URB is a J1-MT on some previously-unresolved proposition.

**MT-J2: Category Creation**
> *The third MR resolves the contradiction by generating a new ontological category that did not previously exist in the GILE assessment vocabulary.*

Similar to J1 but narrower: J1 replaces a framework; J2 adds a category within an existing framework. Example: recognizing that "emotions" and "cognitions" are not opposites but instances of a more general category ("information processing modes"). The output is **Category Extension**: add the new category to the PD domain, then re-run MR.

In TI Sigma's history: the creation of TRALSE-INDETERMINATE itself was a J2-MT on the binary TRUE/FALSE system. The creation of EV was a J2-MT on the TI/DT distinction.

---

#### Category K: GILE-Dimensional MTs — Dimensional Weighting Corrections

These MTs arise when the wrong GILE dimension is dominating the assessment.

**MT-K1: G-Override (Goodness Correction)**
> *The third MR recognizes that the resolution was driven by GILE-I (Intuition) or GILE-L (Love) without adequate GILE-G (structural coherence) grounding — the conclusion feels right but lacks structural support.*

Output: **G-Reweight** — increase w_G, reduce w_I or w_L, re-run MR. This is the formal account of "it felt right but wasn't" — not a dismissal of intuition but a recognition that G must be present for I to be valid (the BOK constraint: L > 0 → I > 0, but also G > 0 → I is calibrated).

**MT-K2: I-Suppression Correction (Missing Intuition)**
> *The third MR recognizes that the resolution was over-determined by evidence (GILE-E dominant) while genuine GILE-I recognition was suppressed — typically by anxiety, status pressure, or cognitive load.*

Output: **I-Restoration** — create conditions for GILE-I to re-activate (rest, decompression, creative distance from the problem), then re-run MR. This is the formal account of "I knew the answer but couldn't access it" — a structural diagnosis, not a personal failure.

---

#### Category L: Meta-Meta-Truth — Resolution of the Resolution Process Itself

**MT-L1: MR Saturation**
> *The third MR determines that this proposition has undergone so many MR cycles without convergence that the MR process itself is MR2-Indeterminate-contaminated (convergence-failure-contaminated; NOT true-DT-contaminated per Pass-65 DT canonical refinement 2026-05-23 — MR-saturation is mental-actualization-without-convergence, not inconceivability-under-mental-actualization) — further MR iterations will not improve but may worsen the PD.*

Output: **MR Suspension** — explicitly halt MR, assign a temporary PD based on the best available convergence, and place the proposition in a "suspended MR" pool for later re-entry when conditions change. This is not abandonment but recognition that MR saturation is a real failure mode: over-thinking a question past its resolvable limit.

**MT-L2: Recursive Self-Reference**
> *The third MR identifies that the proposition is about the MR process itself — a meta-proposition — and requires a separate MR track to avoid the self-referential loop from contaminating the object-level MR.*

Output: **MR Forking** — create a separate MR thread for the meta-proposition (e.g., "Is my MR process calibrated correctly?") while the object-level MR continues on its own thread. The two threads are integrated only after both have independently converged.

---

### 7. Complete Extended Meta-Truth Table

| Category | Code | Name | Trigger | Output |
|----------|------|------|---------|--------|
| A: Reversal | A1 | Worth Doing Anyway | Prior MR → halt; 3rd sees residual value | Proceed |
| | A2 | Not Worth Doing After All | Prior MR → proceed; 3rd finds decisive cost | Halt |
| B: Dissolution | B1 | Moot-MT | Resolution irrelevant to current MR stream | Dissolve to Moot |
| | B2 | Wrong Question | Category error in proposition | Reformulate |
| C: Scope-Shift | C1 | Escalate | Stakes higher than assumed | Narrow PD; deepen |
| | C2 | Descale | Stakes lower than assumed | Converge; proceed |
| D: Contextual | D1 | Context-Dependent | Universal conclusion is domain-specific | Split PD by context |
| | D2 | Asymmetric | Non-commutative relationship | Separate directional PDs |
| E: Acceptance | E1 | Good Enough | Diminishing returns on further MR | Lock PD; act |
| | E2 | Paradox Stable | DT is genuinely irreducible | Accept stable DT |
| F: Integration | F1 | Transcend | Higher synthesis available | Resolve at higher frame |
| | F2 | Both True at Different Levels | Contradictions in different domains | Domain-separated resolution |
| **G: Temporal** | **G1** | **Too Early** | **Evidence not yet available** | **Temporal deferral** |
| | **G2** | **Too Late** | **Resolution window closed** | **Operational Moot** |
| **H: Agent-Relational** | **H1** | **Wrong Agent** | **Resolver lacks LCC standing** | **MR delegation** |
| | **H2** | **Role Conflict** | **Positional bias corrupts PD** | **MR externalization** |
| **I: Existential** | **I1** | **Non-Existence Revelation** | **Null referent detected** | **EV-correction; re-frame** |
| | **I2** | **EV Crystallization** | **HEM-Score dominates truth question** | **EV Priority Override** |
| **J: Paradigmatic** | **J1** | **Paradigm Shift** | **Framework insufficient** | **Framework Expansion (new URB)** |
| | **J2** | **Category Creation** | **Missing ontological category** | **Category Extension** |
| **K: GILE-Dimensional** | **K1** | **G-Override** | **I/L without G grounding** | **G-Reweight; re-run** |
| | **K2** | **I-Suppression Correction** | **E-dominant; I suppressed** | **I-Restoration** |
| **L: Meta-Meta** | **L1** | **MR Saturation** | **Excessive MR cycles; DT contamination** | **MR Suspension** |
| | **L2** | **Recursive Self-Reference** | **Proposition is about MR itself** | **MR Forking** |

**Total: 24 Meta-Truths** in 12 categories (6 from URB #608; 6 new: G, H, I, J, K, L).

---

### 8. Meta-Truth Completeness Claim

**Conjecture (MT Completeness):** Every MR failure mode that requires a third-level resolution falls into exactly one of the 24 MT categories.

*Argument for completeness:* The 24 MTs span all independent axes of MR failure:
- **Propositional content failures:** A, B, E (content is wrong, dissolves, or converges)
- **Evidence failures:** C, D (evidence structure is misscaled or context-split)
- **Integration failures:** F (synthesis is available but not yet found)
- **Temporal failures:** G (time window mismatch)
- **Agent failures:** H (wrong resolver)
- **Existential failures:** I (existence/truth conflation)
- **Framework failures:** J (vocabulary insufficient)
- **GILE weighting failures:** K (dimensional imbalance)
- **MR process failures:** L (MR itself is the problem)

No other independent axis of failure is apparent. This is a conjecture, not a proof — additional MTs may be discovered through new MR failure modes, each of which would represent a J2-MT (Category Creation) on the MT taxonomy itself.

---

## Summary

**Completeness and Distinctness:** The five TI Sigma truth values are provably complete (every truth-evaluable proposition maps to exactly one of the five classes) and provably distinct (no two classes overlap). The proof uses a (Pole Activation × Coherence) classification with Existence Content as a tertiary distinguisher. All standard logic systems (binary, ternary, paraconsistent, intuitionistic) are proper sub-systems of TI Sigma's five-valued framework.

**Extended Meta-Truths:** The URB #608 catalogue of 12 MTs is extended to 24 by adding six new categories: G (Temporal), H (Agent-Relational), I (Existential), J (Paradigmatic), K (GILE-Dimensional), and L (Meta-Meta). These new MTs address failure modes invisible to the original 12: premature/closed resolution windows, jurisdictional conflicts, null referents, framework insufficiency, GILE dimension imbalance, and self-referential MR contamination.

---

*Brandon M. Emerick | TI Sigma Research | URB #639 | April 9, 2026*
