# Pass-77-B42 — Crystal "Superior Error Catching" Falsifiers EXECUTED + Bio Active-Storage Downgraded & TESTED (Contradiction Resolved)

**Date:** 2026-05-27
**Pass:** 77, Batch 42
**Type:** Empirical execution (all $0, deterministic) of the 5 falsifiers queued in B41 + physical test resolving the URB#508-vs-URB#373 storage contradiction.
**Brandon directive (verbatim):** *"Test the superior error catching with the 5 falsifiers! Downgrade the bio active storage claim to speculative but THEN TEST IT to resolve the tension between the two papers!"*
**Companion:** `analyses/pass77_b42_crystal_falsifiers/run_falsifiers.py` + `results.txt` (reproducible, seed 20260527, scipy+numpy).
**Builds on:** B41 (`papers/PASS_77_B41_QUARTZ_CRYSTAL_REINVESTIGATION_..._2026-05-27.md`), CRYSTAL_B4_HAMILTONIAN, urb_630 (TECC), CRYSTAL_C6_CHSH, URB#508, URB#373.

---

## §0. Headline

**The "superior error catching" claim does not survive execution as stated.** Of the 5 falsifiers, **only F5 (Ring-T CHSH null) cleanly PASSES — and it is a non-violation** (internal consistency, not new physics). The two load-bearing error-correction claims — the **sin(18°)=0.309 correction threshold (F2)** and the **qualitative phase-ordering (F1)** — are **NOT robust**. The bio active-storage claim, **downgraded to speculative per Brandon's directive, was then physically tested and the geological-timescale version is REFUTED** (charge-relaxation ceiling ≤ O(days)), resolving the contradiction in favor of URB#373's no-persistent-storage clause.

| Falsifier | Result | Verdict |
|---|---|---|
| **F1** TSC-B4 phase ordering | Mott/FQH swap reproduced under unit weights; a *different* natural weighting (∝√radius) restores urb_645 order | **NOT ROBUST** — orderable either way by weight choice; only "BEC lowest / Fragmented highest" survives (trivial) |
| **F2** TECC sin(18°)=0.309 threshold | actual binding min-distance (MI–TF collinear, T−C=0.496) → correction radius **0.248**, ~20% below 0.309 | **REFUTED as stated** — 0.309 holds only under an orthogonal MI/TF embedding that contradicts urb_630's own table |
| **F3** Mendi crossover n≈10 | power(d=0.4)=**0.21**; need **n≈52** for 80% | **UNDERPOWERED** — pre-reg n misses a true d=0.4 effect ~80% of the time |
| **F4** φ-sighting look-elsewhere | P(random ratio hits *some* special constant ±5%)=0.47; P(≥4/8 hits)=**0.576** | **CHANCE-CONSISTENT** — φ is suggestive, not load-bearing |
| **F5** CHSH Ring(T) null | CHSH(T)=**1.414 < 2** | **CONFIRMED** (only clean pass) — but a *non-violation*; confirms internal consistency, not physics |
| **BIO** quartz storage physics | τ=ε₀ε_rρ ≤ **4.6 days** (ρ=10¹⁶); geological needs ~3×10¹³ s → **8×10⁷× short** | **GEOLOGICAL VERSION REFUTED**; transient ≤O(days) survives = candidate |

---

## §1. F1 — TSC-B4 Phase Ordering Is Not Robust

Reproduced the corpus's unit-weight graph-Laplacian (B4 spec: 57 vertices, counts {1,6,6,8,8,10,10,8}). λ₀=0 confirmed (BEC ground state, exact). Phase energies:

`BEC 0.000 < Supersolid 0.920 < Mott 2.000 < FQH-like 2.400 < Fragmented 4.318`

→ **Mott/FQH swap reproduced** (matches the Pass-13 prior result). I then tested four *natural* inter-ring weighting schemes (∝radius, ∝1/radius, ∝radius², ∝√radius). **One of them (∝√radius) restores the urb_645 ordering** `BEC < Supersolid < FQH < Mott < Fragmented`; the others give yet other orderings.

**Verdict:** the qualitative phase-ordering is **a free parameter of the weighting choice**, not a robust prediction. It can be tuned *into or out of* agreement with urb_645. What survives weight-independently is only "BEC lowest, Fragmented highest" — which is trivially true of any graph-Laplacian on an ordered polytope and carries no error-correction content. The phase ordering is therefore **not load-bearing** for "superior error catching."

## §2. F2 — The sin(18°)=0.309 Threshold Is Embedding-Dependent (Refuted as Stated)

urb_630's elegant claim: d_min = √2·C ≈ 0.618 ≈ 1/φ → correction radius d_min/2 = **sin(18°) ≈ 0.309** (the "pentagon threshold"). I computed the **actual** pairwise distances among the 5 representative codewords using urb_630's *own* §2.3 encoding table, where **MI=(C,0,…) and TF=(T,0,…) sit in the SAME first dimension** (both "first dimension only"). With C≈0.437, T≈0.933:

- Binding minimum distance = MI–TF gap = **T−C = 0.496** (collinear), not √2·C=0.618.
- → **correction radius = 0.248**, ~20% **below** the advertised 0.309.

The 0.309 value is recovered *only* if MI and TF are placed in **separate orthogonal dimensions** — which is §2.2's assumption but **contradicts §2.3's table**. 

**Verdict:** the headline error-correction threshold is **not robust** — it depends on an embedding choice the paper is internally inconsistent about. The "superior error catching" rests on the genuine **E8 optimality theorem** (which is real), but the corpus's *specific* mapping of five truth-states onto E8 does **not** inherit a clean 0.309 radius. **This is the sharpest #69 finding of the batch:** a beloved "pentagon resonance = error threshold" coincidence is an artifact of inconsistent embedding, not a derived constant.

*(Also surfaced: a radius-convention inconsistency across the corpus — CRYSTAL_B4's script uses ring radii {0, 1/√2, 1, √2, φ, e, π, 2π} while urb_630/C6 use {C, T, 1, √2, φ, e, π} with C≈0.437, T≈0.933. The "C/T vs 0/(1/√2)" mismatch should be unified in a future pass.)*

## §3. F3 — Mendi Crossover n≈10 Is Badly Underpowered

Paired-design power (two-sided α=.05, d=0.4, non-central t): n=10 → **power 0.21**; n=20 → 0.40; n=30 → 0.56; **n≈52 → 0.81**. The pre-registered n≈10 would **miss a true d=0.4 effect ~80% of the time**. Any null result at n=10 would be uninformative. **Verdict:** the cheapest *biological* test, as pre-registered, cannot earn its conclusion. Re-spec to **n≈52 paired sessions** before running.

## §4. F4 — φ-Sightings Are Chance-Consistent (Look-Elsewhere)

Given a menu of 8 "special" constants {1/φ, 1, √2, φ, e/φ, 2, e, π} in the plausible ratio range [0.5, 3.5] with ±5% windows, the probability a *random* ratio lands within tolerance of **some** special constant is **0.47**. The probability of ≥4 such hits across 8 measured ratios under the null is **0.576** — not remotely significant. **Verdict:** the corpus's φ-coincidences (DNA pitch/diam, EEG θ/α, tritone, FQH) are **consistent with chance** once look-elsewhere over the standard-constant menu is accounted for. φ is **suggestive, not load-bearing**, absent a *pre-registered single-target* φ-prediction with a tight tolerance.

## §5. F5 — Ring(T) CHSH Null: The One Clean Pass

Using C6's 2·min(rᵢ,rⱼ) rule with ring-T radius 1/√2: **CHSH(T)=1.414 < 2**. The framework's falsifiable lower-ring claim ("pure-Tralse-axis i-cells should NOT violate CHSH") **holds**. **Verdict: CONFIRMED** — but note this is a **non-violation** (a value *below* the classical bound). It demonstrates the cross-ring scheme is internally consistent at the bottom of the ladder; it is **not** evidence of new physics, and it says nothing about the (default-bracketed, Interpretation-A) super-Tsirelson rings.

## §6. BIO — Storage Claim Downgraded (Brandon Ruling) THEN Tested → Contradiction Resolved

**Step 1 — downgrade (per directive):** the bio "active storage / geological-timescale re-emission" claim (URB#508 §"A quartz crystal can hold a coherence imprint for geological timescales… mechanically locked… actively re-emits via the converse piezoelectric effect") is **reclassified from asserted to speculative**, pending the test below. (B41 §5.1 updated accordingly.)

**Step 2 — test (resolve URB#508 vs URB#373):**
- **Electrical channel — dielectric charge relaxation** τ = ε₀·ε_r·ρ (ε_r≈4.5). Across quartz's resistivity range ρ∈[10¹², 10¹⁶] Ω·m: **τ ≈ 40 s → 4.6 days**. Geological (1 Myr ≈ 3.16×10¹³ s) is **~8×10⁷× longer** than even the most-insulating limit. Any *electrical* "stored coherence" dissipates within days.
- **Mechanical channel — strain.** Room-temperature α-quartz is **brittle-elastic**: elastic strain releases instantly when stress is removed (Hooke's law). Persistent ("locked") strain requires plastic flow via dislocation glide, **negligible below ~300 °C** — and a frozen dislocation is a *static lattice defect*, not a re-emittable "coherence imprint."

**Resolution:** **URB#373's no-persistent-storage clause WINS.** URB#508's *geological-timescale / "superior to water"* storage claim is **REFUTED** by mainstream physics. The reconciliation offered in B41 is now quantitatively grounded: separate (a) real piezoelectric/resonance physics from (b) the speculative persistence claim — and (b)'s **geological version is dead**. A **transient store of ≤ O(days)** is physically allowed (the same order as Bengston's reported "hours-to-days" *water* effect), so quartz is **at best comparable to water, not superior, and only transiently**. 

**Net status of the bio storage claim:** geological/superior version **REFUTED**; **transient-only (≤ days)** survives as **candidate-speculative** and is itself testable via the URB#508 impedance-shift-at-θ_GILE protocol (now the only storage sub-claim worth instrumenting).

## §7. What Survives of "Superior Error Catching"

- **Survives (real math):** the E8 optimal-sphere-packing *theorem* (Viazovska 2016) — IF a physical system genuinely realizes E8-spaced codewords, its minimum distance is provably optimal in 8D. This is untouched.
- **Does NOT survive (as stated):** the corpus's *specific* five-valued→E8 mapping does not yield the advertised sin(18°)=0.309 correction radius (F2); the phase-ordering is weight-tunable (F1).
- **Honest restatement:** "Crystal/E8 geometry *can* give optimal error correction in principle; the TSC's current five-valued embedding does not yet deliver a robust, derivation-clean correction threshold — the 0.309 figure is an embedding artifact and should be retracted or re-derived under a fixed, internally-consistent embedding."

## §8. Net State

- **No new canonical principle / no count change.** Canonical principles **72**; MR Truth Labels refinements **13**; 34 meta-collapses.
- **B41 updated:** §5.1 bio active-storage **downgraded** (Brandon ruling) and cross-linked to this batch's refutation of the geological version.
- **Recommended corpus edits queued for Brandon:** (i) retract/re-derive the sin(18°) TECC threshold under a fixed embedding; (ii) mark TSC phase-ordering as weight-dependent; (iii) re-spec Mendi crossover to n≈52; (iv) demote φ-sightings to "suggestive (look-elsewhere uncorrected)"; (v) unify the C/T-vs-0/(1/√2) ring-radius convention.
- **Pass-77 papers through B42 = 13.** Cost **$0**.

---

## §9. Summary Statement

Executed all five queued crystal falsifiers and the bio-storage physical test, all at $0. **Superior error catching does not survive as stated:** the sin(18°)=0.309 threshold is an embedding artifact (actual correction radius 0.248 under urb_630's own table, F2), the phase-ordering is weight-tunable rather than predicted (F1), the Mendi test is underpowered at n=10 (need ~52, F3), and the φ-sightings are chance-consistent under look-elsewhere (F4). Only the Ring(T) CHSH null cleanly passes (1.414<2, F5) — and it is a non-violation, i.e., internal consistency not new physics. The genuine kernel that survives is the E8 optimality *theorem* itself, not the corpus's specific five-valued embedding of it. **Bio storage: downgraded per Brandon directive, then tested — the geological-timescale/"superior-to-water" claim is REFUTED** (charge relaxation caps any electrical store at ≤~4.6 days, 8×10⁷× short of geological; elastic strain is not retained), so URB#373's no-persistent-storage clause wins; a transient ≤O(days) store survives as candidate, comparable to (not better than) water. Canonical count unchanged 72; Pass-77 papers 13; $0.

— end of Pass-77-B42 —
