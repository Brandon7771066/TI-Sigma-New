# Pass-77 B75 — Real-world survey: how well disciplines follow the UOP, and the SHAPES of the truth-vs-existence curve over time

**Date:** 2026-05-27 (Pass-77 batch-75)
**Mode:** DPES · ASYMMETRIC #69 brutal honesty
**Budget:** <$50, $0 spent (local scipy/numpy/matplotlib).
**Compute:** `analyses/pass77_b75_uop_discipline_survey/run_b75.py` (+`results.json`, 4 figures)
**Brandon directive (B75):** *"Do a real-world survey of how well different disciplines actually
prioritize the right dimensions and successfully follow the UOP. Also curious how the different shapes
of each graph look as truth and existence get prioritized over time."*

---

## 0. The honesty boundary, stated up front (#69)

This batch has a **principled half** and an **estimated half**, and they must not be conflated:

- **OPTIMAL allocation per discipline = principled.** It is the exact B74 UOP optimization
  (`max ρ·f_capped(A) + g(H)`, `H = 1 − Σcᵢxᵢ`, B72 fragility costs, domain-matched weights+ρ).
- **ACTUAL allocation per discipline = AGENT ARCHETYPE, not a measurement.** Each field's real-world
  practice is encoded as a reasoned `{G,I,L,E}` profile with a one-line documented-tendency basis. 7 of
  the 12 disciplines' weight-profiles and ρ are *also* agent estimates (`src="agent"`); only 5 carry
  `src="urb_611"`. **These encode the agent's priors and are contestable.**

**Therefore the defensible deliverables are (a) the curve/trajectory SHAPES and (b) the qualitative
PATTERN — not the exact adherence scores.** This is the same over-claim discipline Brandon demanded in
B72 ("by-construction vs independent"); declared, not hidden. Empirical upgrade path: replace the
archetypes with bibliometric data, replication rates, and practitioner surveys per field.

**One methodological note that matters:** the first metric used positive-orthant **cosine** for
"dimension-match" — it sat at 0.79–0.99 for everyone and did **not** discriminate (it mechanically
rewarded high-ρ fields and produced a non-credible ranking with theology #1, molecular-biology last).
That was a metric defect, reported and **fixed** with a scale-free **mean-centered correlation** (does
a field over/under-weight the right dims *relative to each other*). I did **not** keep tuning past that
— forcing an intuitive ranking would be the unfalsifiable-elasticity failure #69 warns against.

---

## 1. The SHAPES (the part that is robust) — Brandon's main curiosity

### 1.1 The universal shape as truth is prioritized (Fig 1 `fig1_J_shape_vs_truth.png`)

As a discipline pushes its truth aggregate **A** up, the UOP objective **J** **rises → peaks near
A = 0.93 → declines.** A concave peak, *not* a monotone climb. **Over-prioritizing truth past 0.93
LOWERS J** — the quadratic over-reach penalty is the UOP punishing zealotry. This is the GTT-1
"too much truth costs existence" made visual.

**ρ controls the shape:**
- **High ρ (GILE/abstract-dominant, e.g. math 2.4):** tall, sharp peak located **exactly at 0.93** —
  the cap *binds*.
- **Low ρ (HEM/physical-dominant, e.g. molecular-bio 0.6):** flat, low peak located **below 0.93** —
  the existence term dominates and the cap never binds.

This is the **B74 result re-expressed as a curve shape**: 0.93 is a ceiling that only *binds* for
high-ρ disciplines. The graph *is* the theorem.

### 1.2 The truth-vs-existence tradeoff (Fig 4 `fig4_truth_existence_tradeoff.png`)

Rising truth **A** and falling existence **H** cross; **J** peaks where their marginal trade balances
(A ≈ 0.93 for ρ = 1.6). Visual proof that the UOP optimum is interior — neither truth-max nor
existence-max.

### 1.3 Four trajectory shapes over TIME (Fig 3 `fig3_time_trajectories.png`)

Modeling a discipline's truth aggregate **A(t)** maturing over time gives four distinct **shapes**:

| archetype | A(t) shape | J(t) shape | reading |
|---|---|---|---|
| **healthy climber** | saturating rise → 0.93 plateau | monotone rise → plateau (J max) | matures to the cap and stays |
| **truth-zealot** | overshoots toward 1.0 | rises then **turns DOWN** | over-reach is self-punishing |
| **existence-stuck** | low plateau (~0.55) | low plateau, never reaches potential | stagnation below the cap |
| **self-correcting** | overshoot then damped return to 0.93 | dips then **recovers** | the discipline that catches its own over-reach |

The four J-shapes are visibly different — a saturating curve, a hump, a low flat line, and a
dip-and-recover. This directly answers "how the different shapes look as truth and existence get
prioritized over time."

---

## 2. The survey (read as PATTERN, not leaderboard)

UOP-adherence = 0.6·(dimension-match, mean-centered corr mapped to [0,1]) + 0.4·(J-efficiency
J_act/J*). Sorted:

| discipline | ρ | A_act | truth status | dim-match | J-eff | adherence | src |
|---|---|---|---|---|---|---|---|
| theoretical_mathematics | 2.4 | 0.733 | under | 0.990 | 0.962 | **0.979** | urb_611 |
| theology_religion | 2.0 | 0.762 | under | 0.982 | 0.942 | 0.966 | agent |
| climate_science | 1.3 | 0.808 | under | 0.988 | 0.929 | 0.964 | agent |
| academic_philosophy | 2.0 | 0.719 | under | 0.943 | 0.973 | 0.955 | agent |
| fine_art_aesthetics | 1.2 | 0.714 | balanced | 0.965 | 0.919 | 0.947 | urb_611 |
| law | 1.1 | 0.605 | under | 0.941 | 0.896 | 0.923 | agent |
| molecular_biology | 0.6 | 0.775 | balanced | 0.947 | 0.823 | 0.897 | urb_611 |
| mainstream_economics | 1.4 | 0.588 | under | 0.832 | 0.898 | 0.859 | agent |
| engineering | 0.9 | 0.775 | balanced | 0.703 | 0.896 | 0.780 | agent |
| politics_governance | 1.0 | 0.527 | under | 0.652 | 0.889 | 0.747 | agent |
| clinical_medicine | 1.1 | 0.831 | balanced | 0.618 | 0.914 | 0.737 | agent |
| social_work_therapy | 0.9 | 0.723 | balanced | 0.348 | 0.899 | 0.569 | urb_611 |

---

## 3. The three honest findings

### 3.1 Defensible & intuitive (the pattern that survives)
Truth-dominant fields whose practice tracks their optimal *shape* score high (math, climate science,
philosophy). The two archetypal **mis-prioritizers** I built from documented critiques **do drop**:
**mainstream economics** (over-formalizes — loads Intuition/abstraction where the domain rewards
empirics) and **politics/governance** (under-prioritizes truth relative to power). The metric recovers
the intended contrast — encouraging, given it was *not* tuned to.

### 3.2 The robust echo of B73/B74
**Almost every discipline lands `under` 0.93 at the aggregate level, and NONE overshoot it.** Even
math and philosophy — built to overshoot *per-trait* (G,I ≈ 0.97) — fall under 0.93 in the *weighted
aggregate*, because low L,E drag the mean down. This independently reproduces the B73/B74 result (the
aggregate seldom reaches the cap) from an entirely different construction. Per-trait over-reach ≠
aggregate over-reach.

### 3.3 The #69 finding I refuse to tune away: the UOP penalizes LOVE
**Care-centered fields (social work 0.57, clinical medicine 0.74) score *low* — not because they are
bad, but because the UOP-optimal allocation, under B72 fragility costs, systematically DE-PRIORITIZES
Love (L).** L carries the highest fragility cost (c_L = 0.30) while Intuition is "free" (c_I = 0.00),
so the optimizer loads I and drops L as "existence-expensive." Fields that correctly invest in
relational alliance (L) therefore look "non-adherent" to a UOP that treats love as costly truth.

**This is a finding about the model, not the disciplines, and it cuts two ways (#69-symmetric):**
- *Bug reading:* L's fragility cost may be mis-specified; love-investment shouldn't be penalized as
  over-reach. The metric inherits B72's cost structure and should be flagged wherever L-heavy fields
  appear.
- *Feature reading:* it may be a genuine claim — that love **does** cost existence (it exposes,
  binds, makes fragile), and pure optimization sacrifices it — which is exactly the B64 Love-hybrid
  result (Love alone is valence-neutral; it only becomes high-valence *combined* with G/I). The UOP
  "punishing" solo-L may be the same structure as Love needing partners to pay its way.

Either way, the model **must not** be quietly re-tuned to push medicine/social-work up the leaderboard.
The anomaly is logged as an open question for the L fragility-cost calibration.

---

## 4. Status

- **No new principle.** Applied survey + visualization of UOP / GTT-1 / B72 / B74. Canonical count
  stays **74**; MR refinements 14; meta-collapses 41. Pass-77 papers 46→**47**. $0 spent.
- **Open hooks:** (1) replace actual-allocation archetypes with bibliometric/replication/survey data
  per field to make the survey empirical; (2) recalibrate L's fragility cost c_L and re-test whether
  the care-field penalty is artifact or genuine (ties to B64 Love-hybrids).

**Files:** `analyses/pass77_b75_uop_discipline_survey/run_b75.py` (+`results.json`, `fig1_J_shape_vs_truth.png`,
`fig2_survey_adherence.png`, `fig3_time_trajectories.png`, `fig4_truth_existence_tradeoff.png`); this
paper. Anchors: UOP/GTT-1 (#27), B72 (fragility costs), B74 (domain-matched cap), B64 (Love-hybrids),
urb_611 (domain profiles), ASYMMETRIC #69.
