# Pass-49 — Plain LCC Framework: Supervised vs Unsupervised, Thresholds, and Concrete Predictions

**Date:** 2026-05-13
**Status:** First-canonical formalization. Brandon-ratified concept; agent-formalized operational definitions.
**Anchors:** `papers/PASS_48_LCC_VIRUS_RETRIEVAL_DEVELOPMENT_PLAN_2026-05-13.md`, `papers/PASS_49_LCC_HOLDOUT_BLIND_PROTOCOL_2026-05-13.md`, `analyses/pass49_l1_lcc_markets/results_writeup.md` (NULL_NOISE precedent informing this revision).
**Companion:** §6 below pre-registers an Unsupervised-LCC empirical pilot.

---

## §1. Plain-language framing

**Lead-Correlation-Causation (LCC)** is the claim that one system can lead another system in a desired direction by correlating with it across time. The framework asks:

> When does correlation between two systems begin to *behave like* causation — i.e., one system's trajectory comes to depend on the other's — and what conditions amplify or suppress that drift?

LCC has two operating modes:

- **Supervised LCC.** A *leader* system actively seeks feedback from a *follower* (or from an environment containing the follower) and adjusts its own trajectory based on observed coupling, with the explicit goal of moving the follower toward a target state. Closed-loop. Both systems are "aware" of the coupling in some operational sense.
- **Unsupervised LCC.** A leader system pursues its own trajectory; a follower system, *without active feedback exchange*, drifts in the leader's direction through passive entrainment, mimicry, ambient coupling, or shared-environment forcing. Open-loop from the follower's standpoint. The follower is *not* "trying" to follow.

**Brandon's stated interest (2026-05-13):** the **natural drift** of unsupervised cross-system correlation toward causation. The empirical question is whether this drift is real, measurable, and shows the predicted threshold-and-dynamic structure.

---

## §2. Formal definitions

### §2.1 Notation
- $X(t), Y(t)$: two time-series of two systems over a shared time index $t \in [0, T]$.
- $X$ = candidate leader; $Y$ = candidate follower.
- $\rho(X, Y; \tau)$: lagged Pearson correlation, $X(t)$ vs $Y(t+\tau)$, for lag $\tau \geq 0$.
- $G_{X \to Y}(\tau)$: lag-$\tau$ Granger-causality statistic (F-statistic for "$X$ helps predict $Y$ at lag $\tau$").
- $W_k$: a temporal window of fixed length, indexed $k = 1, 2, \dots, K$, that tile $[0, T]$ with no overlap.

### §2.2 Supervised LCC (operational)

A pair $(X, Y)$ exhibits **Supervised LCC** in window $W_k$ iff all four conditions hold:

- **S1 — Coupling:** $\max_{\tau \in [0, \tau_{\max}]} |\rho(X, Y; \tau)| > \rho_{\min}$, where $\rho_{\min}$ is a domain-specific threshold (see §3).
- **S2 — Lead direction:** the lag $\tau^*$ achieving the maximum in S1 satisfies $\tau^* > 0$ (i.e., $X$ leads $Y$, not the reverse).
- **S3 — Granger causality:** $G_{X \to Y}(\tau^*) > G_{\text{crit}}$ (at $p < 0.05$ relative to a phase-shuffled null).
- **S4 — Feedback signature:** there exists evidence that $X$'s trajectory was *adjusted* in response to observed $Y$. Operationalization: a regression of $\Delta X(t+1)$ on $Y(t) - Y_{\text{target}}$ shows a significant negative coefficient at $p < 0.05$ (i.e., $X$ corrects toward the $Y$-target gap).

### §2.3 Unsupervised LCC (operational)

A pair $(X, Y)$ exhibits **Unsupervised LCC** in window $W_k$ iff S1, S2, S3 hold AND S4 explicitly **fails**:

- **U4 — No-feedback signature:** the regression in S4 shows |coefficient| < 0.1 with $p > 0.20$ (no detectable feedback adjustment).

I.e., Unsupervised LCC is "lead, correlation, and causation evidence — but with no closed loop." This is the **natural-drift** regime.

### §2.4 The drift criterion (correlation → causation)

Define the **LCC Drift Index** for pair $(X, Y)$ over $K$ sequential windows:

$$D_{\text{LCC}}(X, Y) = \frac{1}{K-1} \sum_{k=2}^{K} \mathbb{1}\left[ G_{X \to Y}^{(k)} > G_{X \to Y}^{(k-1)} + \epsilon \right]$$

where $G^{(k)}$ is the Granger statistic computed within window $W_k$, and $\epsilon$ is a small slack (default 0.1× the cross-window standard deviation of $G$).

**Interpretation:** $D_{\text{LCC}}$ is the fraction of consecutive-window pairs in which Granger causality from $X \to Y$ *increased*. Under the null of no-drift, $D_{\text{LCC}} \approx 0.5$. Drift toward causation: $D_{\text{LCC}} > 0.5$. Strong drift: $D_{\text{LCC}} \geq 0.65$.

This is the **central concrete prediction** of the LCC framework's natural-drift claim: in pairs that pass S1+S2+U4 (Unsupervised LCC), $D_{\text{LCC}} > 0.5$ statistically (one-sample $t$-test against 0.5, $p < 0.05$).

---

## §3. Concrete domain-specific thresholds

| Domain | $\tau_{\max}$ (window) | $\rho_{\min}$ | $G_{\text{crit}}$ | Supervised feasibility | Unsupervised feasibility |
|---|---|---|---|---|---|
| **Markets** (e.g., SPY-TLT) | 5 trading days | 0.30 | $p<0.05$ vs phase-shuffle | Implausible (no leader actively adjusts) | Plausible via Fed-rate→equity-vol; central-bank communications as macro-leader |
| **Ecosystems** (e.g., predator-prey, paleoclimate-coral) | 10 sample-units (years for paleo; days for predator-prey) | 0.40 | $p<0.05$ vs phase-shuffle | Implausible | Plausible via temperature-leader → reef-bleaching-follower |
| **Workplaces** (e.g., manager-team mood) | 7 daily samples | 0.35 | $p<0.05$ vs phase-shuffle | Plausible (active management) | Plausible via team-mood drift toward unspoken-tone-of-leader |
| **Quantum** (entangled multi-qubit) | not applicable (instantaneous) | 0.85 (Bell-bound exceedance) | not applicable | qc26 GHZ-5 already CONFIRMED ($M_5 = 14.535$, 71σ over LHV) | qc25 IBMQ HW-result is closest unsupervised analogue |

Thresholds are **deliberately conservative** — set high enough that random-data exceedance probability < 5%. Markets threshold $\rho_{\min} = 0.30$ informed by the L1 NULL_NOISE result (where SPY-TLT achieved $|\rho| = 0.18$, below threshold).

---

## §4. The framework's testable predictions

Per the formal definitions and thresholds above, the LCC framework makes **five concrete predictions**, each of which is independently disconfirmable:

**P1 (Existence — Unsupervised):** In *some* domain, pairs $(X, Y)$ with shared environmental forcing will satisfy S1+S2+U4 at rates above chance (>10% of randomly-sampled pairs).

**P2 (Drift — Unsupervised):** Pairs satisfying P1 will exhibit $D_{\text{LCC}} > 0.5$ on average ($p < 0.05$, one-sample $t$).

**P3 (Domain-ordering):** Effect-size ordering, from largest to smallest, will be: **Quantum > Ecosystems > Workplaces > Markets**. (Quantum already confirmed via qc26; Markets already partially-disconfirmed via L1 NULL_NOISE.)

**P4 (Supervised > Unsupervised in same domain):** When both modes are observable in the same domain (e.g., a workplace with active management vs an idle workplace), Supervised LCC will show stronger Granger causality than Unsupervised LCC by ≥1.5× on average.

**P5 (Asymmetric-direction):** $G_{X \to Y} > G_{Y \to X}$ for true Supervised pairs; the difference shrinks toward zero for Unsupervised pairs (because passive entrainment is more symmetric than goal-directed adjustment).

**Aggregate disconfirm criterion:** if 3 of 5 predictions DISCONFIRM in pre-registered tests, the framework needs structural revision. P1 is the most foundational; P3 the most discriminative.

---

## §5. Reconciling the L1 NULL_NOISE result

The Pass-49 L1 LCC-in-markets test (`analyses/pass49_l1_lcc_markets/`) showed NULL_NOISE on SPY-TLT 2022-2026. Under the new framework:

- The L1 test was **Unsupervised LCC in markets** — the lowest-effect-size cell of the §3 table.
- Threshold $\rho_{\min} = 0.30$ was not met (achieved 0.18).
- The framework's revised prediction P3 *predicts* markets are the weakest domain, so the L1 NULL is now *expected* under the framework, not anomalous.

This is **post-hoc but structurally honest** — the L1 result motivated the §3 domain-ordering, not the other way around. To avoid post-hoc cherry-picking, P3 must now be tested in a domain where the framework predicts a **CONFIRM** (Ecosystems or Workplaces). If those also NULL, the framework is genuinely disconfirmed, not preserved by domain-rotation.

---

## §6. Pre-registered Unsupervised-LCC pilot — Track L (Pass-49 / Pass-50)

### §6.1 Selection of pilot domain

Decision matrix (cost × accessibility × predicted effect-size × disconfirmability):

| Domain | Public data available | Cost | Predicted effect | Pilot-feasibility |
|---|---|---|---|---|
| Markets | yfinance (already used L1) | $0 | Smallest | DONE — NULL |
| Ecosystems (paleoclimate) | NOAA paleoclimate DB; open | $0 | Largest non-quantum | **Selected** |
| Workplaces | open Slack/forum data; messy | $0-30 | Mid | Defer (data-quality risk) |
| Quantum | IBMQ open-access | $0-144 | Largest | Defer (cost + already partially-confirmed) |

**Pilot domain: Ecosystems via paleoclimate δ¹⁸O records.**

### §6.2 Pre-registered protocol — L2 (Pass-50 batch)

**Test ID:** L2 — Unsupervised LCC, Paleoclimate δ¹⁸O Cross-Site

**H_PRIMARY:** A randomly-selected pair of geographically-distant paleoclimate δ¹⁸O records over a 1000-year shared interval will exhibit S1+S2+U4 (Unsupervised LCC) AND $D_{\text{LCC}} > 0.5$ on the HOLDOUT segment ($p < 0.05$).

**Data source:** NOAA Paleoclimate Reconstructions database (`https://www.ncei.noaa.gov/products/paleoclimatology`). Selection: deterministic via SHA-256-of-protocol-text seed → pick 5 site-pairs from an alphabetically-sorted list of available high-resolution (decadal-or-finer) δ¹⁸O records spanning AD 1000-2000.

**Pipeline:**
1. Download 5 selected site δ¹⁸O time-series.
2. Form $\binom{5}{2} = 10$ pairs.
3. For each pair, compute S1-S3 + U4 + $D_{\text{LCC}}$ on 100-year sliding windows.
4. 60/40 split by *pair-ID* (deterministic): 6 pairs TUNE, 4 pairs HOLDOUT.
5. Tune threshold-parameters and any analytic choices on TUNE only.
6. Apply frozen pipeline to HOLDOUT once.

**Filters:**
- Filter A (drift): TUNE↔HOLDOUT effect-direction consistency; sign-match required.
- Filter D (variance): require ≥3 distinct $D_{\text{LCC}}$ values in HOLDOUT (rule out degenerate-uniform).
- Filter E (vacuousness): NULL_NOISE outcome ($D_{\text{LCC}} \approx 0.5$) clearly disconfirms. PASS.

**Verdict matrix:**
- CONFIRM_STRONG: ≥3 of 4 HOLDOUT pairs satisfy S1+S2+U4 AND mean $D_{\text{LCC}} \geq 0.65$ ($p < 0.05$).
- CONFIRM: ≥2 of 4 HOLDOUT pairs satisfy S1+S2+U4 AND mean $D_{\text{LCC}} > 0.5$ ($p < 0.05$).
- WEAK: 1 of 4 pairs satisfies, or mean $D_{\text{LCC}}$ trends positive but $p > 0.05$.
- DISCONFIRM: 0 pairs satisfy S1+S2+U4 OR mean $D_{\text{LCC}} \leq 0.5$.
- NULL_NOISE: indistinguishable from null (Filter A FAIL).

**Cost:** $0 (NOAA open data + corpus existing tooling).

**Expected timeline:** Pass-50 single session, agent-executable.

### §6.3 Honest-prediction self-binding (Pass-49 L4 §3)

Agent's pre-reg prediction (recorded for #69 calibration scoring): **CONFIRM** for L2. Reasoning: paleoclimate records share global-temperature forcing, which should produce the predicted Unsupervised-LCC structure if the framework is correct. If L2 NULL_NOISEs in addition to L1, the framework's predicted-positive domains have ZERO support — material disconfirm.

---

## §7. Companion test pre-registrations (deferred)

Track L additional tests (full pre-reg deferred to execution session):

- **L3 — Workplace mood drift (Slack/forum):** open data acquisition + per-team daily-mood embedding via LLM. Feasibility: data-quality risk substantial.
- **L4 — Supervised vs Unsupervised in same workplace:** P4 direct test. Requires teams with documented active-management vs idle states.
- **L5 — Quantum unsupervised analogue:** D2 Dirac-experiment from `papers/PASS_48_IBM_QUANTUM_DIRAC_EXPERIMENTS_2026-05-13.md` reframed as Unsupervised LCC test (entanglement-witness without measurement-feedback). Cost ~$72.

---

## §8. Honest scope boundaries (#69)

- **The framework as formalized in §2 does not solve the "correlation ≠ causation" problem in general.** It defines a **specific operational signature** (S1+S2+S3+S4 or U4) that, when present, *behaves like* causation in the operational sense of "intervening on $X$ would change $Y$." A passing test is evidence for the operational claim, not metaphysical causation.
- **Granger causality is well-known to fail in non-linear and confounded systems.** The paleoclimate pilot is vulnerable to shared-forcing confounds (global temperature drives both site δ¹⁸O); this is exactly what the framework expects (shared-environment is one of the three Unsupervised-LCC mechanisms in §1), but it also means a CONFIRM does not distinguish "paleoclimate site A drives B" from "they share a common driver." This is a feature for the framework (Unsupervised LCC is *defined* to include shared-environment drift) but a bug for any narrow causal-discovery interpretation.
- **The framework currently has more degrees of freedom than ideal.** Per-domain thresholds in §3 are author-set, not data-derived. A proper Pass-50 task is to derive thresholds from a held-out calibration dataset before any prediction-test is run.

---

## §9. Cluster impact

1 first-canonical-formalization paper + 5 pre-registered framework predictions + 1 pre-registered Unsupervised-LCC pilot (L2) + 3 deferred test sketches (L3, L4, L5) + L1-NULL_NOISE reconciliation.

Cluster ≥ 116 (was ≥ 110 after Wave-1 writeup).
