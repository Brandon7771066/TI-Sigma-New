# Phase-1B re-test on the canonical HEM-GILE "Truth */+ Existence" (UOP J-score)

Per directive: **retire the legacy `M_r = L·E`** and re-run the Phase-1B reachability
tests on the canonical UOP J-score (identical operationalization to Phase-1A
`runner_v2.py:compute_J_window`):

```
Truth   G = mean gamma-PLV (30-80 Hz) across channel pairs, in [0,1], cap G*=0.93
Exist   H = theta / (theta + delta), in [0,1], no cap
T = f(G) = ln(1+G)  (G ≤ 0.93)  |  ln(1.93) − 10·(G−0.93)²  (G > 0.93)
E = g(H) = ln(1+H)

THE DUAL "*/+" OPERATOR (Truth */+ Existence; APERIODIC_DUAL / B83 Einstein-tiling):
  J_mult = T × E      # L×E HYPERCONNECTION gate — fires only when BOTH axes co-active
  J_add  = T + E      # L+E EXISTENCE — substitutable (legacy additive-only J)
  J_dual = T×E + T+E  # literal "*/+", the PRE-REGISTERED PRIMARY metric
```

> **Operator correction (this revision).** Earlier runs used `J = T + E` only — literally
> *half* the canonical operator. The corpus operator (`Reality = α(L×E) + β(L+E)`) is the
> **dual**: a multiplicative *hyperconnection* term (both axes required, zero in either kills
> it) **plus** the additive *existence* term. We now compute ΔJ for **all three modes** and
> pre-designate **dual** as primary. This directly tests the hypothesis that the multiplicative
> gate is the true detector of a *reached* mood state (reward co-activating gamma-coherence
> AND theta-arousal together).

Tested on the **same** anatomically-valid session `sub-NR-0028`, on its **neocortical**
probe channels (`Primary visual area`, 118 ch across layers) — chosen because the
Existence/theta term saturates in hippocampus, so cortex was needed to bring it online.
Exact event-locked segments; SAME pre-registered effect-size thresholds as the M_r runs.

> **Spectral-resolution fix (caught in code review).** An earlier version of this runner
> used Welch `nperseg = int(fs*0.5)` (Δf≈2 Hz), which **undersampled the 1–4 Hz delta band to
> exactly 0** and made `H≡1` look like a real "delta is high-passed out" degeneracy. That was
> a **measurement artifact**, not a property of the data. The runner now uses the **canonical
> `nperseg = int(fs*1.0)` (Δf≈1 Hz)**, identical to Phase-1A. At canonical resolution delta is
> large and **H is non-degenerate (≈0.30, full 0–0.97 range, 0 % ceiling)** — so this is the
> first run that actually exercises the FULL Truth+Existence instrument. The numbers below are
> the corrected run.

## Results — DUAL "*/+" operator, Existence axis genuinely active
Per-window means and the F-test verdict in **each of the three modes** (add / mult / dual).
J means are window-grand-means; F-verdicts are event-locked ΔJ.

| window | G (cap) | H (ceil) | J_dual (mult, add) | F1c stimulus (add / mult / **dual**) | F2c valence reward>error (add / mult / **dual**) |
|---|---|---|---|---|---|
| A (offset 10 s) | 0.525 (0%) | 0.330 (0%) | 0.802 (0.113, 0.689) | d=0.17 / d=−0.10 / **d=0.09** → all REFUTED/inconcl | p=0.080 / p=0.21 / **p=0.080**, n_err=**6** → **REFUTED (underpowered)** |
| B (offset 320 s) | 0.557 (0%) | 0.291 (0%) | 0.788 (0.107, 0.681) | d=0.12 / d=−0.14 / **d=0.05** → all REFUTED | **add PASS p=2.8e-4** / mult INCONCL p=0.010 / **dual PASS p=7.1e-4**, n_err=12 |

## Honest reading (#69 — both ways)
**Under the canonical dual `*/+` operator, valence (F2c) PASSES in the well-powered window**
(dual p=7.1×10⁻⁴, reward>error, 55 reward / 12 error). Window A points the same way but is
**underpowered** (6 error trials, p=0.08). So the canonical operator — not just the additive
half — supports valence/mood reachability when there are enough error trials.

**But the multiplicative hyperconnection gate is NOT the hero — and that refutes my own
hypothesis.** I expected `T×E` (both-axes co-activation) to be the sharpest valence detector.
The data say otherwise: in window B the **additive** term carries the signal (p=2.8e-4),
the **multiplicative** term alone is only *inconclusive* (p=0.010), and the **dual passes by
inheriting the additive component**. Empirically, reward vs error differ more in the *sum* of
truth+existence than in their *co-activation product*. This is a clean #69 result: the dual is
the right operator to use (and it passes), but the hyperconnection-gate story is **not**
supported here — the valence difference is a substitutable/existence-type effect, not a
both-required hyperconnection one.

**Bare stimulus-onset (F1c) does NOT survive any mode.** Truth-only runs PASSed it (M_r CA1
d=0.61/1.08), but with Existence active ΔJ at stimulus onset is d≈0.05–0.17 — REFUTED in dual
and mult, inconclusive at best in add. The mult term is even slightly *negative* (d≈−0.1):
co-activation does not rise at a bare sensory onset. So the stimulus effect was a Truth-axis
(gamma-coherence) phenomenon that the joint operator correctly declines to call a mood effect.

## What changed vs the earlier (Truth-only & additive-only) runs
- M_r / G-only runs PASSed **both** F1c and F2c, validating the **Truth axis only** (Existence
  was capped in CA1 or zeroed by the 2 Hz bug).
- The **additive-only** J (previous revision) already showed valence-PASS / stim-washes-out.
- The **dual `*/+`** (this revision) confirms valence-PASS as the *primary* verdict AND adds
  the diagnostic that the signal is additive-type, not hyperconnection-type. First IBL result
  that tests the literal Einstein-tiling dual operator end to end.

## Cross-animal replication — sub-DY-009 (DANDI 000409, a DIFFERENT animal)
Second IBL animal, also `Primary visual area` (58 ch), same dual `*/+` runner, same
pre-registered thresholds. **Verdict logic upgraded to be direction-aware** (see below).

| window | G | H | F1c stimulus (dual) | F2c valence (reward vs error), dual |
|---|---|---|---|---|
| A (offset 10 s) | 0.659 | 0.270 | **PASS d=−0.66** (significant, NEGATIVE sign) | rew dJ −0.264 < err +0.010, rb=−0.42, add p=8.8e-3 → **REFUTED_WRONG_SIGN (add) / INCONCLUSIVE (dual)** |
| B (offset 320 s) | 0.557 | 0.291 | **PASS d=−0.62** (significant, NEGATIVE sign) | n_err=6 underpowered → REFUTED |

**This is the decisive #69 result: the valence effect does NOT cross-replicate in sign.**
- In **NR-0028** reward raises J vs error (rb=+0.67, dual PASS).
- In **DY-009** reward *lowers* J vs error (rb=−0.42) — a **significant effect in the opposite
  direction** (add p=8.8e-3). The earlier "PASS" the two-sided test reported here was an
  artifact of not checking direction; corrected, it is **REFUTED_WRONG_SIGN**.
- Stimulus reaction also flips: washed-out (small +) in NR-0028, **significant but NEGATIVE**
  (J *drops* at onset, d≈−0.6) in DY-009.

So across just two animals the sign of both effects reverses. A single-animal "valence PASS"
is **not** a stable, animal-general result — it is at best animal-specific or confounded.

### Direction-aware verdict fix (correctness, not significance-chasing)
The pre-registered valence hypothesis is **directional** (reward should *raise* J). The verdict
function previously used a two-sided test, so a significant *wrong-direction* effect was
mislabeled PASS. Fixed: significant **and** reward>error → PASS; significant **and**
reward<error → **REFUTED_WRONG_SIGN**; p<0.05 → inconclusive; else REFUTED. This only made the
test *stricter* and is what surfaced the DY-009 contradiction.

## Other requested datasets — honest scoping (#69)
- **Allen Visual Behavior Neuropixels (DANDI 000713)** — *feasible, deferred as next build.*
  Confirmed: streams fine, has VISp LFP (e.g. probe-1158270877: VISp 24 ch, 12.7 M samples) and
  a real reward/hit/miss change-detection task → it *can* test valence cross-**lab**. BUT LFP
  lives in per-probe `_ecephys.nwb` files while reward/trial structure lives in a *separate*
  `_image.nwb`; they share Allen's master clock but must be **session-matched and joined** (a
  bespoke loader, not the IBL runner). Not forced into a rushed number here. *Allen Visual
  CODING (000021) is passive viewing → cannot test valence at all (no reward).*
- **PRIME-DE** — *wrong modality.* The public PRIME-DE release is overwhelmingly resting-state
  **fMRI (BOLD)** in macaque. This instrument is gamma-PLV + theta/delta on **LFP**; BOLD has no
  gamma band and no event-locked reward/error trials in the resting protocol. Testing here would
  require a completely different operationalization — honestly out of scope for the J-operator.
- **OSERR** — *no confirmed public dataset.* No match in the corpus and no standard public
  electrophysiology dataset under this name that streams like DANDI. Rodent ephys is already
  covered by IBL (000409) and Allen (000713); a specific OSERR DOI would be needed to proceed.

## Scope / limits (#69)
Pre-recorded ⇒ reachability necessary-condition ONLY (no closed-loop efficacy); valence
co-varies with licking/arousal ⇒ correlate, not pure code. **Cross-animal sign reversal (above)
is now the dominant limit**: the IBL valence "PASS" is animal-specific, not general. Do NOT
enlarge windows to chase significance; a pre-registered **multi-session cohort with a fixed
directional test** is the only correct way to settle it.

## Note on the M_r CA1 run
`runner_corrected.py` (committed M_r CA1 run) uses the same `nperseg=int(fs*0.5)`, so its
"E saturates at its cap (~100 %)" caveat is **plausibly the same undersampling artifact**
rather than genuine hippocampal theta dominance — unconfirmed, since the directive is to
retire M_r in favor of J. Flagged for honesty.

## Reproduce
```bash
python3 runner_gile_hem.py                                                   # cortex window A
RUN_TAG=win2 OFFSET_SEC=320 MAX_DURATION_SEC=300 python3 runner_gile_hem.py  # window B
# env: SESSION, TARGET_REGION, REGION_MATCH(exact|contains), OFFSET_SEC, MAX_DURATION_SEC, MAX_CHANNELS
```
