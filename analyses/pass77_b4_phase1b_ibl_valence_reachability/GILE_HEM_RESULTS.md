# Phase-1B re-test on the canonical GILE-HEM "Truth */+ Existence" (UOP J-score)

Per directive: **retire the legacy `M_r = L·E`** and re-run the Phase-1B reachability
tests on the canonical UOP J-score (identical operationalization to Phase-1A
`runner_v2.py:compute_J_window`):

```
Truth   G = mean gamma-PLV (30-80 Hz) across channel pairs, in [0,1], cap G*=0.93
Exist   H = theta / (theta + delta), in [0,1], no cap
f(G) = ln(1+G)  (G ≤ 0.93)  |  ln(1.93) − 10·(G−0.93)²  (G > 0.93)
g(H) = ln(1+H)
J    = f(G) + g(H)        # the "*/+" UOP combination (additive at this layer)
```

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

## Results — FULL J-score, Existence axis genuinely active
| window | Truth G (cap-hit) | Exist H (ceiling) | F1c stimulus | F2c valence (reward vs error) |
|---|---|---|---|---|
| A (offset 10 s, 300 s) | 0.525 (0%) | 0.330 ± 0.234 (0%) | d=0.17, CI[−0.035,0.104] → **INCONCLUSIVE** | rew dJ 0.202 > err 0.006, p=0.085, ε²=0.071, rb=+0.47, **n_err=6** → **REFUTED (underpowered)** |
| B (offset 320 s, 300 s) | 0.557 (0%) | 0.291 ± 0.221 (0%) | d=0.12, CI[−0.027,0.088] → **REFUTED** | rew dJ 0.212 > err −0.055, p=2.8e-4, ε²=0.187, rb=+0.67, n_err=12 → **PASS** |

## Honest reading (#69 — both ways)
**Valence (F2c) is supported, but power-sensitive.** Reward > error with the **correct sign in
both windows**; the contrast is **significant with a moderate effect in the well-powered
window B** (ε²=0.187, p=2.8×10⁻⁴, 55 reward / 12 error). Window A points the same way but is
**underpowered** (only 6 error trials) and so misses the p<0.01 gate. Net: under the full
canonical Truth+Existence J-score, the valence/mood reachability signal replicates **when
there are enough error trials to test it**.

**Bare stimulus-onset (F1c) does NOT survive the full metric.** It was strong under the
Truth-only runs (M_r in CA1: d=0.61/1.08; J's `G`-term varies cleanly here too), but once the
Existence term `g(H)` is added, ΔJ at stimulus onset drops to d≈0.12–0.17 (inconclusive /
refuted in both windows). Interpretation (offered cautiously, not a claim): the
arousal/Existence term carries variance that is **not locked to a bare sensory onset**, so it
dilutes a Truth-axis-only effect — whereas it is at worst neutral, and plausibly consistent,
with the **arousal-laden reward-vs-error** contrast.

## What changed vs the earlier (Truth-only) runs
- M_r / G-only runs PASSed **both** F1c and F2c, because the Existence term was either capped
  (CA1) or — in the buggy 2 Hz version — zeroed. Those PASSes validated the **Truth axis only**.
- With the Existence axis now genuinely active, the **full** instrument supports **valence**
  reachability (power-permitting) but **not** bare stimulus reaction. This is the first
  result that actually tests "Truth vs Existence" jointly on IBL.

## Scope / limits (unchanged, #69)
Pre-recorded ⇒ reachability necessary-condition ONLY (no closed-loop efficacy); single
session ⇒ cross-animal DEFERRED; valence co-varies with licking/arousal ⇒ correlate, not pure
code. Window-A F2c is underpowered (6 error trials) — do NOT enlarge windows to chase
significance; a multi-session cohort is the correct way to settle it.

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
