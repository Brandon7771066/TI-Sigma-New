# PD = (−3, 2) Perfect-Fifth — Falsifier Execution Results

**Date:** 2026-06-27
**Source paper:** `papers/PASS_47_PD_PERFECT_FIFTH_MUSICAL_ENTAILMENTS_2026-05-11.md`
**Script:** `analyses/pd_perfect_fifth_falsifiers/run_falsifiers.py` (predictions pre-registered in code)
**Data:** S&P 500 (`^GSPC`) daily, Yahoo Finance, no key — 14,242 trading days, 1970-01-02 → 2026-06-26.

## What was testable

Of the four pre-registered hypotheses, only **H-PD-MUSIC-4** (market upside/downside
asymmetry) has free public real data in this environment. **H-PD-MUSIC-1/2/3** require
Brandon's private autobiographical event-stream, his tagged decision log, and human-subject
music A/B ratings respectively — none available — so they are **not executable as designed**
and were not faked (a labelled no-effect base-rate null is included for #1 only).

## H-PD-MUSIC-4 — verdict: **KILL** (per the paper's own §2.4 falsifier: "ratio randomly distributed")

Prediction (frozen): in expansionary NBER regimes, ratio of cumulative positive-day
magnitude to cumulative negative-day magnitude lands in **(1.4, 1.6)** on ≥2 of 3
pre-registered expansions. Falsifier (§2.4): **ratio randomly distributed ⇒ KILL.**
(Note: the separate "outside (1.0, 2.0) ⇒ KILL" rule belongs to H-PD-MUSIC-**1** §2.1
only and is deliberately *not* applied here — a hypothesis-specific rule, no leakage.)

| Regime (NBER expansion) | n days | up/down ratio | total log-ret | in (1.4,1.6)? |
|---|---|---|---|---|
| 1982-11 → 1990-07 | 1938 | **1.156** | +0.985 | no |
| 1991-03 → 2001-03 | 2527 | **1.156** | +1.218 | no |
| 2009-06 → 2020-02 | 2687 | **1.155** | +1.255 | no |

Five other expansions: 1.06–1.19 (all below the band). Contractions (control): 0.67–1.05.

**Verdict (machine + narrative): KILL.** The perfect-fifth 3:2 ratio is absent — observed
≈ **1.155**, not 1.5 — confirmed on **0 of 3** primary regimes (and 0 of 8 expansions total).
The §2.4 KILL condition ("ratio randomly distributed") is met: the ratio is fully explained
by drift (corr = 0.978, below) and the data shows no concentration at 1.5 (base-rate = 0.000).

### Two controls that make the negative decisive
1. **Base-rate null** (20,000 random contiguous windows, matched length): fraction landing in
   (1.4, 1.6) = **0.000**. The S&P up/down magnitude ratio essentially *never* reaches 1.5 at
   this horizon (5/25/50/75/95th pctiles = 1.00 / 1.05 / 1.11 / 1.14 / 1.19). So 1.5 is not a
   value the data can produce here — the prediction was reachable-in-principle and missed.
2. **Resonance check:** corr(total period return, up/down ratio) = **0.978**. The ratio is
   almost perfectly a **relabelling of "the market rose"** — it carries no independent
   perfect-fifth information. Even had it landed near 1.5, that would be **resonance, not
   result** (mechanically forced by drift the framework did not predict).

## H-PD-MUSIC-1 (method-validation null only)
Symmetric no-effect ternary streams (P(pos)=P(neg)=0.4, 120 events): **4.4%** land in
(1.4, 1.6) by chance. Any future real run must beat this base rate to mean anything.

## Honest disposition (corpus convention)
- The falsifier **worked as designed** and returned an honest negative on its one runnable arm.
- Per convention, a falsifier outcome does **not** promote/delete a lead or change the
  canonical principle count (**79**).
- **PD's canonical (−3, 2) form is unaffected.** That form is a definitional/structural choice
  (the 3:2 / 4:3 interval *shape*), per Brandon's Pass-47 ruling; it never depended on these
  empirical event-distribution tests. What is weakened is only the *separate, downstream
  conjecture* that real-world positive/negative event distributions track the 3:2 ratio —
  weakened on markets, untested elsewhere.
- The Pass-47 "Riemann-connected" sub-clause remains demoted/open (unchanged).
