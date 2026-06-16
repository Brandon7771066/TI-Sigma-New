---
name: Mood-Amplifier replication rigor (fair comparison discipline)
description: Two methodology traps that make a CH-vs-BASE decoding / closed-vs-open-loop comparison unfair; fix them before claiming a null or a feedback result.
---

# Fair-comparison discipline for the Consciousness-Hamiltonian Mood-Amplifier batches

When replicating the CH Mood-Amplifier batch onto a new modality (EEG → LFP →
hemodynamic fMRI/fNIRS → next), two non-obvious fairness bugs recur. Both were
caught in architect review of the hemodynamic (B117) port.

## 1. Leakage parity across feature sets
**Rule:** every per-window feature set you compare against BASE must obey the
SAME train/test split-boundary rule as BASE. BASE truncates train windows at the
split sample; the CH per-window extractor originally used full windows, so CH
train rows near the split peeked at post-split samples → asymmetric leakage that
silently favors CH.
**Why:** a "CH doesn't help" null (or a "CH helps" positive) is only credible if
CH was held to the same leakage constraint as BASE. Otherwise the comparison is
confounded.
**How to apply:** pass `split_sample` into the CH window extractor and truncate
train windows identically. Truncation produces very short boundary windows →
guard any `sosfiltfilt`/bandpass call (return zeros below ~12 samples, else
`padlen=n-1`) so it degrades gracefully like welch does, instead of crashing.
Tightening leakage can only weaken a CH advantage, so a pre-existing null gets
cleaner, never artificially rescued.

## 2. Equal-energy control matching must be per-run, not global
**Rule:** the "value of feedback" contrast (closed-loop vs open-loop) is only
valid if open-loop is matched to closed-loop ENERGY. A single global constant
calibrated from a few seeds does NOT match per-seed energy (saw 23.7 vs 20.1).
**Why:** "open-loop beats closed-loop" is only a statement about feedback if the
two used the same energy budget; otherwise it's an energy-confound.
**How to apply:** run closed-loop first per seed, capture its total energy, then
drive open-loop with a constant `u = energy/N_STEPS` so total energy matches
exactly. (Sham already matches by replaying the closed-loop |u| schedule.)

## Also
- The honest "feedback adds no value in a benign regime" finding is robust: even
  at exactly-equal energy open-loop still beats closed-loop. This reproduces the
  original LFP batch — modality-robust *including* the limitation.
- Writeup discipline: do not claim a loader capability that isn't implemented
  (e.g. local OpenNeuro NIFTI ingestion) — describe only what the code does
  (DANDI NWB streaming), label the rest a future leg.
