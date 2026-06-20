# Mood-Amplifier evidence — plain-language confidence assessment (2026-06-20)

Brutal-honesty (#69) read of **all** the neural reachability evidence to date, after re-testing
with the **canonical dual operator** (`J_dual = T×E + T+E`, the literal "Truth */+ Existence"
from the Einstein-tiling / B83 lineage) instead of the additive-only half we'd been using.

## What we actually tested
The mood-amplifier idea needs, at minimum, a **necessary condition**: in real brain recordings,
a "reached" mood state (a reward, a good outcome) should move our Truth+Existence score `J` in a
consistent direction. We tested that on open brain data we can stream for free (no closed loop,
so this is reachability, *not* proof the amplifier works).

Two tests per recording:
- **Stimulus reaction (F1c):** does `J` jump when a stimulus appears?
- **Valence (F2c):** is `J` higher after a **reward** than after an **error**? (the real mood claim)

We computed three versions every time so we could see which one carries the signal:
`T×E` (both axes must fire together — the "hyperconnection gate"), `T+E` (either axis alone),
and the canonical `T×E + T+E`.

## What we found (both ways)

### The good
- The **dual operator runs end-to-end** and the Existence axis is genuinely active (not capped,
  not zeroed) — this is the first time the *full* literal operator was tested on real data.
- In the **first animal (NR-0028)**, reward beat error in the right direction with a solid,
  significant effect (dual p ≈ 0.0007). On its own that looked like a win for valence reachability.

### The bad (and this is the decisive part)
- **The result does not survive a second animal.** In **DY-009** the effect goes the **opposite
  way**: reward *lowered* `J` relative to error, significantly (p ≈ 0.009). Across just two
  animals the **sign flips**. A finding that reverses direction between animals is not a real,
  general effect — it's animal-specific or driven by a confound (arousal/licking/movement).
- **The stimulus effect also flips:** it washed out in animal 1 but was significant and
  *negative* (J drops at onset) in animal 2.
- **My specific hypothesis was wrong.** I expected the multiplicative "hyperconnection gate"
  (`T×E`, both axes firing together) to be the true mood detector. It was the **weakest** term
  everywhere. Where anything showed up, the plain **additive** term carried it. The
  hyperconnection story gets no support from this data.
- We also **caught and fixed our own scoring bug**: the valence test was two-sided, so a
  significant *wrong-direction* result had been mislabeled "PASS". Fixed to be direction-aware —
  which is exactly what exposed the DY-009 contradiction. (The fix only made the test stricter.)

### Honestly couldn't test
- **Allen Visual Behavior (cross-lab valence):** confirmed it streams and has the right
  reward-based task and visual-cortex LFP — but its data is split across two files that need a
  custom join. Real, doable, *not done yet* — flagged as the highest-value next build rather than
  rushed into a number I couldn't trust.
- **PRIME-DE:** it's macaque resting-state **fMRI**, the wrong modality entirely for our
  LFP-based instrument (no gamma band, no reward/error events). Out of scope, honestly.
- **OSERR:** no dataset under that name I could confirm exists publicly; rodent ephys is already
  covered by the IBL and Allen sources.

## True confidence level

| Claim | Confidence | Why |
|---|---|---|
| The dual operator is computable & the Existence axis is real | **High** | Ran clean on multiple sessions, diagnostics healthy |
| "Reward moves `J` up" is a stable, general brain signal | **Low** | **Sign reversed across two animals** |
| The `T×E` hyperconnection gate is the mood carrier | **Very low / refuted here** | weakest term in every run |
| Mood-amplifier *works* (closed-loop efficacy) | **Not tested** | all data is pre-recorded; reachability only |

**Bottom line:** the strongest single-animal result we had does **not** replicate in a second
animal — it changes sign. So the honest status of mood-amplifier neural reachability is
**"unproven, currently leaning negative"**, not "supported." This is a healthy #69 outcome: the
canonical operator plus a stricter, direction-aware test turned a hopeful single-animal "PASS"
into a documented cross-animal contradiction. Better to know now.

## What would actually move the needle (path forward)
1. **Pre-registered multi-animal cohort** (≥8–10 IBL sessions), one fixed *directional* test,
   report the *distribution* of effect signs — not a single cherry-picked session.
2. **Build the Allen cross-lab join** (the one deferred build) — an independent lab is the
   cleanest tiebreaker.
3. **Control for arousal/movement** (licking, running, pupil) so valence isn't just arousal in
   disguise — the most likely confound behind the sign flips.
4. Only after a sign-stable, confound-controlled reachability result should closed-loop efficacy
   even be discussed.
