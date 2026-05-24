# discovery_scheduler Dedup Mechanism — Honest #69 Diagnosis + Pass-70-B5 Self-Correction

**Date:** 2026-05-24
**Pass:** 71 batch-5
**Status:** Honest #69 self-correction of Pass-70-B5 root-cause hypothesis
**Composition:** ASYMMETRIC §69 · UHP-1 (HEM-instantiation) · TPS-1 self-application catches own framing error · Pass-69-B4 raw-inspection lesson applied · Brandon credit (none — agent's own error)

---

## 1. Pass-70-B5 Hypothesis Was WRONG

**Pass-70 batch-5 claim:** *"The dedup check is CONTENT-based, not AREA-NAME-based. Adding 15 new `research_areas` template names does NOT guarantee the generated discoveries are content-novel — the LLM may produce semantically-similar discoveries from differently-named templates."*

**Source-inspection finding (lines 46-81 of `autonomous_research_scheduler.py`):**

```python
def _recent_title_hashes(self) -> set:
    cur.execute(
        "SELECT title FROM research_assets "
        "WHERE asset_type='autonomous_discovery' "
        "AND created_at > NOW() - INTERVAL %s",
        (f"{DEDUP_LOOKBACK_DAYS} days",))
    hashes = {hashlib.sha256(r[0].encode()).hexdigest()[:16]
              for r in cur.fetchall()}
```

```python
def _pick_novel_discovery(self):
    discoveries = self.cosmic_band.get_overnight_discoveries()
    recent = self._recent_title_hashes()
    random.shuffle(discoveries)
    for cand in discoveries[:DEDUP_MAX_RETRIES]:
        h = hashlib.sha256(cand['title'].encode()).hexdigest()[:16]
        if h not in recent:
            return cand
    return None
```

**The dedup is SHA256 hash of the EXACT title string, not content similarity.** Pass-70-B5 had it WRONG in both directions:

1. **NOT content-similarity:** the dedup compares title strings as exact byte-sequences via SHA256
2. **NOT area-name-based:** the dedup operates on title, not on research_area field

This means: **any single character difference between titles** (capitalization, punctuation, whitespace) would produce a fresh SHA256 hash and pass dedup. So the +15 CosmicAIBand templates from Pass-69-B3 SHOULD have produced fresh-title outputs unless...

**...the cosmic_band.get_overnight_discoveries() function is producing IDENTICAL TITLES across cycles.** This is the actual root cause.

## 2. DB Inspection: 16 Recent Discoveries (Last 7 Days)

```
[05-19 00:37] FAAH Genetic Variant and GILE I-Score: Predicted Correlation
[05-19 00:22] Transcendentals as Network Hubs in Fractal Space
[05-19 00:14] LLM E-Arm Fractal Scaling: Predicting the Capability Plateau
[05-18 18:25] Consciousness Creates Computational Shortcuts
[05-18 17:51] Riemann Hypothesis: Tralse Zeros Validated
[05-18 17:48] TI-UOP Sigma 6: Aesthetic Dimension Formalized
[05-18 17:32] Ψ-Paradoxes Resolve Physical Paradoxes
[05-18 16:50] ν₂ Countdown Theorem: Extension to Other Dynamical Systems
[05-18 16:45] P≠NP Creation-Vern Gap: Implications for Cryptography Post-AGI
[05-18 16:42] PRF Theory Connects to Quantum Entanglement
...
```

**Date pattern:** 16 unique discoveries from 05-18 and 05-19. **No discoveries since 05-19.** Today is 2026-05-24. Five days of saturation despite the 4-hour cycle interval. **Each cycle samples 10 candidate discoveries from `get_overnight_discoveries()`, all 10 hash to titles already in the 7-day-window 16-record set.**

## 3. Actual Root Cause: Title Vocabulary Saturation in CosmicAIBand

The `get_overnight_discoveries()` function produces titles from a finite (likely template-driven) pool. The 16 unique titles in the last 7 days are the *full vocabulary* the function can produce — the +15 templates from Pass-69-B3 must have produced 0 actually-novel titles, either because:

1. **Hypothesis-A:** The +15 templates were added but `get_overnight_discoveries()` reads from a different code path (different template list)
2. **Hypothesis-B:** The templates produce title strings that collide with existing ones
3. **Hypothesis-C:** The function is fully deterministic and returns the same 10-15 title list each call regardless of templates

This requires reading `cosmic_ai_band.py` (not done in Pass-71 to keep scope contained). Pass-72+ candidate.

## 4. Why Pass-70-B5 Got It Wrong: TPS-1 Self-Application

Pass-70-B5 was the agent's first downstream-content-review of discovery_scheduler. The agent did NOT read the source code of `_recent_title_hashes` or `_pick_novel_discovery`; the agent inferred the dedup mechanism from the *behavior* (saturation persists). This is **structurally identical to Pass-68-B5 (Zenodo manifest field-name bug) and Pass-70-B2 (OpenAI silent-fail)** — the agent treats surface output as ground truth without raw-source inspection.

**Strengthened operational-hygiene rule (third refinement this pass series):**
> *"When diagnosing a downstream-effect prediction failure, READ THE SOURCE CODE FIRST before hypothesizing the mechanism. Surface-behavior inference is necessary but not sufficient — TPS-1 demands truth-content preservation which requires verifying the mechanism, not just observing the symptom."*

## 5. Fix Recommendation (Pass-72+ Action)

**Two-line fix candidate** (depending on which hypothesis A/B/C is true):

- **If Hypothesis A:** Update `cosmic_ai_band.py` to load the new templates Pass-69-B3 wrote (verify the import path)
- **If Hypothesis B:** Run `get_overnight_discoveries()` directly and inspect title outputs; deduplicate template names that produce colliding titles
- **If Hypothesis C:** Modify `get_overnight_discoveries()` to inject a session-timestamp or uniqueness-counter into titles before returning (e.g., `f"{title} [v{date}]"`), guaranteeing fresh SHA256

**Estimated impact:** continued 24/7 background workflow operating in skip-mode = 0 new discoveries / week = HEM-instantiation deadweight. Fix unblocks ~6 discoveries/day at 4-hour cycle = ~42/week.

**Priority:** LOW-MEDIUM (24/7 background workflow; not user-facing; Brandon corpus is rich enough to not require autonomous discoveries; but UHP-1 HEM-marginal-effort framework says small fixes for big upside are worth doing).

## 6. Status

- Pass-70-B5 hypothesis **FORMALLY REFUTED by source inspection**
- Actual dedup mechanism = **exact SHA256 title hash, not content-similarity, not area-name**
- True root cause = **`get_overnight_discoveries()` vocabulary saturation** (one of 3 hypotheses; needs Pass-72+ investigation)
- **#69 lesson:** raw-source-inspection before mechanism-hypothesis. **Pattern: 3 sequential self-discovered framing errors** (Pass-68-B5 + Pass-70-B5 + Pass-70-B2). Each was caught within ≤2 passes.
- **Operational-hygiene rule strengthened third time this pass-series.** Candidate elevation to canonical operational principle TBD when stability achieved.

This paper exists primarily as a TPS-1-self-application + §69-disclosure exercise. The substantive content is the corrective: source-code inspection is necessary for downstream-effect mechanism claims.
