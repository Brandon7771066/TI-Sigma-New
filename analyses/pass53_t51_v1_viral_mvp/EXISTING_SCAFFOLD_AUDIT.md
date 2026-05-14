# T51-V1 Existing Scaffold Audit (Pass-53 Step 1)

**Date:** 2026-05-14
**Status:** AUDIT COMPLETE
**Decision:** **EXTEND (not replace)** — build 6-pillar gpt-5 CLI layer as net-new complement to existing engine

---

## §1 — Existing files inventoried

| File | Lines | Purpose | Reuse decision |
|---|---|---|---|
| `biological_virality_engine.py` | 454 | R0/mutation/host-susceptibility epidemic model + acoustic resonance for concept spread; defines `TransmissionVector`, `HostSusceptibility`, `ConceptGenome`, `ViralMetrics`, `AcousticProperties` | **REUSE** — scoring backend for generated content |
| `viral_meme_generator.py` | 458 | Template-based meme generation (Drake, Distracted-BF, etc.) with caption gen + virality optimization via `BiologicalViralityEngine` + `gile_content_optimizer` | **REFERENCE** — its API patterns inform CLI design; not directly reused (template-meme ≠ 6-pillar prose) |
| `virality_machine_dashboard.py` | 1001 | Streamlit dashboard wrapping video creator, book generator, content optimizer, biological virology, acoustic resonance, analytics | **OUT OF V1 SCOPE** — V1 is CLI; Pass-54+ may add a tab here |
| `gile_content_optimizer.py` | (referenced; unaudited this turn) | GILE-score-based content optimization | **REUSE** — likely the scoring layer for the rubric |
| `acoustic_resonance_engine.py` | (referenced; unaudited) | Harmonic coupling model for concept resonance | Optional reuse |

## §2 — Gap analysis

**What exists:** Template-based meme generator with biological-virology scoring backend, accessed via streamlit dashboard.

**What Pass-51 §7 + `urb_783` specified for V1 MVP:**
- CLI tool: `viral_gen --topic X --platform Y`
- gpt-5-based 6-pillar prompt-template library (Hook / Frame / Payload / Bridge / Action / Tag)
- gpt-5-as-judge rubric scoring
- 5 candidate posts per invocation
- jsonl persistence
- 20-candidate manual-review pre-reg

**Gap:**
- No CLI entry point (everything is streamlit-routed)
- No gpt-5 6-pillar prompt library (existing system uses template-based generation, not prose-prompt)
- No gpt-5-as-judge rubric (existing scoring is algorithmic via `BiologicalViralityEngine`)

**Implication:** V1 is a **complementary** layer, not a replacement. The CLI calls gpt-5 for 6-pillar prose generation, then OPTIONALLY pipes the output to `BiologicalViralityEngine` for virology-scored evaluation.

## §3 — V1 architecture (Pass-53 build)

```
viral_gen_pass53.py        # CLI entry point: --topic, --platform, --n
    │
    ├─→ prompts/pillar_hook.txt        \
    ├─→ prompts/pillar_frame.txt        \
    ├─→ prompts/pillar_payload.txt       6-pillar gpt-5 prompt library
    ├─→ prompts/pillar_bridge.txt       /
    ├─→ prompts/pillar_action.txt      /
    ├─→ prompts/pillar_tag.txt        /
    │
    ├─→ ai_integrations.OpenAIIntegration         # gpt-5 generator
    ├─→ viral_judge_pass53.py                     # gpt-5-as-judge rubric scorer
    │
    └─→ viral_outputs/YYYY-MM-DD_topic.jsonl      # candidates + scores persisted

[OPTIONAL Pass-54+:]
    └─→ BiologicalViralityEngine.score()          # virology-backend cross-check
```

## §4 — Files NOT created (per audit-first principle)

- No new `viral_gen.py` at root (existing `viral_meme_generator.py` already there)
- No streamlit dashboard changes
- No modification of existing engine files

## §5 — Per-#69 honesty note

The existing scaffold is BIGGER and OLDER than the Pass-51 design assumed. The Pass-51 V1 spec did not account for `virality_machine_dashboard.py` already existing as a 1002-line streamlit integration. The decision to build the CLI/6-pillar layer as a NEW module (not modify the existing dashboard) is the conservative #69 move — it lets the existing dashboard keep working while adding the gpt-5 prose-pillar capability the design called for.
