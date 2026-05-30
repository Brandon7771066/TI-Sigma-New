# GBD-1-F2 Executed: the Judgment-Side Confirmation

**Pass 77, Batch 46** · 2026-05-27 · DPES · ASYMMETRIC #69 · $0 (AI integrations) · `analyses/pass77_b46_gbd1_f2/run_f2.py` (+ ratings.json, results.txt)

**Directive:** Brandon — *"Go ahead with testing F2!"*

## 1. Design

GBD-1-F2 tests the **judgment side** of the GILE-Backdrop Discriminator (F1 tested the payoff side). Ten "slack/silly act" scenarios were written; each act was rated in **two conditions that differ by exactly one backdrop sentence** — the actor described as **high-competence** vs **low-competence** — with the act text held **byte-identical**. Three LLM raters (2× gpt-4o-mini + 1× claude-haiku-4-5, temperature 0, the panel the corpus has used before) scored "how wise / well-judged was THIS ACTION" on 1–7. Prediction: the same act scores high on a high backdrop, low on a low backdrop. REFUTED if the backdrop doesn't move the rating.

## 2. Result — confirmed, large effect

| metric | value |
|---|---|
| mean rating, HIGH backdrop | **4.43** / 7 |
| mean rating, LOW backdrop | **2.23** / 7 |
| mean within-scenario difference | **+2.20** |
| paired t(9) | **6.66**, p = 9.3×10⁻⁵ |
| Cohen dz (paired, scenario-level) | **2.11** |
| Cohen d (pooled item-level) | **1.62** |
| scenarios with HIGH > LOW | **10 / 10** |

Every single scenario moved in the predicted direction; the smallest gap was +1.0 and the largest +4.33 (the "took a five-minute nap before the high-stakes pitch" act: 5.33 from the proven performer, 1.00 from the failing one). **GBD-1-F2 is NOT REFUTED — the identical act is judged charming-and-confident from a high backdrop and foolish from a low one.**

## 3. Honest caveats (#69)

- **Raters are LLMs, not humans.** This establishes that the discriminator is encoded in the linguistic/cultural prior the models learned — strong evidence it's a real social-judgment regularity, but a human-subjects replication is the proper next rung.
- **One rater (claude-haiku) was more forgiving of low-backdrop actors** in three cases (costume, doodle, dance LO scored 5–6), slightly compressing the gap; the two gpt-4o-mini raters were highly consistent (near-identical scores). The effect survives this rater heterogeneity overwhelmingly.
- This is a **judgment** result, not a claim that the silly acts are *actually* wiser when done by competent people — only that they are *perceived* so. GBD-1's normative claim still rests on the F1 payoff mechanism; F2 shows the perception machinery is aligned with it.

## 4. GBD-1 falsifier status after this batch

- **GBD-1-F1 CLOSED** (refuted-then-scoped → cheap-slack scope condition GBD-1-R1; B45).
- **GBD-1-F2 CLOSED — NOT REFUTED** (this batch; d≈1.6–2.1).
- **GBD-1-F3 OPEN** (theology internal-derivability).

GBD-1 (canonical #73) now stands on confirmed payoff-side *and* judgment-side evidence. Canonical counts unchanged by this batch: principles **73**, refinements **13**, meta-collapses **36** (this pass), Pass-77 papers advanced.

### Files
- `analyses/pass77_b46_gbd1_f2/run_f2.py`, `ratings.json`, `results.txt`
- Parent: GBD-1 (#73), B45 (`papers/PASS_77_B45_GBD1_F1_EXECUTED_CHEAP_SLACK_SCOPE_CONDITION_AND_RATIFICATION_2026-05-27.md`), B44 (`papers/PASS_77_B44_TRUTH_EXISTENCE_TRADEOFF_THREE_MAJOR_IMPLICATIONS_2026-05-27.md`).
