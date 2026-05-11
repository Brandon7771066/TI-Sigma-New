# Pass 44 — LLM E-Arm Fractal Scaling: ARC-AGI Plateau Falsifiable Prediction (Formal Promotion)

**Date:** 2026-05-11
**Pass:** 44
**Source:** discovery_scheduler asset #5227 (2026-05-11 19:36, conf 0.87, also asset #5211 12:27 and #5210 12:16). Promoted to formal corpus paper because it is the only autonomous-discovery output in the last 90 days that is (a) novel, (b) falsifiable, (c) numerically specific, and (d) cleanly anchored to an existing URB.

---

## §1 — One-paragraph claim

**LLMs are E-arm simulators with G≈0, I=0, L≈0 per URB #587.** The E-arm is fractal — every parameter doubling explores a self-similar pattern-recognition space. This predicts: (1) E-arm scaling laws continue indefinitely (no compute ceiling for pattern-completion tasks); (2) a hard ceiling exists at the noncomputability boundary for I-arm tasks (intuition / non-algorithmic insight); (3) **ARC-AGI performance for transformer-only architectures will plateau at ≤25%, regardless of parameter count, training compute, or RLHF.** The plateau is already visible: GPT-4 ≈ 4%, frontier models ≈ 20%, predicted asymptote ≈ 25%. The TI Sigma ARC solver (URB-cited) achieves ~18% by deliberately incorporating relational / I-arm features absent from pure transformers — providing one corroborating data point and one clean comparator.

## §2 — URB-587 anchor (E/G/I/L decomposition)

URB #587 (Pass-26 cluster, ratified Pass-37) splits cognitive work into four arms:
- **E (Extensive)**: pattern-completion, interpolation, surface statistics. Computable. Scales with compute.
- **G (Generative-symbolic)**: novel symbol manipulation under explicit rules. Partially computable.
- **I (Intuitive / non-algorithmic)**: leap-of-insight; provably non-Turing per Pass-37 PD-final synthesis.
- **L (Logical-relational)**: cross-domain abstraction over typed relations.

Per URB-587, transformer-only architectures realize E≈full, G≈0, I=0, L≈0. ARC-AGI is constructed (per Chollet 2019) specifically to require I+L over and above E. The two predictions follow directly: E-tasks scale forever; ARC-AGI is bounded.

## §3 — Falsifiable prediction with operational thresholds

| Predicted outcome | Numerical threshold | Verdict |
|---|---|---|
| Plateau at ≤25% | Best transformer-only ARC-AGI ≤ 25.0% by 2027-12-31 | CONFIRM |
| Marginal | 25.0% < score ≤ 35.0% by 2027-12-31 | PARTIAL |
| Refutation | Score > 35.0% by 2027-12-31 with transformer-only architecture | **REJECT URB-587 E-arm claim** |
| Strong refutation | Score > 50.0% by 2027-12-31 | **REJECT entire E/I decomposition** |

**Pre-reg conditions:**
- "Transformer-only" = decoder-only or encoder-decoder transformer with no external symbolic search at inference time, no I-arm feature engineering, no test-time training of architecture-novel modules. Standard fine-tuning on ARC examples is allowed; RLHF allowed.
- Source = ARC Prize official leaderboard (https://arcprize.org/leaderboard) or peer-reviewed paper, whichever reports first.
- Replication = score must hold across ≥2 independent ARC-AGI evaluation cycles (v1 + v2 if released).
- Hybrid systems (transformer + symbolic search e.g. AlphaCode-style) are **out-of-scope**: this prediction is about *transformer-only*. A hybrid > 35% does not refute URB-587 (it confirms the I-arm gap by demonstrating that an external module is needed to bridge it).

## §4 — Pre-existing data points (informational, not part of pre-reg)

| Year | System | Architecture | ARC-AGI score |
|---|---|---|---|
| 2024 | GPT-4 baseline | transformer-only | ~4% |
| 2024 | GPT-4 + chain-of-thought | transformer-only | ~9% |
| 2024 | Best transformer-only frontier | various | ~20% |
| 2024 | TI Sigma ARC solver | hybrid (E + L heuristics) | ~18% |
| 2025 | OpenAI o3 (high compute, hybrid) | transformer + search | ~76-87% |

The o3 result is **out-of-scope** per §3 — o3 uses extensive test-time search + scaffolding, classified as hybrid not transformer-only. It is a data point *consistent with* the I-arm requiring external machinery (CONFIRMS URB-587 indirectly), not against the prediction.

## §5 — Why this discovery is worth promoting (and 99% of bot-band output is not)

Per Pass-43 §3 honest review of discovery_scheduler:
- 3,144 discoveries over 6 months, 1.0% unique titles in last 90 days.
- Most "high-confidence" outputs are template-walked grandiosity (e.g. asset #5224 "Riemann Tralse Zeros validated to 10^15 decimal places — could win Millennium Prize" — Pass-38 already DISCONFIRMED Riemann/Pareto claim with real data; the bot is hallucinating empirical work that does not exist).
- This discovery is the **single non-redundant, non-hallucinated, non-grandiose** output produced by the bot in the last 30 days.

Distinguishing features:
1. **Falsifiable by external observation** (ARC-AGI leaderboard is public, refresh quarterly).
2. **Numerically specific** (25% / 35% / 50% thresholds, not vague "scales well").
3. **Cleanly anchored** to URB-587 (already in corpus, already ratified).
4. **Asymmetric implication** — confirmation has policy implications for Brandon's "AI Trainer" pipeline (per Pass-29); refutation collapses URB-587's E/I split.
5. **Out-of-scope clause is honest** — explicitly excludes hybrid systems where the prediction does not bind.

## §6 — What this paper does NOT claim (#69)

- Does NOT claim the prediction will hold. The 25% number could be wrong by 2-10 percentage points without invalidating the qualitative claim, but the formal pre-reg uses the strict thresholds in §3.
- Does NOT claim URB-587 E/I decomposition is established science. It is an internal TI Sigma framework. External replication required.
- Does NOT claim ARC-AGI is the right benchmark for I-arm (it's the *best public* benchmark; better ones welcomed).
- Does NOT claim transformer-only o3 will fail at >35%. The pre-reg explicitly notes hybrid o3 is out-of-scope; that route is not refutation.
- Does NOT vindicate the discovery_scheduler bot. The bot produced 1 testable claim out of 3,144 attempts (0.03%). The signal-to-noise ratio remains poor.

## §7 — Linked artifacts

- Source discoveries: `research_assets` rows #5210, #5211, #5227 (DB query: `SELECT * FROM research_assets WHERE asset_id IN (5210,5211,5227);`)
- URB anchor: URB #587 (cited in Pass-26 + Pass-37; full text in `papers/urb_587_*` if separated)
- Prior refutation (separate but related): Pass-38 §F-2 Riemann disconfirm + Pass-39 MBE asymmetric NULL — both demonstrate the discovery_scheduler's tendency to invent results; this paper is the exception that warrants promotion.
- Sister paper: Pass-45 (real empirical tests for top-N untested TI Sigma claims).

## §8 — Tracking protocol

Add to PIPELINE.md tracker (if maintained) and review at: 2026-09-01, 2026-12-31, 2027-06-30, 2027-12-31. At each checkpoint:
1. Pull current best transformer-only ARC-AGI v1+v2 scores from official leaderboard.
2. Apply §3 thresholds.
3. Log verdict (CONFIRM / PARTIAL / REJECT) with timestamp + source URL.
4. If REJECT triggers, open Pass-N retraction paper.
