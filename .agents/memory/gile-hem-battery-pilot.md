---
name: GILE+HEM rater-battery pilot (B190)
description: First rater-based validation battery on GILE + HEM dimensions — results, gates for scale-up, and rails for any re-run.
---

# GILE + HEM dimensions through the truth-label battery (61-prop pilot, QUALIFIED)

Anchor: `papers/PASS_77_B190_GILE_HEM_DIMENSIONS_TRUTH_LABEL_BATTERY_PILOT_FLEISS_MI_SPECTRUM_EXHAUSTION_2026-07-06.md`; code `analyses/pass77_gile_hem_battery_pilot/` (reuses B125's frozen 61 props, thresholds, metric code).

**The battery** = Fleiss κ (reliability) + MI/unique-variance (own-information) + spectrum coverage/exhaustion (extra-axis unique-variance probe). This is the "spectrum exhaustion" sense (user-defined) — the D3-spectral-purity reading is withdrawn.

## Durable results / rails
- **First rater-based battery ever on either pillar** (prior GILE = algorithmic-only; prior HEM = plan only). Both pillars **QUALIFIED**, not confirmed.
- **LLM-rater parsing must be strict:** require the full reply to be exactly the expected score tokens (full-string match) and log raw replies; lenient "grab first N digits anywhere" parsing silently mis-parses noncompliant outputs. A hardened re-run showed only small drift here, but always use strict parse + raw-response log for audit-grade batteries.
- **Reliability is the failing leg:** only G clears κ≥0.40 (0.529 in the canonical strict-parse run); other 7 dims 0.18–0.35 vs labels' 0.886–0.906. Do NOT scale to the 1,000-prop set before gates pass: S1 rubric-anchored re-pilot median κ≥0.40; S2 HEM-tailored item set (61 props are truth-designed, may under-span HEM); S3 decide if ~4 effective dims is acceptable.
- **PCA effective rank ≈4.1 of 8** — the 4+4 architecture spans ~4 perceived dims; I/D1/D2/D3 fail cross-pillar unique-variance.
- **Pre-reg E↔D3 r≈0.01** ⇒ the B116 GILE-E==HEM-D3 identity is **operational-only** (no abstract-space echo; scope-narrowing, not refutation — never cite the identity as perceptual).
- **G, not I, is the top verdict-informer** (0.612 vs 0.367 b); canonical-weight GILE composite (0.412 b) < G alone — another instance of aggregation losing signal.
- Exhaustion probe found **no gap** (persistence 0.265 / usefulness 0.195 ≪ 0.50).
- Falsifiers GHB-F1/F2/F3 OPEN. Empirical only — count stays 81.

**Why:** prevents re-running the battery blind at scale, mis-citing B116 as perceptual, or re-guessing "spectrum exhaustion."
**How to apply:** any GILE/HEM measurement, scale-up, or battery re-run must start from the S1–S3 gates and the DV1–DV4 deviations.
