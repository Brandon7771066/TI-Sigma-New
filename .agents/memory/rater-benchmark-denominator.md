---
name: Rater-benchmark fair denominator
description: When benchmarking truth-label representations/encoders on the gold rater corpus, count unencodable props as misses — never silently drop them.
---

When comparing PD/truth representations as encoders on the reused gold rater corpus
(`analyses/fleiss_binary_vs_5tier_*`), some representations cannot encode every label
(e.g. scalar/TIG have no NA codeword; 64D folds NA→MI). If a proposition's rater labels
are all unencodable under a rep, you must score it as an **explicit miss on the full N**,
NOT skip it.

**Why:** silently dropping unencodable props shrinks the denominator for the weak reps
and inflates their accuracy — in B108 it made the NA-blind reps look like 0.903 (on 413
rows) when the fair number on all 500 is 0.746. The architect code review caught this; it
flipped a headline claim ("64D is uniquely worst" → "64D ties the NA-blind floor 0.746").

**How to apply:** any apples-to-apples encoder benchmark must use one shared denominator;
mirror whatever the robustness Monte-Carlo does (it already counts unrepresentable draws as
misses). Cross-check: the accuracy gap between NA-blind and NA-holding reps should ≈ the NA
share of the gold set.

Related: when citing the urb_630 TECC error-correction weakness (B42), the quantity that
must clear the sin18°=0.309 threshold is the **correction radius (d_min/2 = 0.248)**, NOT
d_min itself (0.496). Stating "d_min 0.496 < 0.309" is a false inequality.
