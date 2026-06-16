---
name: Retrieval-operator benchmark — matched-feature control overturned "operators win"
description: Methodological lesson from the Retrieval-Gap benchmark; when comparing fancy operators vs a passive baseline, a matched-feature control is mandatory.
---

# Matched-feature control is decisive in operator benchmarks

When testing whether sophisticated retrieval/decoding operators beat a "passive"
baseline, the passive baseline MUST receive the same rich feature vector. A bare
resonance-magnitude scalar baseline makes every operator look great — but that gain
is almost entirely **feature richness, not mechanism**.

**Why:** In the Retrieval-Gap benchmark, operators (cross-attention, Hopfield,
reverse-osmosis, TI-Sigma Active Inference) all beat a scalar resonance baseline by
+0.3–0.5 balanced accuracy. Adding a nearest-centroid baseline on the SAME features
(P0b) collapsed that: P0b became the top method on both live DANDI mice, and NO
operator significantly beat it except TI-Sigma Active Inference on one hard
synthetic cross-frequency sim (sim7, +0.139). The flashy "operators dominate /
combination wins" first-pass conclusion was a confound.

**How to apply:** For any "does mechanism X beat baseline" claim, always include a
matched-input control and report paired deltas vs BOTH the weak and the matched
baseline. Also: cluster-as-latent targets must be fit on TRAIN ONLY (assign test by
nearest train centroid), and acausal filters (sosfiltfilt+hilbert) must be computed
per train/test block so no filter spans the split boundary — both bled in the first
pass and changed numbers.
