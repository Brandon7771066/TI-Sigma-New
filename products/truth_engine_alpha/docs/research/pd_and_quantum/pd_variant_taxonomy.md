# PD Variant Taxonomy

This taxonomy defines a PD family rather than a single universal PD.

## Variant Matrix

| variant | input | output | range | semantics | threshold source | calibration method | current evidence | falsification condition | production status |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| PD-A (Classical continuous scalar) | claim or aggregate evidence features | scalar potential value | candidate [-3, 2] | graded state magnitude and evidence potential | pd_threshold_registry.csv historical profiles | supervised mapping against expert labels | ANECDOTAL to ARTIFACT_RECOVERED | no incremental calibration or action gain vs scalar baseline | RESEARCH_ONLY |
| PD-T (Ternary Real-Axis decoder) | PD-A scalar plus threshold profile | FALSE / INDETERMINATE / TRUE | categorical ternary | human-readable truth classification | threshold registry profile | threshold fitting on train only | ARTIFACT_RECOVERED | unstable boundaries on held-out data | RESEARCH_ONLY |
| PD-S (Soft ternary state) | PD-A scalar or direct probabilities | P(F), P(I), P(T) | simplex probabilities summing to 1 | boundary uncertainty and calibration | threshold set + decoder assumptions | Gaussian softmax or isotonic-style calibration | ARTIFACT_RECOVERED | poor calibration or invalid normalization | RESEARCH_ONLY |
| PD-G (Graph PD) | claim nodes, support/contradiction edges, paths | node_pd, edge_pd, path_pd, gradients | graph potential domain, candidate [-3,2] | propagation of support/contradiction tension | variant-specific graph threshold set | compare propagation families on held-out graphs | ANECDOTAL | no gain vs existing graph heuristics | RESEARCH_ONLY |
| PD-C (Crystal PD) | claim x layer matrix inputs | layer and global PD diagnostics | crystal-layer potential domain | multidimensional local/global instability state | crystal-specific threshold set | layer-wise calibration and divergence checks | ANECDOTAL | no gain vs existing crystal diagnostics | RESEARCH_ONLY |
| PD-Q (Quaternion block PD) | four axis summaries | quaternion-valued state | R^4 | compact directional summary of tension/uncertainty | inherited from parent scalar/soft variant | post-hoc fitting over held-out tasks | PROPOSED | no reproducible advantage over scalar or graph features | RESEARCH_ONLY |
| PD-O (Octonion PD) | eight axis summaries | octonion-valued state | R^8 | richer symbolic structure of relation space | inherited | post-hoc fitting with regularization | PROPOSED | no stable gain or lost interpretability | RESEARCH_ONLY |
| PD-M (Myrion/sedenion PD) | sixteen axis Truth-Existence summary | 16D state | R^16 | high-dimensional representation of cross-layer context | inherited and variant-specific | experimental, benchmark-separated | PROPOSED | instability, zero-divisor-like degeneracy, or no gain | RESEARCH_ONLY |

## Policy

- PD variants are non-equivalent hypotheses.
- Each variant can have its own threshold family.
- Graph PD and Crystal PD are allowed to use different ranges and threshold sets if measurement objects differ.
- No PD variant may alter production outputs until entry gates are satisfied.
