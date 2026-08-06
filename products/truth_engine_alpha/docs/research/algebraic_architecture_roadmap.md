# Algebraic Architecture Roadmap

This roadmap documents a staged research sequence. Each stage is a proposed analytical representation, not an empirical claim about physical reality.

| Stage | Hypothesis | Representation | Baseline | Evaluation metric | Falsification condition | Status |
| --- | --- | --- | --- | --- | --- | --- |
| Ordinary scalar vector | Scalar features can establish a reproducible baseline. | Flat feature vector | Keyword baseline | classification accuracy / calibration | no gain over keyword rules | implemented |
| Graph-derived vector | Graph structure improves hallucination and contradiction detection. | Node/edge summary vector | ordinary scalar vector | accuracy / graph error recall | no gain over scalar baseline | proposed |
| Crystal tensor | Layered alignment exposes uncertainty and instability more directly. | Crystal matrix / tensor | graph-derived vector | diagnostic separation / error localization | no better localization than graph vector | proposed |
| GILE quaternion | Quaternion features may encode directional evidence relations. | Quaternion feature block | Crystal tensor | downstream accuracy lift | no improvement on held-out cases | proposed_theoretical_extension |
| Truth-axis quaternion | A truth-axis basis may separate support from contradiction pressure. | Quaternion axis projection | GILE quaternion | conflict discrimination | axis projection fails to isolate contradictions | proposed_theoretical_extension |
| HEM quaternion | A HEM-coded quaternion may expose structural uncertainty. | Quaternion feature block | truth-axis quaternion | uncertainty calibration | no gain in calibration | proposed_theoretical_extension |
| Eight-C octonion | Octonions may provide a larger structured basis for symbolic relations. | Octonion feature block | HEM quaternion | benchmark lift | no lift on held-out benchmarks | proposed_theoretical_extension |
| Truth Byte octonion | An octonion byte layer may compress claim relations. | Octonion byte representation | Eight-C octonion | compression fidelity | no fidelity gain | proposed_theoretical_extension |
| Existence Byte octonion | Existence-oriented octonion coding may improve criticality routing. | Octonion byte representation | Truth Byte octonion | action ranking quality | no ranking improvement | proposed_theoretical_extension |
| Myrion sedenion | Higher-dimensional sedenion coding may preserve more cross-layer context. | Sedenion feature block | Existence Byte octonion | held-out accuracy | instability or no gain | proposed_theoretical_extension |
| Qutrit simulation | A qutrit-like symbolic basis may support ternary confidence states. | Qutrit encoder | Myrion sedenion | ternary calibration | no benefit on ternary calibration | proposed_theoretical_extension |
| Qutrit hardware experiment | Hardware validation may test whether the ternary representation is useful. | qutrit hardware mapping | qutrit simulation | hardware-vs-simulation agreement | hardware diverges materially from simulation | proposed_theoretical_extension |

## Notes

- Every stage should reuse the same scalar feature values so that future tests can isolate algebraic benefit.
- No stage above should be presented as validated unless a held-out benchmark demonstrates a statistically meaningful gain.