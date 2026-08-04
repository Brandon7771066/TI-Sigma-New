# Quaternion Block Specifications

Status: PROPOSED_THEORETICAL_EXTENSION

| block_id | semantic target | component map (w,x,y,z) | expected benefit | falsification condition |
| --- | --- | --- | --- | --- |
| gile_q_v1 | information gain latent encoding | completeness, contradiction_density, uncertainty, actionability | better prioritization stability | no lift versus scalar ordering |
| truth_axis_q_v1 | ternary truth tension | support_strength, contradiction_pressure, indeterminate_mass, calibration | better false/true separation | no AUROC lift on contradiction labeling |
| hem_q_v1 | heuristic evidence manifold | citation_support, source_concentration, conflict_density, resolution_potential | better uncertainty calibration | no calibration gain on held-out cases |

## Implementation Guidance

- Build features from existing analysis outputs only.
- Keep all outputs in research namespaces.
- Include explicit provenance for any derived threshold or ratio used in quaternion transforms.
