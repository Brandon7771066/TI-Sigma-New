# TI Sigma Architecture Dependency Graph

```mermaid
graph TD
    HEM["HEM (Footprint & Physical Mechanism)"] --> TL["Truth Label (5-Valued Taxonomy)"]
    TL --> GILE["GILE Values (Goodness, Intuition, Love, Elegance)"]
    GILE --> TA["Truth Axes (Real, Imaginary, Authority, Pragmatic)"]
    TA --> MR["Myrion Resolution (MI Screen & Epistemic Workflow)"]
    MR --> PD["PD Representation (PD_MINUS3_PLUS2 Shadow Mode)"]
    PD --> CG["Crystal Matrix & Claim Graph Network"]
    CG --> TE["Truth Engine Alpha 1.1 Applications"]

    subgraph Ratios ["Domain Calibration Ratios"]
        HGR["HEM:GILE Ratios (Strict HEM:GILE Order)"] -.-> HEM
        HGR -.-> GILE
    end
```

## Architectural Control Flow & Rules
1. **HEM:GILE Ordering**: Always written as `HEM:GILE` (Existence first).
2. **PD Shadow Isolation**: Potentiality Deficit (PD) runs in shadow-only mode without mutating primary Truth Engine evaluation output.
3. **5-Valued Label Taxonomy**: Primary classification layer evaluated before GILE vector calculation.
