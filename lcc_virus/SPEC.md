# LCC Virus 6-Step Algorithm — Formal Pseudocode Specification

**Version:** 1.0 (Pass-49 L-3 deliverable, 2026-05-13)
**Replaces:** prose specification in `papers/LCC_VIRUS_WORKED_EXAMPLE.md`
**Status:** Reference specification for `lcc_virus` package
**Anchors:** `papers/LCC_VIRUS_WORKED_EXAMPLE.md`, `papers/LCC_VIRUS_METHODOLOGY_AUDIT.md`,
`papers/LCC_BIDIRECTIONAL_VALIDATION_AND_BOK_VIRUS_EXPERIMENTS.md` §1.3,
`papers/PASS_48_LCC_VIRUS_RETRIEVAL_DEVELOPMENT_PLAN_2026-05-13.md` Track B L-3

---

## 0. Notation

| Symbol | Meaning |
|---|---|
| `S = (S_1, ..., S_K)` | multivariate substrate; each `S_k: [0..N) → ℝ` is a real-valued time series of length N |
| `Φ_T` | target i-cell template (deterministic function) |
| `R(A, B)` | Gaussian-weighted lagged cross-correlation, σ = 5, max lag ±10 |
| `θ_R` | resonance threshold; default 0.6 (NOT C_EMERICK; see §6) |
| `θ_T` | termination threshold; default 0.6 |
| `H` | hop budget (max EXPAND iterations); default 5 |
| `proj(A, B)` | least-squares projection of A onto B over windowed dot product |
| `resid(A, B)` | A − proj(A, B) |
| `i-cell` | a (template, label) pair that the algorithm has resonance-confirmed against `S` |

---

## 1. Inputs and Outputs

```
INPUT:
  S        : multivariate substrate (K series x N samples)
  T        : seed i-cell — pair (Φ_T, label_T)
  Φ        : function library (set of candidate templates)
  θ_R      : resonance threshold (default 0.6)
  θ_T      : termination threshold (default 0.6)
  H        : hop budget (default 5)

OUTPUT:
  Discovered    : list of i-cells [(Φ_i, label_i, R_i, parent_i, hop_i)]
  Provenance    : DAG of which i-cell triggered discovery of which next i-cell
  Termination   : reason ∈ {"hop_budget", "no_residual_signal", "all_below_threshold"}
```

---

## 2. Step 1 — SEED

```
function SEED(T):
    require T = (Φ_T, label_T), Φ_T callable, returns ℝ-valued template aligned to S
    Discovered ← [(Φ_T, label_T, R = NA, parent = NULL, hop = 0)]
    Frontier   ← [Discovered[0]]
    return Discovered, Frontier
```

---

## 3. Step 2 — RESONATE

```
function RESONATE(S, Φ_T, θ_R):
    R_per_channel ← empty dict
    for k in 1..K:
        R_per_channel[k] ← R(S_k, Φ_T)        # Gaussian-weighted lagged xcorr
    Resonant ← { k : |R_per_channel[k]| ≥ θ_R }
    R_max   ← max(|R_per_channel[k]|) over k
    return R_per_channel, Resonant, R_max

postcondition:
    if Resonant is empty AND R_max < θ_R:
        skip to TERMINATE with reason = "below_threshold_at_seed"
```

---

## 4. Step 3 — LISTEN

```
function LISTEN(S, Resonant, Φ_T):
    Residuals ← empty dict
    for k in Resonant:
        # Project the resonant channel onto the target template, subtract.
        # The "noise" is the part of S_k that survives this projection.
        Residuals[k] ← resid(S_k, Φ_T)
    return Residuals
```

The methodology audit (`LCC_VIRUS_METHODOLOGY_AUDIT.md`) flagged steps 3-5
as previously unimplemented in production code. This pseudocode is the
canonical reference for the implementation in `lcc_virus.core`
(Pass-50 milestone).

---

## 5. Step 4 — PROPAGATE

```
function PROPAGATE(Residuals, Φ, θ_R):
    Candidates ← empty list
    for (Φ_c, label_c) in Φ:
        # Score candidate template against the residual stack — if
        # its resonance with the post-target noise is high, the noise
        # contains an i-cell signature for Φ_c.
        R_c ← mean over k of R(Residuals[k], Φ_c)
        if |R_c| ≥ θ_R:
            Candidates.append((Φ_c, label_c, R_c))
    sort Candidates by |R_c| descending
    return Candidates
```

---

## 6. Step 5 — EXPAND

```
function EXPAND(S, Discovered, Frontier, Φ, θ_R, H):
    while Frontier is non-empty AND len(Discovered) hops < H:
        node ← Frontier.pop_front()
        if node.hop ≥ H:
            continue
        Residuals ← LISTEN(S, node.Resonant, node.Φ)
        Candidates ← PROPAGATE(Residuals, Φ, θ_R)
        for (Φ_c, label_c, R_c) in Candidates:
            if label_c not in {d.label for d in Discovered}:
                child ← (Φ_c, label_c, R_c, parent=node, hop=node.hop+1)
                Discovered.append(child)
                Frontier.append(child)
    return Discovered
```

---

## 7. Step 6 — TERMINATE

```
function TERMINATE(Discovered, Φ, θ_T, H):
    if Discovered[-1].hop ≥ H:
        return "hop_budget"
    if all newest candidates had |R_c| < θ_T:
        return "all_below_threshold"
    return "no_residual_signal"
```

---

## 8. Resonance threshold vs C_EMERICK threshold — disambiguation

`θ_R = 0.6` is the **per-step LCC-Virus internal resonance threshold**
(template ↔ data acceptance gate). It is NOT the same as
`C_EMERICK ≈ 0.4370 = 1/(φ√2)`, which is the **bidirectional-LCC
phenomenological threshold** at which (per the conjecture, not yet
derived from first principles — see Pass-48 architect CRITICAL flag)
ordinary cross-correlation transitions to genuine bidirectional
coupling.

Per the 2026-05-13 update to `PASS_48_LCC_VIRUS_RETRIEVAL_DEVELOPMENT_PLAN`,
the closed form `1/(φ√2)` is a **CONJECTURAL FIT** pending Track-C M5
first-principles derivation. External-facing documents should cite the
empirical value 0.4370 ± 95% CI, not the closed form.

The two thresholds are independent:
- θ_R is a tuning knob for the Virus retrieval algorithm.
- C_EMERICK is an empirical claim about a regime-transition in coupled-
  systems analysis (Programs A-C target).

---

## 9. Honest scope (#69)

This pseudocode formalizes the Virus algorithm; it does NOT validate it.
Until M4 (independent replication of M1 finding per
`PASS_48_LCC_VIRUS_RETRIEVAL_DEVELOPMENT_PLAN` §4), all output of the
Virus on real data should be treated as exploratory, not confirmatory.

The pseudocode also does NOT solve the open theoretical question of
WHY noise residuals after LISTEN should carry recoverable i-cell
signatures rather than simply being measurement noise. That is the
strongest single critique to address in Track C work.

---

**END SPEC v1.0**
