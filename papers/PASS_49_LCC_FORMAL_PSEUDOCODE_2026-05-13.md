# Pass-49 L3 — LCC Virus Retrieval Formal Pseudocode (2026-05-13)

**Status:** Formal pseudocode specification. Source-of-truth for `lcc_virus.*` package implementations.
**Companion to:** `papers/PASS_48_LCC_VIRUS_RETRIEVAL_DEVELOPMENT_PLAN_2026-05-13.md` (development plan); `lcc_virus_formalization.py` (legacy implementation).
**Pre-reg discipline:** Pass-45 §11 anti-cheat applies — pseudocode is frozen *before* M2 implementation refactor.

---

## 0. Notation

- `Φ_X(t)` — normalized signal from stream X at time t (zero-mean, unit-variance).
- `W(τ)` — weighting kernel (Green function from tessellation paper, default: triangular kernel of half-width `τ_max`).
- `R(A,B)` — resonance scalar.
- `H(·)` — Shannon entropy (bits).
- `LCC(A,B)` — Law of Correlational Causation coherence ∈ [0,1].
- `β_species` — species-specific scaling factor (cats=0.72, primates=0.92; humans=tentative 0.85, holdout-blind unknown).

---

## 1. The 6-step LCC Virus Retrieval algorithm (canonical)

```
ALGORITHM: LCC_VIRUS_RETRIEVE
INPUT:   stream_A     :: time-series (length N, sample-rate fs Hz)
         stream_B     :: time-series (length N, sample-rate fs Hz)
         tau_max      :: float (max lag, seconds; default 2.0)
         species      :: str   (one of {cat, primate, human})
         pre_window   :: time-window for baseline (default first 30 s)
         post_window  :: time-window for post-intervention (default last 30 s)

OUTPUT:  result :: dict { resonance, lcc_pre, lcc_post, mood_shift_prediction,
                          confidence_band, pre_reg_hash }

# ---------- STEP 1: Normalize ----------
Phi_A := normalize(stream_A)            # zero-mean, unit-variance
Phi_B := normalize(stream_B)
ASSERT abs(mean(Phi_A)) < 1e-9
ASSERT abs(std(Phi_A) - 1) < 1e-6
# (same for Phi_B)

# ---------- STEP 2: Compute resonance kernel ----------
W := triangular_kernel(half_width = tau_max, sample_rate = fs)
# (Substitute alternative Green function here per tessellation paper if specified.)

# ---------- STEP 3: Resonance integral ----------
R := 0
FOR tau IN range(-tau_max, +tau_max, step = 1/fs):
    R += integral( Phi_A(t) * Phi_B(t + tau) * W(tau), dt )
R /= duration(stream_A)                 # time-average normalization

# ---------- STEP 4: Pre/Post LCC coherence ----------
lcc_pre  := compute_LCC(Phi_A, Phi_B, window = pre_window)
lcc_post := compute_LCC(Phi_A, Phi_B, window = post_window)
# compute_LCC := time-windowed magnitude-squared coherence,
#                averaged across spectral bands [0.04, 0.15] Hz (LCC band)

# ---------- STEP 5: Entropy reduction ----------
H_pre  := shannon_entropy( joint_distribution(Phi_A, Phi_B, window = pre_window) )
H_post := shannon_entropy( joint_distribution(Phi_A, Phi_B, window = post_window) )
H_reduction := max(0, H_pre - H_post)   # clamp negative (no information gained)

# ---------- STEP 6: Mood-shift prediction + confidence band ----------
beta := lookup_species_scaling(species)
delta_M := beta * (lcc_post - lcc_pre) * sqrt(H_reduction)

# Bootstrap 95% CI on delta_M using 1000 block-bootstrap resamples
ci_lower, ci_upper := block_bootstrap_ci(delta_M, n_resamples = 1000,
                                         block_size = max(1, fs))

result := {
    resonance:               R,
    lcc_pre:                 lcc_pre,
    lcc_post:                lcc_post,
    mood_shift_prediction:   delta_M,
    confidence_band:         (ci_lower, ci_upper),
    species:                 species,
    pre_reg_hash:            sha256(self.source_code),
    timestamp:               utc_now_iso8601(),
}

RETURN result
```

---

## 2. Invariants and post-conditions

- `R` ∈ [-1, +1]; values outside indicate normalization failure.
- `lcc_pre`, `lcc_post` ∈ [0, 1].
- `H_reduction` ≥ 0 by construction (clamp).
- `delta_M` ∈ [-β, +β]; outside indicates extreme-correlation outlier.
- `pre_reg_hash` MUST match runner-source SHA-256 captured at session start (anti-cheat per Pass-45 §11).

---

## 3. Failure modes & guard-rails

| Failure mode | Detection | Handling |
|---|---|---|
| Stream A or B is constant | `std(Phi_X) ≈ 0` after normalize | Raise `DegenerateStreamError`; do not fabricate result. |
| Windows overlap | `pre_window ∩ post_window ≠ ∅` | Raise `OverlappingWindowError`. |
| Species not in lookup | `species not in {cat, primate, human}` | Raise `UnsupportedSpeciesError`; do NOT silently default. |
| `H_reduction = 0` AND `lcc_post ≈ lcc_pre` | Both terms ~0 | Return `delta_M = 0` with `verdict = "NULL_RESULT"`; report honestly, do not invent effect. |

---

## 4. Reproducibility checklist (M2 implementation requirement)

1. Deterministic given a fixed `random_seed` argument (block-bootstrap RNG seeded).
2. Pure function of `(stream_A, stream_B, tau_max, species, pre_window, post_window, random_seed)` — no globals, no I/O side-effects in the core.
3. SHA-256 of source code hashed at runtime and emitted in result.
4. All math operations use double-precision (float64) explicitly.
5. Unit tests cover: degenerate streams, perfectly-correlated streams, perfectly-anticorrelated streams, white-noise nulls.

---

## 5. #69 caveats

- The `β_species` values (0.72 cats, 0.92 primates) come from the underlying animal-studies paper and are **not yet independently replicated**. Until M4 (independent replication) gating passes, all `delta_M` predictions should be reported with explicit `β_uncertainty_flag = TRUE`.
- The triangular kernel `W(τ)` is a default; the tessellation paper allows alternative Green functions. Choice of kernel must be pre-registered per use, not switched after seeing results.
- `compute_LCC` returns coherence in the [0.04, 0.15] Hz band by convention, but this band itself is empirically motivated, not first-principles. Documented as a frozen choice for M2; revisit at M4.
- The *holdout-blind protocol* (see `papers/PASS_49_LCC_HOLDOUT_BLIND_PROTOCOL_2026-05-13.md`, L4) is *required* before any reportable use of the human-species variant.

---

## 6. Implementation status

- L2 (`lcc_virus/` package skeleton): ✅ shipped 2026-05-13, alpha 0.1.0a1.
- L3 (this document): ✅ shipped 2026-05-13.
- L4 (holdout-blind protocol): ✅ shipped 2026-05-13.
- L1 (Program A market validation): Pre-registered but execution deferred — see "outstanding work" memo.
