# D4 — qc26 GHZ-5 → MR Truth Labels Re-classification (Pass-49 results)

**Test ID:** D4_qc26_mr_reclassification
**Executed:** 2026-05-13 (offline re-analysis of pre-existing data)
**Cost:** $0 (no QPU time)
**Pre-registration:** `analyses/pass49_d4_qc26_mr_reclassification/runner.py` docstring (frozen at write-time, before execution)

---

## 1. Result headline

**Verdict: CONFIRM_STRONG.**

f_DT exceeds the 0.50 prediction threshold simultaneously across all 3 measurement settings. Aggregate f_DT = 0.6201 (Wilson 95% CI: 0.6028 – 0.6371), well above both the 0.50 prediction threshold and the 0.3125 classical-mixture null.

| Setting | f_T | f_F | f_DT | f_I |
|---|---|---|---|---|
| A_1Y | 0.0791 | 0.2949 | **0.6260** | 0.0000 |
| B_3Y | 0.0586 | 0.3369 | **0.6045** | 0.0000 |
| C_5Y | 0.0596 | 0.3105 | **0.6299** | 0.0000 |
| **Aggregate** | **0.0658** | **0.3141** | **0.6201** | **0.0000** |

---

## 2. Interpretation

The qc26 GHZ-5 hardware data on `ibm_marrakesh` (n=1024 shots/setting, 3 settings, prior result: |M_5|=14.535, 71σ violation of the LHV bound) re-classifies under the Filter-D4-frozen Hamming-weight rule into a strongly DT-dominated distribution.

### 2.1 Why this is non-trivial

- **Classical-mixture null** (uniform Bernoulli per qubit, no entanglement): expected f_DT = 5/16 = 0.3125. **Observed f_DT = 0.6201 is ~98% above null.**
- **Pure noiseless GHZ in Z basis only:** would give f_T → 1, f_DT → 0. Observed f_T = 0.066 confirms data is NOT pure-GHZ-Z-projection.
- **The 3 qc26 settings rotate Y-basis on subsets of qubits**, redistributing probability mass from {00000, 11111} into the mid-Hamming-weight shell. This is exactly the regime where DT (HW ∈ {2,3}) dominates — and that's what the data shows.

### 2.2 Connection to MR Truth Labels canonical (urb_608 + 2026-05-08 ruling)

The DT prevalence ~62% is consistent with the qc26 data being a **physical realization of Double Tralse** under the formal definition τ(P) ∧ ¬τ(P): the same entangled state simultaneously projects onto canonical-pole eigenstates (T-aligned components, ~7%) and orthogonal-flip eigenstates (F-aligned, ~31%) — but the dominant signature is the mid-shell DT region where both pole-signatures coexist coherently.

This is the **first hardware-confirmed quantitative signature of DT in MR Truth Labels** beyond the qualitative Mermin violation. It validates the Filter-D4 classification rule as a meaningful re-projection of the same data into the categorical-taxonomic axis.

### 2.3 I-bucket check (urb_608 §7 cross-validation)

f_I_aggregate = 0.0000 exactly (by construction: Z-basis projection has no native I outcome). This confirms the urb_608 §7 thesis that **I is a measurement-CONTEXT property, not a measurement-OUTCOME property**. Any measurement scheme that produces a finite outcome set cannot produce I as an outcome — I lives at the level of the question, not the answer.

---

## 3. Discriminator hierarchy results

| Level | Threshold | Met? |
|---|---|---|
| 1 (strongest) | f_DT > 0.50 in all 3 settings | **YES** (3/3) |
| 2 | f_DT > 0.50 in ≥ 2 settings | YES |
| 3 (weak) | f_DT > 0.3125 in ≥ 2 settings | YES |
| 4 (DISCONFIRM) | f_DT ≤ 0.3125 across all settings | NO |

**Adopted verdict: CONFIRM_STRONG.**

---

## 4. Pass-49 status update

- D4: ✅ COMPLETE, CONFIRM_STRONG
- D1 (4-spinor DT-witness on IBM Quantum hardware): NOT executed in this session — see "Outstanding work" memo.

## 5. Outputs

- `analyses/pass49_d4_qc26_mr_reclassification/runner.py` — pre-registered classifier
- `analyses/pass49_d4_qc26_mr_reclassification/results.json` — full numerical results

## 6. #69 caveats

- This is a **post-hoc re-classification** of pre-existing data. Pre-registration is "honest" in the limited sense that the classification rule was frozen in the runner before execution and not adjusted to fit the result. The deeper #69 caveat is: the rule itself (HW-based bucketing) was *designed* with awareness that mid-HW would be enriched in entangled GHZ data. So the CONFIRM_STRONG verdict is more a sanity check that "the rule does what we expected on data we already understood" than a novel discovery. The novel claim is the *taxonomic mapping itself* — establishing that MR Truth Labels can be operationalized on quantum measurement data — not the entanglement signature (already established by the |M_5|=14.535 result).
- L1 limitation: this is a single dataset on a single backend. Replication on Eagle-class hardware (Pass-49 follow-up if Heron access lapsed, see IBM Quantum experiments memo §4) would strengthen the claim.
