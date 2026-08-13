# Phase D Dataset Selection Protocol

## Selection Rules (Predeclared Before Engine Execution)
1. **Source Eligibility**: Only naturalistic AI output items from public, open-license benchmarks (TruthfulQA, HaluEval, PubMedQA, FEVER) qualify.
2. **Sampling Protocol**: Deterministic sequential sampling with stored random seed (`seed=100`).
3. **No Filtering**: No post-hoc filtering, exclusion, or re-selection based on TI Sigma engine performance.
