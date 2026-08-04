# Qumode PD Specification

Status: PROPOSED_THEORETICAL_EXTENSION

This document defines a non-hardware, simulation-only qumode interpretation for PD.

## Scope

- Input: scalar PD value and threshold profile.
- Output: continuous confidence envelope and optional discretized ternary bucket.
- Constraints: deterministic implementation with fixed seed for stochastic sampling.

## Mapping

Let PD be normalized to x in [-1, 1].

- False pressure: f(x) = max(0, -x)
- True pressure: t(x) = max(0, x)
- Indeterminate pressure: i(x) = 1 - |x|

Then normalize (f, i, t) by their sum.

## Operational Notes

- This mapping is an informational encoding, not a physical oscillator model.
- Continuous confidence should remain inspectable in CSV/JSON outputs.
- Any hardware language must remain out of scope until dedicated empirical work is completed.
