"""lcc_virus.experiments.program_a — Bidirectional LCC in Markets.

Re-export shim around the Pass-49 L-1 runner at
`analyses/pass49_program_a_bidirectional_lcc/runner.py`. Provides the
core building blocks (`gaussian_weighted_lagged_xcorr`,
`granger_causality_min_p`, `C_EMERICK`) for downstream callers.

Per Pass-48 architect-review CRITICAL #69 finding (logged in
`papers/PASS_48_LCC_VIRUS_RETRIEVAL_DEVELOPMENT_PLAN_2026-05-13.md` §0
2026-05-13 update), the closed form `C_EMERICK = 1/(phi*sqrt(2))` is a
CONJECTURAL FIT, not a derived constant. The empirical value 0.4370
should be cited externally, with the closed form as a candidate fit
pending Track-C M5 first-principles derivation.
"""
from __future__ import annotations

PHI = (1 + 5 ** 0.5) / 2
C_EMERICK_EMPIRICAL = 0.4370
C_EMERICK_CONJECTURAL_FIT = 1 / (PHI * (2 ** 0.5))  # 0.43701602...
C_EMERICK = C_EMERICK_CONJECTURAL_FIT  # alias for back-compat

# Pre-registered window parameters (Program A §2.5)
WINDOW = 60
STEP = 5
SIGMA = 5
MAX_LAG = 10
GRANGER_LAGS = (1, 2, 3, 4, 5)
ALPHA = 0.01

import sys as _sys
from pathlib import Path as _Path
_RUNNER_DIR = _Path(__file__).resolve().parents[2] / "analyses" / "pass49_program_a_bidirectional_lcc"
if str(_RUNNER_DIR) not in _sys.path:
    _sys.path.insert(0, str(_RUNNER_DIR))

try:
    from runner import (  # type: ignore[import-not-found]
        gaussian_weighted_lagged_xcorr,
        granger_causality_min_p,
        granger_min_p,
    )
except Exception:  # pragma: no cover
    gaussian_weighted_lagged_xcorr = None
    granger_causality_min_p = None
    granger_min_p = None

__all__ = [
    "PHI", "C_EMERICK", "C_EMERICK_EMPIRICAL", "C_EMERICK_CONJECTURAL_FIT",
    "WINDOW", "STEP", "SIGMA", "MAX_LAG", "GRANGER_LAGS", "ALPHA",
    "gaussian_weighted_lagged_xcorr", "granger_causality_min_p", "granger_min_p",
]
