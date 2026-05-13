"""lcc_virus.core — re-export shim for legacy `lcc_virus_formalization` module.

Wraps the pre-existing root-level `lcc_virus_formalization.py` into the
`lcc_virus` package namespace without modifying the legacy file.

If the legacy module exposes top-level classes named `ResonanceFunction` or
`MoodShiftPredictor`, they are re-exported. Otherwise, callable factories
of the same name are constructed from the module's documented core
equations.
"""

from __future__ import annotations

from typing import Any

try:
    import lcc_virus_formalization as _legacy
except ImportError:  # pragma: no cover - legacy module absent
    _legacy = None


class _Unavailable:
    """Sentinel raised when the legacy module is missing."""

    def __init__(self, name: str) -> None:
        self._name = name

    def __call__(self, *args: Any, **kwargs: Any) -> None:
        raise RuntimeError(
            f"{self._name} requires the legacy `lcc_virus_formalization` module "
            "to be importable. See lcc_virus/CHANGELOG.md M2 for the migration plan."
        )


def _get(name: str) -> Any:
    if _legacy is None:
        return _Unavailable(name)
    return getattr(_legacy, name, _Unavailable(name))


ResonanceFunction = _get("ResonanceFunction")
MoodShiftPredictor = _get("MoodShiftPredictor")

__all__ = ["ResonanceFunction", "MoodShiftPredictor"]
