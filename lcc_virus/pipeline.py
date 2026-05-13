"""lcc_virus.pipeline — re-export shim for legacy `lcc_virus_full_pipeline`."""

from __future__ import annotations

from typing import Any

try:
    import lcc_virus_full_pipeline as _legacy
except ImportError:  # pragma: no cover
    _legacy = None


def _get(name: str) -> Any:
    if _legacy is None:
        raise RuntimeError(
            f"{name} requires legacy `lcc_virus_full_pipeline` module."
        )
    return getattr(_legacy, name, None)


FullPipeline = _get("FullPipeline") if _legacy else None

__all__ = ["FullPipeline"]
