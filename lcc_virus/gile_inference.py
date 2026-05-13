"""lcc_virus.gile_inference — re-export shim for legacy `lcc_virus_gile_inference`."""

from __future__ import annotations

from typing import Any

try:
    import lcc_virus_gile_inference as _legacy
except ImportError:  # pragma: no cover
    _legacy = None


def _get(name: str) -> Any:
    if _legacy is None:
        raise RuntimeError(
            f"{name} requires legacy `lcc_virus_gile_inference` module."
        )
    return getattr(_legacy, name, None)


GileInference = _get("GileInference") if _legacy else None

__all__ = ["GileInference"]
