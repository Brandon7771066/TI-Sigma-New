"""lcc_virus.framework — re-export shim for legacy `lcc_virus_framework`."""

from __future__ import annotations

from typing import Any

try:
    import lcc_virus_framework as _legacy
except ImportError:  # pragma: no cover
    _legacy = None


def _get(name: str) -> Any:
    if _legacy is None:
        raise RuntimeError(
            f"{name} requires legacy `lcc_virus_framework` module. "
            "See lcc_virus/CHANGELOG.md M2 for migration plan."
        )
    return getattr(_legacy, name, None)


VirusFramework = _get("VirusFramework") if _legacy else None

__all__ = ["VirusFramework"]
