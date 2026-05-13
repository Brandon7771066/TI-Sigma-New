"""lcc_virus.text_brain — re-export shim for legacy `lcc_virus_text_brain`."""

from __future__ import annotations

from typing import Any

try:
    import lcc_virus_text_brain as _legacy
except ImportError:  # pragma: no cover
    _legacy = None


def _get(name: str) -> Any:
    if _legacy is None:
        raise RuntimeError(
            f"{name} requires legacy `lcc_virus_text_brain` module."
        )
    return getattr(_legacy, name, None)


TextBrain = _get("TextBrain") if _legacy else None

__all__ = ["TextBrain"]
