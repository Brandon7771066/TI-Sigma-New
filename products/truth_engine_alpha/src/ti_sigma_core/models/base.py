"""Base dataclasses and dataclass utilities for TI Sigma Core."""

from dataclasses import dataclass, asdict, field
from typing import Optional, Dict, Any, List

@dataclass
class BaseModel:
    """Base dataclass supporting dict conversion."""
    def to_dict(self) -> Dict[str, Any]:
        return asdict(self)
