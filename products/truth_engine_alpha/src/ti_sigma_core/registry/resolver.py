"""Registry Resolver providing read-only query APIs with mode enforcement."""

from typing import List, Dict, Any, Optional
from .loader import load_master_registry_v1
from .validation import filter_by_resolution_mode
from ..models.evidence import ResolutionMode
from ..models.gile import GILEVector
from ..models.truth_axes import TruthAxesQuaternionBlock
from ..models.domain import DomainCalibrationProfile

class RegistryResolver:
    def __init__(self, registry_path: str = None):
        self.entries = load_master_registry_v1(registry_path)

    def get_calibration(self, entry_id: str, mode: str = "CERTIFIED_ONLY") -> Optional[Any]:
        filtered = filter_by_resolution_mode(self.entries, mode)
        for e in filtered:
            if e.id == entry_id:
                return e
        return None

    def get_construct_calibrations(self, construct: str, mode: str = "CERTIFIED_ONLY") -> List[Any]:
        filtered = filter_by_resolution_mode(self.entries, mode)
        return [e for e in filtered if e.construct.lower() == construct.lower()]

    def get_gile_values(self, domain: Optional[str] = None, mode: str = "CERTIFIED_ONLY") -> Optional[GILEVector]:
        """In CERTIFIED_ONLY mode, simulation default universal GILE weights MUST NOT be returned!"""
        if mode == "CERTIFIED_ONLY":
            return None # No certified universal GILE weights exist
        return GILEVector()

    def get_truth_axes(self, domain: Optional[str] = None, mode: str = "CERTIFIED_ONLY") -> Optional[TruthAxesQuaternionBlock]:
        if mode == "CERTIFIED_ONLY":
            return None
        return TruthAxesQuaternionBlock()

    def get_hem_gile_weights(self, domain: str, mode: str = "CERTIFIED_AND_DERIVED") -> Optional[Dict[str, float]]:
        domain_map = {
            "Physics": {"hem": 0.70, "gile": 0.30, "ratio": 2.333},
            "Mathematics": {"hem": 0.60, "gile": 0.40, "ratio": 1.500},
            "Philosophy": {"hem": 0.20, "gile": 0.80, "ratio": 0.250},
            "Software": {"hem": 0.50, "gile": 0.50, "ratio": 1.000}
        }
        return domain_map.get(domain)
