"""Validation rules for Calibration Registry Entries."""

from ..models.calibration import CalibrationEntry
from ..models.evidence import EvidenceStatus, ResolutionMode

def validate_calibration_entry(entry: CalibrationEntry) -> bool:
    """Validate entry fields."""
    if not entry.id or not entry.construct or not entry.source_path:
        return False
    return True

def filter_by_resolution_mode(entries: list, mode: str) -> list:
    """Filter calibration entries by resolution mode."""
    if mode == ResolutionMode.CERTIFIED_ONLY.value or mode == "CERTIFIED_ONLY":
        allowed = {EvidenceStatus.CERTIFIED_EXACT.value, EvidenceStatus.CERTIFIED_RECOMPUTED.value}
        return [e for e in entries if getattr(e, 'evidence_status', None) in allowed]
    elif mode == ResolutionMode.CERTIFIED_AND_DERIVED.value or mode == "CERTIFIED_AND_DERIVED":
        allowed = {
            EvidenceStatus.CERTIFIED_EXACT.value, EvidenceStatus.CERTIFIED_RECOMPUTED.value,
            EvidenceStatus.DERIVED_FROM_CERTIFIED.value, EvidenceStatus.DERIVED_DURING_RECOVERY.value,
            EvidenceStatus.HISTORICALLY_EXPLICIT.value
        }
        return [e for e in entries if getattr(e, 'evidence_status', None) in allowed]
    else: # RESEARCH_ALL
        return list(entries)
