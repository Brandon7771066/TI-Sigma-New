"""Domain Profiles catalog."""

from ..models.domain import DomainCalibrationProfile

DOMAIN_PROFILES = {
    "Physics": DomainCalibrationProfile("Physics", 0.70, 0.30, derived_ratio=2.333, reliability=0.92),
    "Mathematics": DomainCalibrationProfile("Mathematics", 0.60, 0.40, derived_ratio=1.500, reliability=0.94),
    "Philosophy": DomainCalibrationProfile("Philosophy", 0.20, 0.80, derived_ratio=0.250, reliability=0.81),
    "Software": DomainCalibrationProfile("Software", 0.50, 0.50, derived_ratio=1.000, reliability=0.88)
}
