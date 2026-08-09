"""Registry Loader for Master V1 Registry."""

import json
import os
from typing import List, Dict, Any
from ..models.calibration import CalibrationEntry

def load_master_registry_v1(registry_path: str = None) -> List[CalibrationEntry]:
    if registry_path is None:
        registry_path = os.path.normpath(os.path.join(
            os.path.dirname(__file__), '..', '..', '..', 'calibration_registry', 'master_registry_v1.json'
        ))
    if not os.path.exists(registry_path):
        return []
    with open(registry_path, 'r', encoding='utf-8') as f:
        data = json.load(f)
    
    entries = []
    for item in data:
        entries.append(CalibrationEntry(**item))
    return entries
