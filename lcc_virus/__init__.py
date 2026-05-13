"""LCC Virus — Latched Consciousness Correlator retrieval package.

Pass-49 L2: Package skeleton wrapping the pre-existing module-level
`lcc_virus_*.py` files into an importable, versioned namespace suitable
for eventual PyPI release.

Public API (current):
    from lcc_virus import (
        ResonanceFunction,
        MoodShiftPredictor,
        VirusFramework,
        FullPipeline,
        GileInference,
        TextBrain,
    )

Status: ALPHA. Public API is unstable. Do not depend on import paths in
production code yet. See `lcc_virus/CHANGELOG.md` for milestones.

#69 caveat: empirical validation of the underlying claims (77.3% animal-
study efficacy, mood-shift prediction beta values) is OUTSTANDING. This
package wraps the *implementation*; the *claims* are not yet independently
replicated. See `papers/PASS_48_LCC_VIRUS_RETRIEVAL_DEVELOPMENT_PLAN_2026-05-13.md`
M4 (independent replication) for gating criterion before commercial use.
"""

from __future__ import annotations

__version__ = "0.1.0a1"
__status__ = "alpha"
__all__ = [
    "ResonanceFunction",
    "MoodShiftPredictor",
    "VirusFramework",
    "FullPipeline",
    "GileInference",
    "TextBrain",
    "__version__",
]


def _lazy_import(name: str):
    """Defer heavy imports of legacy modules until first access."""
    import importlib
    return importlib.import_module(name)


def __getattr__(name: str):
    mapping = {
        "ResonanceFunction": ("lcc_virus.core", "ResonanceFunction"),
        "MoodShiftPredictor": ("lcc_virus.core", "MoodShiftPredictor"),
        "VirusFramework": ("lcc_virus.framework", "VirusFramework"),
        "FullPipeline": ("lcc_virus.pipeline", "FullPipeline"),
        "GileInference": ("lcc_virus.gile_inference", "GileInference"),
        "TextBrain": ("lcc_virus.text_brain", "TextBrain"),
    }
    if name in mapping:
        module_path, attr = mapping[name]
        mod = _lazy_import(module_path)
        return getattr(mod, attr, None)
    raise AttributeError(f"module 'lcc_virus' has no attribute {name!r}")
