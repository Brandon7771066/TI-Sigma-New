"""
ARC-AGI TI Sigma Solver
=======================
A 5-valued logic approach to Abstraction and Reasoning Corpus tasks.

TI Sigma Five-Valued Truth System (URB #528):

  POSITIONAL truth values (the three ternary slots):
    FALSE        (0): definitively background / false
    INDETERMINATE(1): genuinely in the middle — coherent 50/50 balance between
                      figure and ground. This IS the third ternary slot. Its
                      irreconcilability is COHERENT — it knows it is balanced.
    TRUE         (2): definitively figure / pattern-relevant

  QUALITY-LEVEL designations (not positional slots):
    TRALSE       (3): imperfection/contradiction quality marker — the "grease
                      that makes the gears run." Tralse is EMBEDDED inside
                      True, False, and Indeterminate. It marks a state that
                      has coherent contradiction — imperfect but processable.
                      Tralse has no position on the truth polarity.
    DOUBLE_TRALSE(4): MR1 failure — incoherent, irresolvable contradiction.
                      FLAGGED and IMMEDIATELY DISCARDED. No dedicated storage
                      slot. The system recognizes nonsense and refuses to
                      dwell on it. DT cells collapse to their best positional
                      guess (nearest coherent neighbor).

Why 5 values but still ternary?
  Ternary logic is preserved in the 3 positional slots (FALSE/INDETERMINATE/TRUE).
  Tralse cannot be the "third value" because it has no location on the truth
  spectrum — it is a *property* of any state. Indeterminate IS the balanced
  middle. Double Tralse is not stored — it is a detection-and-discard signal.

Key distinction (Indeterminate vs Double Tralse):
  Both involve irreconcilability. The difference:
    Indeterminate: coherent irreconcilability (knows it is 50/50)
    Double Tralse:  incoherent irreconcilability (self-contradicting, MR1 fail)

Myrion Resolution (MR1/MR2):
  MR1: Filters Double Tralse — cells/transforms below LCC 0.8647 → discard
  MR2: Maintains Indeterminate — cells balanced between interpretations; holds
       open until further context collapses them to TRUE or FALSE
  MR Radiant: LCC >= 0.9323 — full causal weight, GILE Radiant
"""

FALSE          = 0
INDETERMINATE  = 1
TRUE           = 2
TRALSE         = 3
DOUBLE_TRALSE  = 4

TVALUES = {
    FALSE:         "FALSE",
    INDETERMINATE: "INDETERMINATE",
    TRUE:          "TRUE",
    TRALSE:        "TRALSE",
    DOUBLE_TRALSE: "DOUBLE_TRALSE",
}

# Legacy aliases for backward compatibility
MR_PEND = TRALSE  # MR_PEND was the 4th slot; now correctly mapped to TRALSE quality
