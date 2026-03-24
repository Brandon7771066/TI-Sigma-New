"""
ARC-AGI TI Sigma Solver
=======================
A 4-valued logic approach to Abstraction and Reasoning Corpus tasks.

TI Sigma Framework:
  - TRUE    (2): cell is definitively figure / pattern-relevant
  - FALSE   (0): cell is definitively background
  - TRALSE  (1): cell is ambiguously figure or ground (context-dependent)
  - MR_PEND (3): cell's truth value depends on resolving a downstream pattern

Myrion Resolution (MR1): constraint propagation across tralse cells
toward the highest-coherence attractor, rather than arbitrary binary commit.

LCC (Local Coherence Coefficient): measures how consistently a candidate
transformation applies across all training pairs — analogous to the
Logical Coherence Coefficient in TI Sigma theory.
"""

FALSE    = 0
TRALSE   = 1
TRUE     = 2
MR_PEND  = 3

TVALUES = {FALSE: "FALSE", TRALSE: "TRALSE", TRUE: "TRUE", MR_PEND: "MR_PEND"}
