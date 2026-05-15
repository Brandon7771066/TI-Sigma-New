import NavierStokes.UOPGap
import NavierStokes.ToyDecay
-- UOPGap theorem: should list sorryAx + UOP_existence_claim (NOT closed)
#print axioms NavierStokes.UOPGap.UOP_implies_NS_smoothness
-- ToyDecay theorem: should list ONLY built-in foundations (real proof)
#print axioms NavierStokes.ToyDecay.energy_monotone_decay
#print axioms NavierStokes.ToyDecay.energy_nonneg
