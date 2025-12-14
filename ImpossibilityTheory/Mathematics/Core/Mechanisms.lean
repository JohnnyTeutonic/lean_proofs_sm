/-
  Core/Mechanisms.lean

  Tags for obstruction "kinds". Logic lives elsewhere.
-/

namespace ImpossibilityTheory.Mathematics

/-- The fundamental obstruction mechanisms (extendable). -/
inductive ObstructionMechanism where
  | operation   -- missing / non-closed operations
  | axiom       -- failed axioms / properties
  | uniqueness  -- multiple candidates, no canonical choice
  | coherence   -- local data does not glue
  deriving DecidableEq, Repr

end ImpossibilityTheory.Mathematics
