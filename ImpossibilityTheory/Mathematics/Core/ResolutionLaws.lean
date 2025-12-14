/-
  Core/ResolutionLaws.lean

  Optional well-behavedness axioms for obstructions.
-/

import Mathlib.CategoryTheory.Category.Basic
import ImpossibilityTheory.Mathematics.Core.Obstruction

namespace ImpossibilityTheory.Mathematics

open CategoryTheory

universe u

variable (C : Type u) [Category.{u} C]

/-- Laws an obstruction may satisfy (optional structure). -/
structure ObstructionLaw (o : StructuralObstruction C) : Prop where
  stable_under_iso :  (X Y : C), (X  Y)  StructuralObstruction.Resolves X o  StructuralObstruction.Resolves Y o

end ImpossibilityTheory.Mathematics
