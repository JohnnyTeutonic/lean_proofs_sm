/-
  Core/ObstructionSet.lean

  Sets of obstructions and obstruction-free objects.
-/

import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Data.Finset.Basic
import ImpossibilityTheory.Mathematics.Core.Obstruction

namespace ImpossibilityTheory.Mathematics

open CategoryTheory

universe u

variable (C : Type u) [Category.{u} C]

/-- A set of obstructions in category `C`. -/
structure ObstructionSet : Type (u + 1) where
  obstructions : Set (StructuralObstruction C)
  finite_basis : ∃ (B : List (StructuralObstruction C)), ∀ x, x ∈ B ↔ x ∈ obstructions

namespace ObstructionSet

variable {C}

/-- `X` is obstruction-free for `obs` iff it resolves every obstruction in `obs`. -/
def IsObstructionFree (obs : ObstructionSet C) (X : C) : Prop :=
  ∀ o, o ∈ obs.obstructions → StructuralObstruction.Resolves X o

/-- The subtype of obstruction-free objects (lightweight "subcategory for now"). -/
def ObstructionFreeSubcat (obs : ObstructionSet C) :=
  { X : C // IsObstructionFree obs X }

end ObstructionSet

end ImpossibilityTheory.Mathematics
