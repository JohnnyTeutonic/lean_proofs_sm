/-
  Core/Forcing.lean

  Solution operators = reflections into obstruction-free worlds.
-/

import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Functor.Basic
import ImpossibilityTheory.Mathematics.Core.ObstructionSet

namespace ImpossibilityTheory.Mathematics

open CategoryTheory

universe u

variable (C : Type u) [Category.{u} C]

/-- A solution operator for an obstruction set.

Interpretation:
`refl` adds exactly the structure required to resolve the obstructions,
and is universal among maps into obstruction-free objects.
-/
structure SolutionOperator (obs : ObstructionSet C) : Type (u + 1) where
  /-- The "resolved world" category. -/
  D : Type u
  [catD : Category.{u} D]
  /-- Inclusion of resolved world into the ambient category. -/
  incl : D ⥤ C
  /-- Reflection / completion / closure operator. -/
  refl : C ⥤ D
  /-- Universal property: refl ⊣ incl. -/
  adj : refl ⊣ incl
  /-- Soundness: everything in D is obstruction-free (up to iso in C). -/
  sound :
    ∀ (Y : D), ObstructionSet.IsObstructionFree obs (incl.obj Y)
  /-- Completeness: if X is obstruction-free, then X is in the essential image of incl. -/
  complete :
    ∀ (X : C),
      ObstructionSet.IsObstructionFree obs X →
      ∃ (Y : D), Nonempty (incl.obj Y ≅ X)

attribute [instance] SolutionOperator.catD

end ImpossibilityTheory.Mathematics
