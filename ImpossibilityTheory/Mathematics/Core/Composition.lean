/-
  Core/Composition.lean

  Towers of obstruction resolutions.
-/

import ImpossibilityTheory.Mathematics.Core.Forcing

namespace ImpossibilityTheory.Mathematics

open CategoryTheory

universe u

variable (C : Type u) [Category.{u} C]

/-- A tower step: an obstruction set together with its solution operator. -/
structure TowerStep : Type (u + 1) where
  obs : ObstructionSet C
  sol : SolutionOperator (C := C) obs

/-- A (finite) tower of obstruction resolutions. -/
structure ObstructionTower : Type (u + 1) where
  steps : List (TowerStep (C := C))

/-- The composite endofunctor on C induced by a tower (placeholder).

Later: define explicitly via iterated change-of-world along each step's `incl`.
-/
def ObstructionTower.compFunctor (T : ObstructionTower (C := C)) : C ⥤ C :=
  𝟭 C  -- placeholder: you'll refine as you make towers strict/composable

end ImpossibilityTheory.Mathematics
