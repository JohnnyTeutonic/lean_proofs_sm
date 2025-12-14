/-
  Core/Obstruction.lean

  Category-indexed obstructions with witness semantics.
-/

import Mathlib.CategoryTheory.Category.Basic
import ImpossibilityTheory.Mathematics.Core.Mechanisms

namespace ImpossibilityTheory.Mathematics

open CategoryTheory

universe u

variable (C : Type u) [Category.{u} C]

/-- A structural obstruction relative to a category `C`.

`Witness X` is the *type of ways* that `X` resolves the obstruction.
Resolution is `Nonempty (Witness X)`.
-/
structure StructuralObstruction : Type (u + 1) where
  mechanism : ObstructionMechanism
  Witness   : C → Type u

namespace StructuralObstruction

variable {C}

/-- `X` resolves obstruction `o` iff there exists a witness that `o` is solved at `X`. -/
def Resolves (X : C) (o : StructuralObstruction C) : Prop :=
  Nonempty (o.Witness X)

/-- Smart constructor: operation/closure-like obstruction. -/
def operation (W : C → Type u) : StructuralObstruction C :=
  { mechanism := .operation, Witness := W }

/-- Smart constructor: axiom-like obstruction. -/
def axiom' (P : C → Type u) : StructuralObstruction C :=
  { mechanism := .axiom, Witness := P }

/-- Smart constructor: uniqueness-like obstruction (placeholder form). -/
def uniqueness (U : C → Type u) : StructuralObstruction C :=
  { mechanism := .uniqueness, Witness := U }

/-- Smart constructor: coherence-like obstruction (placeholder form). -/
def coherence (G : C → Type u) : StructuralObstruction C :=
  { mechanism := .coherence, Witness := G }

end StructuralObstruction

end ImpossibilityTheory.Mathematics
