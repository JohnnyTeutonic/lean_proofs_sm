/-
  Core/ObstructionTransport.lean

  Witness transport: functorial structure on obstruction witnesses.
  Morphisms in C induce maps on witnesses.
-/

import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Iso
import Mathlib.Logic.Equiv.Defs
import ImpossibilityTheory.Mathematics.Core.Obstruction

namespace ImpossibilityTheory.Mathematics

open CategoryTheory

universe u

variable {C : Type u} [Category.{u} C]

/-- Typeclass for obstructions whose witnesses transport functorially along morphisms.

Given `f : X ⟶ Y`, a witness that `X` resolves `o` pushes forward to a witness
that `Y` resolves `o`. This is the key structure enabling the model category. -/
class WitnessTransport (o : StructuralObstruction C) where
  /-- Push a witness forward along a morphism. -/
  map : ∀ {X Y : C}, (X ⟶ Y) → o.Witness X → o.Witness Y
  /-- Identity morphisms act trivially on witnesses. -/
  map_id : ∀ {X : C} (w : o.Witness X), map (𝟙 X) w = w
  /-- Composition of morphisms respects witness transport. -/
  map_comp : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (w : o.Witness X),
    map (f ≫ g) w = map g (map f w)

namespace WitnessTransport

variable {o : StructuralObstruction C} [WitnessTransport o]

/-- Witnesses transport along isomorphisms in both directions. -/
def mapIso {X Y : C} (i : X ≅ Y) : o.Witness X ≃ o.Witness Y where
  toFun := map i.hom
  invFun := map i.inv
  left_inv w := by simp [← map_comp, map_id]
  right_inv w := by simp [← map_comp, map_id]

end WitnessTransport

/-- An obstruction with functorial witnesses: the witness type forms a functor C → Type. -/
structure FunctorialObstruction (C : Type u) [Category.{u} C] extends StructuralObstruction C where
  /-- Witness transport map. -/
  mapWitness : ∀ {X Y : C}, (X ⟶ Y) → Witness X → Witness Y
  /-- Identity law. -/
  mapWitness_id : ∀ {X : C} (w : Witness X), mapWitness (𝟙 X) w = w
  /-- Composition law. -/
  mapWitness_comp : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (w : Witness X),
    mapWitness (f ≫ g) w = mapWitness g (mapWitness f w)

namespace FunctorialObstruction

variable {C : Type u} [Category.{u} C]

/-- Every FunctorialObstruction induces a WitnessTransport instance. -/
instance toWitnessTransport (o : FunctorialObstruction C) :
    WitnessTransport o.toStructuralObstruction where
  map := o.mapWitness
  map_id := o.mapWitness_id
  map_comp := o.mapWitness_comp

/-- The underlying structural obstruction. -/
def toObstruction (o : FunctorialObstruction C) : StructuralObstruction C :=
  o.toStructuralObstruction

end FunctorialObstruction

end ImpossibilityTheory.Mathematics
