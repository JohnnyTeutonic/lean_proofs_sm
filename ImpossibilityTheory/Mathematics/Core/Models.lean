/-
  Core/Models.lean

  The category of resolved models: objects with witnesses for all obstructions,
  morphisms that transport witnesses compatibly.
-/

import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Iso
import ImpossibilityTheory.Mathematics.Core.ObstructionSet
import ImpossibilityTheory.Mathematics.Core.ObstructionTransport

namespace ImpossibilityTheory.Mathematics

open CategoryTheory

universe u

variable {C : Type u} [Category.{u} C]

/-- A functorial obstruction set: all obstructions have witness transport. -/
structure FunctorialObstructionSet (C : Type u) [Category.{u} C] where
  /-- The underlying set of obstructions. -/
  obstructions : List (FunctorialObstruction C)

namespace FunctorialObstructionSet

variable {C : Type u} [Category.{u} C]

/-- Membership predicate for functorial obstruction sets. -/
def mem (S : FunctorialObstructionSet C) (o : FunctorialObstruction C) : Prop :=
  o ∈ S.obstructions

instance : Membership (FunctorialObstruction C) (FunctorialObstructionSet C) where
  mem S o := S.mem o

end FunctorialObstructionSet

/-- A resolved model: an object X together with witnesses for every obstruction.

This is the fundamental object of study: a "fully resolved structure" in the
impossibility-theoretic sense. -/
structure Model {C : Type u} [Category.{u} C] (obs : FunctorialObstructionSet C) where
  /-- The underlying object in the ambient category. -/
  carrier : C
  /-- Witnesses that the carrier resolves each obstruction. -/
  witness : ∀ (o : FunctorialObstruction C), o ∈ obs → o.Witness carrier

namespace Model

variable {C : Type u} [Category.{u} C] {obs : FunctorialObstructionSet C}

/-- Two models are equal iff their carriers and witnesses are equal. -/
@[ext]
theorem ext {M N : Model obs} (h_carrier : M.carrier = N.carrier)
    (h_wit : ∀ o ho, HEq (M.witness o ho) (N.witness o ho)) : M = N := by
  cases M; cases N
  simp only at h_carrier
  subst h_carrier
  congr
  funext o ho
  exact eq_of_heq (h_wit o ho)

end Model

/-- A morphism of models: a morphism in C that transports witnesses compatibly.

This captures the idea that "resolved structures" form their own category,
with morphisms respecting the resolution witnesses. -/
structure ModelHom {C : Type u} [Category.{u} C] {obs : FunctorialObstructionSet C}
    (M N : Model obs) where
  /-- The underlying morphism in C. -/
  hom : M.carrier ⟶ N.carrier
  /-- Witnesses transport correctly: pushing M's witness forward gives N's witness. -/
  wit_comm : ∀ (o : FunctorialObstruction C) (ho : o ∈ obs),
    o.mapWitness hom (M.witness o ho) = N.witness o ho

namespace ModelHom

variable {C : Type u} [Category.{u} C] {obs : FunctorialObstructionSet C}

/-- Identity morphism on a model. -/
def id (M : Model obs) : ModelHom M M where
  hom := 𝟙 M.carrier
  wit_comm o ho := by simp [FunctorialObstruction.mapWitness_id]

/-- Composition of model morphisms. -/
def comp {M N P : Model obs} (f : ModelHom M N) (g : ModelHom N P) : ModelHom M P where
  hom := f.hom ≫ g.hom
  wit_comm o ho := by
    simp [FunctorialObstruction.mapWitness_comp]
    rw [f.wit_comm, g.wit_comm]

@[ext]
theorem ext {M N : Model obs} {f g : ModelHom M N} (h : f.hom = g.hom) : f = g := by
  cases f; cases g
  simp only at h
  subst h
  rfl

end ModelHom

/-- The category of models for a given obstruction set.

Objects are resolved models (carrier + witnesses).
Morphisms are C-morphisms that transport witnesses. -/
instance modelCategory {C : Type u} [Category.{u} C] (obs : FunctorialObstructionSet C) :
    Category (Model obs) where
  Hom := ModelHom
  id := ModelHom.id
  comp := ModelHom.comp
  id_comp f := by ext; simp [ModelHom.id, ModelHom.comp]
  comp_id f := by ext; simp [ModelHom.id, ModelHom.comp]
  assoc f g h := by ext; simp [ModelHom.comp]

namespace Model

variable {C : Type u} [Category.{u} C] {obs : FunctorialObstructionSet C}

/-- The forgetful functor from models to the ambient category. -/
def forget (obs : FunctorialObstructionSet C) : Model obs ⥤ C where
  obj M := M.carrier
  map f := f.hom
  map_id _ := rfl
  map_comp _ _ := rfl

/-- An isomorphism of models induces an isomorphism of carriers. -/
def carrierIso {M N : Model obs} (i : M ≅ N) : M.carrier ≅ N.carrier where
  hom := i.hom.hom
  inv := i.inv.hom
  hom_inv_id := congrArg ModelHom.hom i.hom_inv_id
  inv_hom_id := congrArg ModelHom.hom i.inv_hom_id

end Model

/-- The automorphism group of a model: gauge redundancy within a fixed model. -/
def ModelAut {C : Type u} [Category.{u} C] (obs : FunctorialObstructionSet C)
    (M : Model obs) := M ≅ M

end ImpossibilityTheory.Mathematics
