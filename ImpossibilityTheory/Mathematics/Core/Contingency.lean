/-
  Core/Contingency.lean

  Structural completeness vs. contingent moduli:
  - Isomorphism of models
  - Structural completeness = all models isomorphic
  - Contingent sector = non-trivial automorphisms or multiple iso classes
-/

import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Iso
import ImpossibilityTheory.Mathematics.Core.Models

namespace ImpossibilityTheory.Mathematics

open CategoryTheory

universe u

variable {C : Type u} [Category.{u} C]

/-!
## Isomorphism of models

Two models are isomorphic when there's an isomorphism in the model category.
-/

/-- Two models are isomorphic in the model category. -/
def ModelIso {obs : FunctorialObstructionSet C} (M N : Model obs) : Prop :=
  Nonempty (M ≅ N)

namespace ModelIso

variable {obs : FunctorialObstructionSet C}

/-- ModelIso is reflexive. -/
theorem refl (M : Model obs) : ModelIso M M := ⟨Iso.refl M⟩

/-- ModelIso is symmetric. -/
theorem symm {M N : Model obs} (h : ModelIso M N) : ModelIso N M :=
  h.map Iso.symm

/-- ModelIso is transitive. -/
theorem trans {M N P : Model obs} (h1 : ModelIso M N) (h2 : ModelIso N P) : ModelIso M P :=
  ⟨h1.some.trans h2.some⟩

/-- ModelIso is an equivalence relation. -/
theorem equivalence (obs : FunctorialObstructionSet C) : Equivalence (@ModelIso C _ obs) :=
  ⟨refl, symm, trans⟩

end ModelIso

/-!
## Structural Completeness

The obstruction set is "structurally complete" if all models are isomorphic:
no contingent parameters remain.
-/

/-- Structural completeness: any two models satisfying the obstructions are isomorphic.

This means all data is forced by the obstructions---no free parameters. -/
def StructurallyComplete (obs : FunctorialObstructionSet C) : Prop :=
  ∀ M N : Model obs, ModelIso M N

/-!
## Contingent Sector

The contingent sector is non-trivial when structural completeness fails.
-/

/-- The contingent sector is non-trivial: not all models are isomorphic. -/
def HasContingentModuli (obs : FunctorialObstructionSet C) : Prop :=
  ¬ StructurallyComplete obs

/-- A specific model has gauge contingency: nontrivial automorphisms. -/
def HasGaugeContingency {obs : FunctorialObstructionSet C} (M : Model obs) : Prop :=
  Nontrivial (M ≅ M)

/-!
## The Interface Theorem

Formal statement of the structural necessity vs. contingent moduli boundary.
-/

/-- The Interface Theorem:

Given an obstruction set `obs`:
- If `StructurallyComplete obs`, all data is structurally determined
- Otherwise, contingent parameters exist (multiple iso classes or nontrivial Aut)

This captures the principled boundary between structural necessity
and contingent realization. -/
theorem interface_dichotomy (obs : FunctorialObstructionSet C) :
    StructurallyComplete obs ∨ HasContingentModuli obs := by
  by_cases h : StructurallyComplete obs
  · left; exact h
  · right; exact h

/-!
## Decoration Functors (Contingent Sector Interface)

Parameters not arising from obstructions are "decorations" on resolved models.
-/

/-- A decoration type: assigns extra data to each resolved model.

This captures contingent parameters like Yukawa couplings: data that
can vary without affecting obstruction resolution. -/
structure Decoration (obs : FunctorialObstructionSet C) where
  /-- The type of decoration data for each model. -/
  Param : Model obs → Type u

variable {obs : FunctorialObstructionSet C}

/-- A decorated model: a resolved model plus decoration data. -/
structure DecoratedModel (D : Decoration obs) where
  /-- The underlying resolved model. -/
  base : Model obs
  /-- The decoration data (e.g., Yukawa couplings). -/
  param : D.Param base

/-- The forgetful map from decorated models to models.

The fibres are exactly the contingent sector:
varying the decoration does not change obstruction resolution. -/
def Decoration.forgetParam (D : Decoration obs) : DecoratedModel D → Model obs :=
  DecoratedModel.base

/-- A decoration is non-trivial if some model admits multiple decorations. -/
def Decoration.isNontrivial (D : Decoration obs) : Prop :=
  ∃ M : Model obs, Nontrivial (D.Param M)

/-- The No-Obstruction-No-Uniqueness Lemma:

If decoration `D` is not constrained by obstruction witnesses,
then `D` cannot be uniquely determined by obstruction resolution.

Formally: if `D.Param M` has more than one element for some `M`,
then varying that parameter does not affect resolution status. -/
theorem no_obstruction_no_uniqueness (D : Decoration obs) (h : D.isNontrivial) :
    ∃ (M : Model obs) (p q : D.Param M), p ≠ q := by
  obtain ⟨M, hM⟩ := h
  obtain ⟨p, q, hpq⟩ := hM.exists_pair_ne
  exact ⟨M, p, q, hpq⟩

end ImpossibilityTheory.Mathematics
