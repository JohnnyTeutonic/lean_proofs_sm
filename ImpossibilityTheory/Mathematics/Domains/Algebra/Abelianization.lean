/-
  Domains/Algebra/Abelianization.lean

  Second domain instantiation:
  Grp ⟶ CommGrp (abelianization)
  as resolution of the "non-commutativity" obstruction.

  This is a cleaner example than GroupCompletion because mathlib
  already provides the categorical functor and adjunction!
-/

import Mathlib.Algebra.Category.Grp.Adjunctions
import Mathlib.CategoryTheory.Adjunction.Basic

namespace ImpossibilityTheory.Mathematics.Domains.Algebra

open CategoryTheory

universe u

/-!
## The "non-commutativity" obstruction

The witness type is: the group is commutative (∀ x y, x * y = y * x).
Resolution means the group is already abelian.
-/

/-- Witness type for "commutativity": a proof that the group operation commutes. -/
structure CommutativeWitness (G : GrpCat.{u}) : Prop where
  comm : ∀ x y : G, x * y = y * x

/-- The inclusion functor `CommGrp ⥤ Grp`. -/
abbrev inclCommGrp : CommGrpCat.{u} ⥤ GrpCat.{u} := forget₂ CommGrpCat GrpCat

/-!
## Soundness: Commutative groups are obstruction-free
-/

/-- Any commutative group, viewed as a group, satisfies the commutativity witness.

Proof: CommGroup has commutative multiplication by definition. -/
theorem sound_commGrp (Y : CommGrpCat.{u}) : CommutativeWitness (inclCommGrp.obj Y) where
  comm x y := by
    -- Y is a CommGroup, so multiplication commutes
    convert @mul_comm Y _ x y

/-!
## Completeness: Commutative groups are exactly the obstruction-free groups
-/

/-- If a group is commutative, it's in the essential image of CommGrp ⥤ Grp.

This is the "completeness" direction: obstruction-free objects come from the resolved world. -/
theorem complete_grp (X : GrpCat.{u}) (hX : CommutativeWitness X) :
    ∃ (Y : CommGrpCat.{u}), Nonempty (inclCommGrp.obj Y ≅ X) := by
  -- Step 1: upgrade X's structure to a CommGroup using the commutativity witness
  letI : CommGroup X := { (inferInstance : Group X) with mul_comm := hX.comm }
  -- Step 2: bundle it as an object of CommGrpCat
  refine ⟨CommGrpCat.of X, ⟨?_⟩⟩
  -- underlying GrpCat is definitionally X
  exact Iso.refl _

/-!
## The Abelianization Functor and Adjunction

Unlike GroupCompletion, mathlib already provides the categorical wrapper!
  - `GrpCat.abelianize : GrpCat ⥤ CommGrpCat`
  - `GrpCat.abelianizeAdj : abelianize ⊣ forget₂ CommGrpCat GrpCat`
-/

/-- The abelianization functor from mathlib. -/
noncomputable abbrev abelianizeFunctor : GrpCat.{u} ⥤ CommGrpCat.{u} :=
  GrpCat.abelianize

/-- The adjunction: abelianize ⊣ forget₂ CommGrpCat GrpCat, from mathlib. -/
noncomputable abbrev abelianize_adj : abelianizeFunctor ⊣ inclCommGrp :=
  GrpCat.abelianizeAdj

/-!
## Summary

This demonstrates the same pattern as GroupCompletion:
1. **Obstruction**: "non-commutativity" — resolved when ∀ x y, x * y = y * x
2. **Soundness**: Every CommGrp resolves this (mul_comm)
3. **Completeness**: If a Grp resolves it, it's essentially a CommGrp
4. **Solution operator**: Abelianization functor G ↦ G/[G,G] with universal property

Key difference: mathlib already provides `abelianize` and `abelianizeAdj`,
so no axioms needed!
-/

end ImpossibilityTheory.Mathematics.Domains.Algebra
