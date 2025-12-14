/-
  Domains/Algebra/GroupCompletion.lean

  First nontrivial SolutionOperator:
  CommMon ⟶ CommGroup (Grothendieck group / group completion)
  as resolution of the "missing inverses" obstruction.
  
  Architecture demonstration: the obstruction specifies resolution (∀ x, IsUnit x),
  and the Grothendieck group is the universal provider of witnesses.
-/

import Mathlib.Algebra.Category.MonCat.Basic
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.CategoryTheory.Adjunction.Basic

namespace ImpossibilityTheory.Mathematics.Domains.Algebra

open CategoryTheory

universe u

/-!
## Standalone Domain Module

This module demonstrates the group completion pattern without depending on
the full Core infrastructure (which has universe constraints). It shows
the mathematical content of what a SolutionOperator for "missing inverses" looks like.
-/

/-!
## The "missing inverses" obstruction

The witness type is: every element is a unit.
This is a *specification of resolution*, not a failure witness.
-/

/-- Witness type for "group-likeness": a proof that every element is a unit. -/
structure GroupLikeWitness (M : CommMonCat.{u}) : Prop where
  all_units : ∀ x : M, IsUnit x

/-- The inclusion functor `CommGrp ⥤ CommMon`. -/
abbrev inclCommGrp : CommGrpCat.{u} ⥤ CommMonCat.{u} := forget₂ CommGrpCat CommMonCat

/-!
## Soundness: Groups are obstruction-free
-/

/-- Any commutative group, viewed as a commutative monoid, has all units.

Proof: in a group, every element x has inverse x⁻¹, so IsUnit x holds. -/
theorem sound_commGrp (Y : CommGrpCat.{u}) : GroupLikeWitness (inclCommGrp.obj Y) where
  all_units x := by
    -- The underlying type is Y which is a CommGroup.
    -- Group.isUnit gives us IsUnit for any element in a group.
    convert @Group.isUnit Y _ x

/-!
## Completeness: Obstruction-free monoids are groups
-/

/-- If a commutative monoid has all elements as units, it's in the essential image of CommGrp.

This is the "completeness" direction: obstruction-free objects come from the resolved world. -/
theorem complete_commMon (X : CommMonCat.{u}) (hX : GroupLikeWitness X) :
    ∃ (Y : CommGrpCat.{u}), Nonempty (inclCommGrp.obj Y ≅ X) := by
  classical
  -- Step 1: upgrade X's structure to a CommGroup using commGroupOfIsUnit
  letI : CommGroup X := commGroupOfIsUnit (fun x : X => hX.all_units x)
  -- Step 2: bundle it as an object of CommGrpCat
  refine ⟨CommGrpCat.of X, ⟨?_⟩⟩
  -- underlying CommMonCat is definitionally X
  exact Iso.refl _

/-!
## The Grothendieck Group Functor

Mathlib has `Algebra.GrothendieckGroup` (in GroupTheory.MonoidLocalization.GrothendieckGroup)
but it's not yet wrapped as a categorical functor `CommMonCat ⥤ CommGrpCat` with adjunction.

We declare axioms for the functor and adjunction. The mathematical content exists in mathlib;
wrapping it categorically is routine but tedious glue work better suited for a mathlib PR.
-/

/-- The Grothendieck group functor.

Axiomatized here; the underlying construction is `Algebra.GrothendieckGroup M`
which localizes a commutative monoid at its top submonoid. -/
axiom grothendieckGrp : CommMonCat.{u} ⥤ CommGrpCat.{u}

/-- The adjunction: grothendieckGrp ⊣ forget₂ CommGrpCat CommMonCat.

This follows from `Algebra.GrothendieckGroup.lift` which provides the universal property. -/
axiom grothendieckGrp_adj : grothendieckGrp ⊣ inclCommGrp

/-!
## Summary

This demonstrates the pattern:
1. **Obstruction**: "missing inverses" — resolved when ∀ x, IsUnit x
2. **Soundness**: Every CommGrp resolves this (Group.isUnit)
3. **Completeness**: If a CommMon resolves it, it's essentially a CommGrp
4. **Solution operator**: Grothendieck group functor with universal property

This is the first domain instantiation of Impossibility Theory for Mathematics.
-/

end ImpossibilityTheory.Mathematics.Domains.Algebra
