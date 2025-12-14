/-
Canonical Tests for Impossibility Quotient Isomorphism
 
Golden tests demonstrating that quotient_to_binary_unique correctly
determines all structure-preserving maps to BinaryImp.

Author: Jonathan Reich
Date: November 2025
-/

import ImpossibilityQuotientIsomorphism
import GodelAxiomsComplete
import HaltingProblem_Real
import TarskiUndefinability

namespace CanonicalTests

open ImpossibilityQuotient
open ModularKernel
open BinaryImp

/-! ## Test 1: Identity Map to Binary is quotient_to_binary -/

/-- Any identity-like map that preserves structure must equal quotient_to_binary -/
example {S : Type*} (I_S : ImpStruct S) :
    ∀ (f : ImpQuotient S I_S → BinaryImp),
    (∀ q, quotient_to_binary I_S q = paradox ↔ f q = paradox) →
    f = quotient_to_binary I_S :=
  quotient_to_binary_unique I_S

/-! ## Test 2: Gödel Quotient to Binary is Canonical -/

/-- The map from Gödel quotient to BinaryImp is uniquely determined -/
example :
    ∀ (f g : ImpQuotient ℕ GodelComplete.godel_impstruct → BinaryImp),
    (∀ q, quotient_to_binary GodelComplete.godel_impstruct q = paradox ↔ f q = paradox) →
    (∀ q, quotient_to_binary GodelComplete.godel_impstruct q = paradox ↔ g q = paradox) →
    f = g := by
  intro f g hf hg
  apply binary_is_terminal GodelComplete.godel_impstruct f g hf hg

/-! ## Test 3: Halting Quotient to Binary is Canonical -/

/-- The map from Halting quotient to BinaryImp is uniquely determined -/
example :
    ∀ (f g : ImpQuotient HaltingProblem_real.HaltingInstance 
                        HaltingProblem_real.halting_ImpStruct → BinaryImp),
    (∀ q, quotient_to_binary HaltingProblem_real.halting_ImpStruct q = paradox ↔ f q = paradox) →
    (∀ q, quotient_to_binary HaltingProblem_real.halting_ImpStruct q = paradox ↔ g q = paradox) →
    f = g := by
  intro f g hf hg
  apply binary_is_terminal HaltingProblem_real.halting_ImpStruct f g hf hg

/-! ## Test 4: Tarski Quotient to Binary is Canonical -/

/-- The map from Tarski quotient to BinaryImp is uniquely determined -/
example :
    ∀ (f g : ImpQuotient GodelComplete.Formula TarskiUndefinability.tarski_impstruct → BinaryImp),
    (∀ q, quotient_to_binary TarskiUndefinability.tarski_impstruct q = paradox ↔ f q = paradox) →
    (∀ q, quotient_to_binary TarskiUndefinability.tarski_impstruct q = paradox ↔ g q = paradox) →
    f = g := by
  intro f g hf hg
  apply binary_is_terminal TarskiUndefinability.tarski_impstruct f g hf hg

/-! ## Test 5: Morphism Composition Preserves Uniqueness -/

/-- Composing the canonical morphism with identity yields the same morphism -/
example {S : Type*} (I_S : ImpStruct S) :
    ImpQuotientMorphism.comp (ImpQuotientMorphism.id I_S) (to_binary_morphism I_S) = 
    to_binary_morphism I_S := by
  apply ImpQuotientMorphism.id_comp

/-- The canonical morphism composed with identity on the right is unchanged -/
example {S : Type*} (I_S : ImpStruct S) :
    ImpQuotientMorphism.comp (to_binary_morphism I_S) (ImpQuotientMorphism.id canonical_binary_impstruct) = 
    to_binary_morphism I_S := by
  apply ImpQuotientMorphism.comp_id

/-! ## Test 6: Terminal Object Uniqueness -/

/-- Any morphism to BinaryImp equals the canonical morphism -/
example {S : Type*} (I_S : ImpStruct S) 
    (f : ImpQuotientMorphism I_S canonical_binary_impstruct) :
    f = to_binary_morphism I_S := by
  apply binary_terminal

/-! ## Test 7: Quotient Preserves Structure -/

/-- quotient_to_binary sends stable elements to stable -/
example {S : Type*} (I_S : ImpStruct S) (q : ImpQuotient S I_S) :
    quotient_to_binary I_S q = stable ↔ quotient_to_binary I_S q ≠ paradox := by
  constructor
  · intro h
    rw [h]
    simp
  · intro h
    cases hq : quotient_to_binary I_S q
    · rfl
    · contradiction

/-- quotient_to_binary sends paradoxical elements to paradox -/
example {S : Type*} (I_S : ImpStruct S) (q : ImpQuotient S I_S) :
    quotient_to_binary I_S q = paradox ↔ quotient_to_binary I_S q ≠ stable := by
  constructor
  · intro h
    rw [h]
    simp
  · intro h
    cases hq : quotient_to_binary I_S q
    · contradiction
    · rfl

/-! ## Test 8: Functoriality of quotient_to_binary -/

/-- quotient_to_binary respects the quotient equivalence -/
example {S : Type*} (I_S : ImpStruct S) (s₁ s₂ : S)
    (h : I_S.fixed_point s₁ ↔ I_S.fixed_point s₂) :
    quotient_to_binary I_S (Quotient.mk _ s₁) = quotient_to_binary I_S (Quotient.mk _ s₂) := by
  unfold quotient_to_binary
  simp only [Quotient.lift_mk]
  by_cases h1 : I_S.fixed_point s₁
  · have h2 := h.mp h1
    simp [h1, h2]
  · have h2 := mt h.mpr h1
    simp [h1, h2]

/-! ## Test 9: Category Laws Hold -/

/-- Morphism composition is associative (concrete instance) -/
example {S T U V : Type*}
    {I_S : ImpStruct S} {I_T : ImpStruct T} {I_U : ImpStruct U} {I_V : ImpStruct V}
    (f : ImpQuotientMorphism I_S I_T) 
    (g : ImpQuotientMorphism I_T I_U)
    (h : ImpQuotientMorphism I_U I_V) :
    ImpQuotientMorphism.comp (ImpQuotientMorphism.comp f g) h = 
    ImpQuotientMorphism.comp f (ImpQuotientMorphism.comp g h) := by
  apply ImpQuotientMorphism.comp_assoc

/-! ## Test 10: Push Simplification -/

/-- Push simplifies correctly with identity -/
example {S : Type*} (P : S → Prop) :
    Push (fun x => x) P = P := by
  simp [Push]

/-- Push composes correctly -/
example {S T U : Type*} (g : T → U) (f : S → T) (P : S → Prop) :
    Push (g ∘ f) P = Push g (Push f P) := by
  simp [Push]

end CanonicalTests

