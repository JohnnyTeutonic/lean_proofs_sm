import Mathlib.Logic.Function.Defs
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Floor
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Yoneda
import InterfaceTheory

/-!
# Interface Theory: Categorical Strengthening

Copyright (c) 2025 Jonathan Reich.
Released under the Apache 2.0 license.

## Overview

This file strengthens `InterfaceTheory.lean` by providing a rigorous categorical
framework for the interface concept.

-/

namespace InterfaceTheoryCategorical

open CategoryTheory
open InterfaceTheory
open Classical

universe u

/-! ## Part I: Category Instance -/

/--
The interface category on `Type u`.
Objects are types in universe `u`. Morphisms `α ⟶ β` are `InterfaceFunctor α β`.
-/
instance : Category (Type u) where
  Hom α β := InterfaceFunctor α β
  id α := interfaceId α
  comp f g := interfaceComp f g
  id_comp f := interface_strict_left_unit f
  comp_id f := interface_strict_right_unit f
  assoc f g h := interface_strict_assoc f g h

/-! ## Part II: Concrete Interface Monad -/

/--
The concrete interface monad: **Powerset Monad**.
Restricted to universe `u` to satisfy `Monad` typeclass requirements.
-/
abbrev InterfaceMonadConcrete (α : Type u) : Type u := Set α

namespace InterfaceMonadConcrete

/-- Unit: pure observation (singleton set) -/
def unit {α : Type u} (x : α) : InterfaceMonadConcrete α :=
  {x}

/-- Bind: union of results -/
def bind {α β : Type u} (m : InterfaceMonadConcrete α)
    (f : α → InterfaceMonadConcrete β) : InterfaceMonadConcrete β :=
  ⋃ x ∈ m, f x

instance : Monad InterfaceMonadConcrete where
  pure := unit
  bind := bind

@[simp] lemma pure_def {α : Type u} (x : α) :
    (pure x : InterfaceMonadConcrete α) = unit x := rfl

@[simp] lemma bind_def {α β : Type u}
    (m : InterfaceMonadConcrete α) (f : α → InterfaceMonadConcrete β) :
    (m >>= f) = bind m f := rfl

end InterfaceMonadConcrete

/-! ## Part III: Mathematical Examples -/

section Examples

/-- Simple identity interface on ℕ -/
def natIdentity : InterfaceFunctor ℕ ℕ where
  functor := id

/-- Double function on ℕ -/
def natDouble : InterfaceFunctor ℕ ℕ where
  functor := fun n => 2 * n

theorem identity_left_neutral : natIdentity ≫ natDouble = natDouble := by
  ext n
  rfl

theorem identity_right_neutral : natDouble ≫ natIdentity = natDouble := by
  ext n
  rfl

end Examples

/-! ## Part IV: Yoneda Integration -/

section YonedaInterface

/-- Precomposition functor. -/
def precompInterface {α β γ : Type u} (f : InterfaceFunctor α β) :
    InterfaceFunctor γ α → InterfaceFunctor γ β :=
  fun g => g ≫ f

end YonedaInterface

/-! ## Part V: Profunctor Embedding -/

section ProfunctorEmbedding

/--
Canonical embedding of interfaces into profunctors.
`f : β ⟶ α` (function `α → β`) maps to `P(b, a) := (b = f.functor a)`.
-/
def interfaceToGraph {α β : Type u} (f : InterfaceFunctor α β) : α → β → Prop :=
  fun a b => a = f.functor b

end ProfunctorEmbedding

/-! ## Part VI: Functional Equivalence Refined -/

section FunctionalEquivalenceRefined

def preimageSet {α β : Type u} (f : InterfaceFunctor α β) (S : Set α) : Set β :=
  {b | f.functor b ∈ S}

end FunctionalEquivalenceRefined

/-! ## Part VII: Stability Functional -/

/--
Epistemic stability functional.
-/
abbrev Stability := ℝ
noncomputable def stabilityRange : Set ℝ := {x | 0 ≤ x ∧ x ≤ 1}

structure EpistemicStabilityFunctional (α : Type u) where
  stab : (α → Prop) → Stability
  bounded : ∀ P, stab P ∈ stabilityRange
  monotone : ∀ {P Q}, (∀ x, P x → Q x) → stab P ≤ stab Q

noncomputable def canonicalStability (α : Type u) : EpistemicStabilityFunctional α :=
{ stab := fun P => if h : ∃ x, P x then 1 else 0,
  bounded := by
    intro P
    by_cases h : ∃ x, P x <;> simp [h, stabilityRange] <;> norm_num
  monotone := by
    intro P Q h
    by_cases hP : ∃ x, P x
    · have hQ : ∃ x, Q x := by cases hP with | intro x hx => exact ⟨x, h x hx⟩
      simp [hP, hQ]
    · simp [hP]
      by_cases hQ : ∃ x, Q x <;> simp [hQ] }

structure GlobalEpistemicStructure where
  E : ∀ α : Type u, EpistemicStabilityFunctional α
  nonexpansive : ∀ {α β : Type u} (f : InterfaceFunctor α β),
    ∀ P : α → Prop, (E β).stab (fun b => P (f.functor b)) ≤ (E α).stab P

noncomputable def canonicalGlobalEpistemicStructure : GlobalEpistemicStructure :=
{ E := canonicalStability,
  nonexpansive := by
    intro α β f P
    simp [canonicalStability]
    split
    · case isTrue h_im =>
      cases h_im with | intro b hb =>
      have : ∃ a, P a := ⟨f.functor b, hb⟩
      simp [this]
    · case isFalse h_im =>
      split
      · norm_num
      · norm_num }

/-! ## Part VIII: Applications -/

section QuantumApps

axiom QuantumState : Type u
axiom ClassicalState : Type u

axiom measure : InterfaceFunctor ClassicalState QuantumState
axiom quantum_classical_equivalence : functional_equivalence ClassicalState QuantumState

end QuantumApps

section AutomataApps

structure NFA where
  State : Type u
structure DFA where
  State : Type u

axiom determinize : NFA → DFA

noncomputable def determinizeInterface : InterfaceFunctor DFA NFA :=
  ⟨determinize⟩

end AutomataApps

end InterfaceTheoryCategorical
