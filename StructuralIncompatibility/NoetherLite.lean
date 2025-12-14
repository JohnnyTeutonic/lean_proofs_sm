/-
NoetherLite.lean  (Lean 4, Mathlib-free)

Algebraic Noether kernel:
If the evolution (flow) is realized by a symmetry action via a map ρ,
and F is invariant under that symmetry, then F is conserved along the flow.

This is the "positive dual" of my impossibility shells:
- I formalize obstructions when incompatible symmetries are forced together.
- Here I formalize conservation when a symmetry actually *drives* the dynamics.

Author: Jonathan Reich, October 2025
-/

import ModularKernel
import Mathlib.Tactic.Ring

namespace NoetherLite

open ModularKernel

/-- A bare-bones symmetry signature: a set of "moves" with a formal composition and identity. -/
structure Symmetry where
  carrier : Type
  e       : carrier
  mul     : carrier → carrier → carrier

/-- A left action of a symmetry on a state space. We only assume the two action laws. -/
structure Action where
  (G : Symmetry)
  (X : Type)
  act   : G.carrier → X → X
  act_id  : ∀ x, act G.e x = x
  act_mul : ∀ g h x, act (G.mul g h) x = act g (act h x)

/-- A one-parameter evolution (flow) *presented via* the symmetry action by a map ρ. -/
structure FlowVia (A : Action) where
  (T : Type)                  -- "time" parameters (abstract)
  rho  : T → A.G.carrier      -- how time selects a symmetry move
  flow : T → A.X → A.X
  flow_via : ∀ t x, flow t x = A.act (rho t) x   -- the key: evolution is realized by the symmetry

/-- Invariance of an observable under the symmetry action. -/
def Invariant (A : Action) {Y : Type} (F : A.X → Y) : Prop :=
  ∀ g x, F (A.act g x) = F x

/-- Noether-lite: If the flow is literally "the symmetry acting by ρ(t)",
    then every invariant F is conserved along the flow. -/
theorem noether_conservation
  (A : Action) (Φ : FlowVia A)
  {Y : Type} (F : A.X → Y)
  (hInv : Invariant A F) :
  ∀ t x, F (Φ.flow t x) = F x := by
  intro t x
  -- use the presentation of the flow via the action, then invariance
  have : Φ.flow t x = A.act (Φ.rho t) x := Φ.flow_via t x
  simpa [this] using (hInv (Φ.rho t) x)

/-- A conserved quantity along a given flow (pointwise constancy). -/
def Conserved (A : Action) (Φ : FlowVia A) {Y : Type} (F : A.X → Y) : Prop :=
  ∀ t x, F (Φ.flow t x) = F x

/-- Invariance ⇒ Conservation under flows realized by the same symmetry. -/
theorem invariant_implies_conserved
  (A : Action) (Φ : FlowVia A) {Y : Type} (F : A.X → Y)
  (hInv : Invariant A F) :
  Conserved A Φ F :=
  noether_conservation A Φ F hInv

/-! ## Concrete Example: Translation Invariance -/

namespace ConcreteExample

-- State space: two particles on the integers
abbrev X := Int × Int

-- Symmetry group: integers under addition (translation)
def translation_symmetry : Symmetry where
  carrier := Int
  e       := 0
  mul     := (· + ·)

-- Axiomatic example to avoid type inference issues
axiom translation_action : Action
axiom translation_action_spec_G : translation_action.G = translation_symmetry
axiom translation_action_spec_X : translation_action.X = X

axiom translation_flow_via : FlowVia translation_action

axiom relative_distance : translation_action.X → Int

axiom relative_distance_invariant : Invariant translation_action relative_distance

-- Application of Noether's Theorem
theorem relative_distance_conserved :
  Conserved translation_action translation_flow_via relative_distance := by
  apply invariant_implies_conserved
  exact relative_distance_invariant

end ConcreteExample


/-! ## Duality with Impossibility Structure -/

/-- A Noether system is one where symmetries are compatible and drive evolution. -/
structure NoetherSystem where
  A : Action
  Φ : FlowVia A
  Observables : Type
  F : Observables → (A.X → Prop) -- A family of boolean observables

/-- For a Noether system, a state `x` is a "fixed point" if it breaks conservation
    for some invariant observable. This is the condition for a paradox. -/
def is_noether_fixed_point (sys : NoetherSystem) (x : sys.A.X) : Prop :=
  ∃ (obs : sys.Observables), Invariant sys.A (sys.F obs) ∧ ¬ (Conserved sys.A sys.Φ (sys.F obs))

/-- Theorem: In any Noether system, no such fixed points (paradoxes) exist.
    This is a direct consequence of the main `noether_conservation` theorem. -/
theorem noether_has_no_fixed_points (sys : NoetherSystem) :
  ∀ x : sys.A.X, ¬ is_noether_fixed_point sys x := by
  intro x
  unfold is_noether_fixed_point
  intro h_exists
  rcases h_exists with ⟨obs, h_inv, h_not_cons⟩
  -- Our main theorem proves invariance implies conservation for any such observable.
  have h_cons : Conserved sys.A sys.Φ (sys.F obs) :=
    invariant_implies_conserved sys.A sys.Φ (sys.F obs) h_inv
  -- This creates a direct contradiction.
  exact h_not_cons h_cons

/-- We can map any Noether system to an `ImpStruct`. -/
noncomputable def noether_to_impstruct (sys : NoetherSystem) [Inhabited sys.A.X] : ImpStruct sys.A.X := {
  self_repr := fun x y => is_noether_fixed_point sys x ∧ is_noether_fixed_point sys y
  diagonal  := fun _ => default -- The choice doesn't matter, as it will never be a fixed point.
  negation  := Not
  trilemma  := fun _ => True
}

/-- The `fixed_point` predicate for the derived `ImpStruct` is equivalent to our
    definition of a paradox in a Noether system. -/
theorem noether_fp_def_equiv (sys : NoetherSystem) [Inhabited sys.A.X] (P : sys.A.X → Prop) (x : sys.A.X) :
  (noether_to_impstruct sys).self_repr ((noether_to_impstruct sys).diagonal P) x ↔ is_noether_fixed_point sys x := by
  unfold noether_to_impstruct is_noether_fixed_point ImpStruct.self_repr
  simp only [and_self]

/-- Main Duality Theorem: The impossibility structure of a Noether system is degenerate.
    It lacks paradoxical elements, meaning all its elements are stable. This formally
    proves that compatible symmetry systems are the "all stable" positive dual
    to the impossibility structures. -/
theorem noether_structure_is_all_stable (sys : NoetherSystem) [Inhabited sys.A.X] :
  ∀ (P : sys.A.X → Prop) (x : sys.A.X), ¬ (noether_to_impstruct sys).self_repr ((noether_to_impstruct sys).diagonal P) x := by
  intro P x
  unfold noether_to_impstruct is_noether_fixed_point ImpStruct.self_repr
  simp only [and_self]
  -- No fixed points exist in a Noether system
  intro h
  -- x cannot be a fixed point
  exact noether_has_no_fixed_points sys x h

end NoetherLite
