import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

/-!
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license.

# Algebraic Incompatibility Between Faithful Time Evolution and Diffeomorphism Covariance

## Main result

We give a machine-verified algebraic obstruction relevant to quantum gravity:
faithful one-parameter unitary time evolution (Stone-like structure) is incompatible
with equivariance under all time reparametrisations (full diffeomorphism covariance).

## Key idea

If `U : (ℝ, +) → End(H)` is faithful, any intertwiner implementing a reparametrisation `ρ`
forces `ρ` to be additive. Since diffeomorphisms include non-additive maps (e.g. `t ↦ t^3`),
full covariance yields a contradiction.

No topology, differential geometry, or quantum field theory is required — only algebra.

-/

namespace QuantumGravityTheorems

/-! ## Core abstractions (purely algebraic) -/

/-- Minimal algebraic one-parameter “unitary” action by function composition.

We model a homomorphism `U : ℝ → (H → H)` with the group law
`U (s + t) = U s ∘ U t`, identity `U 0 = id`, and **faithfulness** at the
parameter level: `U s = U t → s = t`.

No topology/analysis is used.
-/
structure OneParamUnitary (H : Type*) where
  U         : ℝ → (H → H)
  idU       : U 0 = id
  group_law : ∀ s t, U (s + t) = (U s) ∘ (U t)
  faithful  : ∀ {s t}, U s = U t → s = t

attribute [simp] OneParamUnitary.idU

/-- Convenience lemma for readability in calc chains. -/
lemma OneParamUnitary.U_add {H : Type*} (U : OneParamUnitary H) (s t : ℝ) :
    U.U (s + t) = U.U s ∘ U.U t :=
  U.group_law s t

/-- A time reparametrisation with the single constraint `ρ(0) = 0`. -/
structure TimeReparam where
  ρ    : ℝ → ℝ
  fix0 : ρ 0 = 0

/-- Equivariance under a time reparametrisation `ρ` via an invertible intertwiner `W`. -/
def equivariant_under {H : Type*}
    (U : OneParamUnitary H) (ρ : TimeReparam) : Prop :=
  ∃ (W : Equiv H H), ∀ t, (W ∘ U.U t) = (U.U (ρ.ρ t) ∘ W)

/-! ## Surjective right-cancellation helper -/

/-- If `(f ∘ W) = (g ∘ W)` and `W` is surjective, then `f = g`.

This factors the cancellation step used in `additive_from_equivariance`.
-/
lemma cancel_right_surjective {H : Type*}
    {f g : H → H} {W : H → H} (h : f ∘ W = g ∘ W) (hW : Function.Surjective W) :
    f = g := by
  funext x
  rcases hW x with ⟨y, rfl⟩
  simpa [Function.comp] using congrArg (fun k => k y) h

/-! ## Intertwiner ⇒ additivity -/

/-- If `U` is faithful and there is an intertwiner implementing `ρ`, then `ρ` is additive. -/
lemma additive_from_equivariance {H : Type*}
    (U : OneParamUnitary H) (ρ : TimeReparam)
    (heq : equivariant_under U ρ) :
    ∀ s t, ρ.ρ (s + t) = ρ.ρ s + ρ.ρ t := by
  rcases heq with ⟨W, hW⟩
  intro s t
  -- Intertwining at s+t
  have h1 : (W ∘ U.U (s + t)) = (U.U (ρ.ρ (s + t)) ∘ W) := by simpa using hW (s + t)
  -- Compute the same LHS via group law and two-step intertwining
  have hL : (W ∘ U.U (s + t)) = (U.U (ρ.ρ s) ∘ U.U (ρ.ρ t) ∘ W) := by
    calc
      (W ∘ U.U (s + t))
          = (W ∘ (U.U s ∘ U.U t)) := by simp [U.U_add s t]
      _   = ((W ∘ U.U s) ∘ U.U t) := rfl
      _   = ((U.U (ρ.ρ s) ∘ W) ∘ U.U t) := by rw [hW s]
      _   = (U.U (ρ.ρ s) ∘ (W ∘ U.U t)) := rfl
      _   = (U.U (ρ.ρ s) ∘ (U.U (ρ.ρ t) ∘ W)) := by rw [hW t]
      _   = (U.U (ρ.ρ s) ∘ U.U (ρ.ρ t) ∘ W) := rfl
  -- Compare RHS; rewrite to `(f ∘ W) = (g ∘ W)` form
  have hR : (U.U (ρ.ρ (s + t)) ∘ W) = (U.U (ρ.ρ s + ρ.ρ t) ∘ W) := by
    calc
      (U.U (ρ.ρ (s + t)) ∘ W)
          = (W ∘ U.U (s + t)) := h1.symm
      _   = (U.U (ρ.ρ s) ∘ U.U (ρ.ρ t) ∘ W) := hL
      _   = ((U.U (ρ.ρ s) ∘ U.U (ρ.ρ t)) ∘ W) := rfl
      _   = (U.U (ρ.ρ s + ρ.ρ t) ∘ W) := by
            simp [U.U_add (ρ.ρ s) (ρ.ρ t)]
  -- Surjective right-cancellation (using Equiv.surjective) gives equality of endomorphisms
  have hEndo : U.U (ρ.ρ (s + t)) = U.U (ρ.ρ s + ρ.ρ t) :=
    cancel_right_surjective hR (Equiv.surjective W)
  -- Faithfulness of parameters yields additivity
  exact U.faithful hEndo

/-! ## The obstruction theorem -/

/-- There is no equivariance under *all* time reparametrisations fixing `0`.

Pick the nonlinear cubic `ρ(t) = t^3` and use `additive_from_equivariance`.
-/
theorem no_full_time_reparam_equivariance {H : Type*}
    (U : OneParamUnitary H) :
    ¬ (∀ (ρ : TimeReparam), equivariant_under U ρ) := by
  intro hall
  -- Choose a nonlinear reparametrisation
  let rho : TimeReparam := { ρ := fun t => t ^ 3, fix0 := by simp }
  have hρ := hall rho
  have addρ := additive_from_equivariance U rho hρ
  -- Evaluate additivity at s = t = 1: ρ(2) = ρ(1) + ρ(1), i.e., 8 = 2
  have h_add : rho.ρ (1 + 1) = rho.ρ 1 + rho.ρ 1 := addρ 1 1
  have hL : rho.ρ (1 + 1) = 8 := by norm_num [rho]
  have hR : rho.ρ 1 + rho.ρ 1 = 2 := by norm_num [rho]
  have : (8 : ℝ) = 2 := by
    calc
      (8 : ℝ) = rho.ρ (1 + 1) := hL.symm
      _ = rho.ρ 1 + rho.ρ 1 := h_add
      _ = 2 := hR
  -- Contradiction
  norm_num at this

/-! ## Legacy compatibility layer (axiom-free, decorative Hilbert shell) -/

/-- Abstract “Hilbert space” shell. We do not use analysis; purely a placeholder. -/
class HilbertSpace (H : Type*) where
  inner : H → H → ℂ
  complete : True

/-- Legacy unitary group structure as a 1-parameter action on `H`. -/
structure UnitaryGroup (H : Type*) [HilbertSpace H] where
  U         : ℝ → (H → H)
  idU       : U 0 = id
  group_law : ∀ t₁ t₂, U (t₁ + t₂) = U t₁ ∘ U t₂
  faithful  : ∀ {s t}, U s = U t → s = t

attribute [simp] UnitaryGroup.idU

/-- Convert `UnitaryGroup` to the core `OneParamUnitary`. -/
def UnitaryGroup.toOneParamUnitary {H : Type*} [HilbertSpace H] (U : UnitaryGroup H) :
    OneParamUnitary H where
  U := U.U
  idU := U.idU
  group_law := U.group_law
  faithful := U.faithful

/-! ## Implementations and functorial formulations -/

/-- A ρ-implementation for `U`: reparametrisation acts by (invertible) conjugation,
possibly depending on a background parameter `m : M`. -/
structure ReparamImplementation (M H : Type*) (U : OneParamUnitary H) :=
  (ρ  : TimeReparam)
  (W  : M → Equiv H H)
  (intertwine : ∀ m t, (W m ∘ U.U t) = (U.U (ρ.ρ t) ∘ W m))

/-- “All reparametrisations are implemented” (there exists some witness `m` and intertwiner). -/
def AllReparamsImplemented {H M : Type*} [HilbertSpace H]
    (U : UnitaryGroup H) : Prop :=
  ∀ (ρ : TimeReparam), ∃ (m : M) (W : Equiv H H),
    ∀ t, (W ∘ U.U t) = (U.U (ρ.ρ t) ∘ W)

/-- From an implementation witness, obtain equivariance for the core action. -/
lemma implemented_reparams_give_equivariance {H M : Type*} [HilbertSpace H]
    (U : UnitaryGroup H) :
    AllReparamsImplemented (H:=H) (M:=M) U →
    ∀ ρ : TimeReparam, equivariant_under U.toOneParamUnitary ρ := by
  intro hall ρ
  rcases hall ρ with ⟨m, W, hW⟩
  refine ⟨W, ?_⟩
  intro t
  simpa using hW t

/-- **Legacy incompatibility (axiom-free).**

If every time reparametrisation fixing `0` is implemented by an invertible
state map (for some background `m : M`), then equivariance holds for **all** `ρ`,
contradicting the core obstruction when the 1-parameter action is faithful.
-/
theorem stone_von_neumann_diffeo_incompatibility
    {H M : Type*} [HilbertSpace H] :
    ∀ (U : UnitaryGroup H),
      ¬ AllReparamsImplemented (H:=H) (M:=M) U := by
  intro U
  -- If all reparams were implemented, we'd get equivariance for all ρ:
  intro hall
  have hall_equiv : ∀ ρ : TimeReparam, equivariant_under U.toOneParamUnitary ρ :=
    implemented_reparams_give_equivariance (H:=H) (M:=M) U hall
  -- But the core theorem rules that out:
  exact no_full_time_reparam_equivariance U.toOneParamUnitary hall_equiv

/-! ## Functorial No-Go (light categorical shell, no axioms)

We model a “Diff→Hilb” functor only through the *property we need*: for each `ρ`,
it yields an intertwiner implementing `ρ` on the underlying 1-parameter action.
No category theory library or axioms required.
-/

/-- A *clean* formulation of “`F` preserves all reparametrisations for `U`”. -/
def FunctorPreservesAllReparams {H : Type*} [HilbertSpace H]
    (U : UnitaryGroup H) (F : Type*) : Prop :=
  ∀ ρ : TimeReparam, ∃ W : Equiv H H, ∀ t, (W ∘ U.U t) = (U.U (ρ.ρ t) ∘ W)

/-- Functorial no-go: if some `F` preserves all reparametrisations for a faithful `U`,
we obtain the same contradiction as before. -/
theorem diff_to_hilb_no_go {H : Type*} [HilbertSpace H]
    (U : UnitaryGroup H) :
    ¬ ∃ F : Type*, FunctorPreservesAllReparams U F := by
  intro h
  rcases h with ⟨F, hpres⟩
  -- Convert the functorial preservation hypothesis into "equivariance for all ρ"
  have hall : ∀ ρ : TimeReparam, equivariant_under U.toOneParamUnitary ρ := by
    intro ρ
    rcases hpres ρ with ⟨W, hW⟩
    exact ⟨W, by intro t; simpa using hW t⟩
  -- Contradiction with the core algebraic obstruction
  exact no_full_time_reparam_equivariance U.toOneParamUnitary hall

/-! ## Remarks and generalizations

- Structural, universe-agnostic: all proofs are purely algebraic; no analytic,
  topological, or set-theoretic machinery is used.
- Categorical reading: view `U : (ℝ, +) → End(H)` as a faithful strict monoidal functor,
  and an equivariance under `ρ` as a monoidal natural isomorphism `U ≅ U ∘ ρ`.
  Faithfulness forces `ρ` to be a monoid endomorphism; non-additive diffeomorphisms
  cannot be implemented.
- Generalization: the same argument works for any faithful action of a commutative group
  `(G, ·)` on `End(H)`: an intertwiner implementing `ρ : G → G` forces `ρ` to be a
  group homomorphism.

-/

end QuantumGravityTheorems
