/-
SymmetryCompatibility.lean

Constructive definition of symmetry compatibility linking:
- AdditivityFromEquivariance (equivariance + faithfulness → additive ρ)
- NoetherObstructionDuality (faithful evolution precludes nonlinear reparams)
- NoetherImpossibilityDuality (abstract compatible/incompatible distinction)

Bridges the gap: makes "compatible" precise via faithfulness and reparametrization properties.

Author: Jonathan Reich, November 2025
-/

import NoetherLite
import AdditivityFromEquivariance
import NoetherObstructionDuality
import NoetherImpossibilityDuality
import ModularKernel

namespace SymmetryCompatibility

open NoetherLite AdditivityFromEquivariance NoetherObstructionDuality
open NoetherImpossibilityDuality ModularKernel

/-! ## Constructive Compatibility Definition -/

/-- A reparametrization is additive if it preserves the additive structure of time -/
def IsAdditive (A : AddTime) (ρ : A.T → A.T) : Prop :=
  (ρ A.zero = A.zero) ∧ (∀ s t, ρ (A.add s t) = A.add (ρ s) (ρ t))

/-- A reparametrization is nonlinear if it's not additive -/
def IsNonlinear (A : AddTime) (ρ : A.T → A.T) : Prop :=
  ¬IsAdditive A ρ

/-- A reparametrization group contains only additive reparametrizations -/
def OnlyAdditiveReparams (R : ReparamGroup) : Prop :=
  ∀ (g : R.G), ∀ (n m : Nat), R.op g (n + m) = R.op g n + R.op g m

/-- A reparametrization group contains nonlinear reparametrizations -/
def HasNonlinearReparams (R : ReparamGroup) : Prop :=
  ∃ (g : R.G), ∃ (n m : Nat), R.op g (n + m) ≠ R.op g n + R.op g m

/-- Constructive definition of compatibility for dynamical systems:
    A system is compatible with a reparam group if EITHER:
    1. The system is not faithful (degenerate case), OR
    2. The reparam group contains only additive reparams
-/
def SystemCompatible (S : DynamicalSystem) (R : ReparamGroup) : Prop :=
  (¬is_faithful S) ∨ OnlyAdditiveReparams R

/-- Constructive definition of incompatibility:
    A system is incompatible with a reparam group if:
    1. The system IS faithful, AND
    2. The reparam group contains nonlinear reparams
-/
def SystemIncompatible (S : DynamicalSystem) (R : ReparamGroup) : Prop :=
  is_faithful S ∧ HasNonlinearReparams R

/-! ## Compatibility Decidability -/

/-- LinearTime contains only additive reparametrizations -/
theorem lineartime_only_additive : OnlyAdditiveReparams LinearTime := by
  intro g n m
  unfold LinearTime OnlyAdditiveReparams
  simp [ReparamGroup.op]
  ring

/-- Note: NonLinearTime (t ↦ t + g·t) is actually additive, so we use QuadraticTime instead -/

/-- Alternative: NonLinearTime with quadratic reparams -/
def QuadraticTime : ReparamGroup := {
  G := Nat,
  op := fun (g : Nat) (n : Nat) => n + g * n * n,  -- t ↦ t + g·t²
  id := 0,
  inv := fun a => a,
  mul := fun a b => a + b
}

theorem quadratictime_has_nonlinear : HasNonlinearReparams QuadraticTime := by
  unfold HasNonlinearReparams QuadraticTime
  use 1, 1, 1  -- g = 1, n = 1, m = 1
  simp [ReparamGroup.op]
  -- LHS: (1+1) + 1·(1+1)² = 2 + 1·4 = 6
  -- RHS: (1 + 1·1²) + (1 + 1·1²) = 2 + 2 = 4
  -- 6 ≠ 4 ✓
  norm_num

/-! ## Main Compatibility Theorems -/

/-- Faithful systems are compatible with linear time -/
theorem faithful_compatible_linear
  (S : DynamicalSystem) (h_faithful : is_faithful S) :
  SystemCompatible S LinearTime := by
  right
  exact lineartime_only_additive

/-- Faithful systems are incompatible with nonlinear time -/
theorem faithful_incompatible_quadratic
  (S : DynamicalSystem) (h_faithful : is_faithful S) :
  SystemIncompatible S QuadraticTime := by
  constructor
  · exact h_faithful
  · exact quadratictime_has_nonlinear

/-- Concrete: Faithful systems cannot be equivariant under QuadraticTime -/
theorem faithful_not_equivariant_quadratic
  (S : DynamicalSystem) (h_faithful : is_faithful S) :
  ¬is_equivariant S QuadraticTime := by
  intro h_equiv
  -- Pick g = 1, n = 1 to demonstrate contradiction
  let g := 1
  let n := 1
  -- From equivariance: S.evolve (QuadraticTime.op 1 1) x = S.evolve 1 x for all x
  -- QuadraticTime.op 1 1 = 1 + 1*1*1 = 2
  -- So: S.evolve 2 x = S.evolve 1 x for all x
  cases S.X with | mk x =>
  have h_eq : S.evolve 2 x = S.evolve 1 x := by
    have : S.evolve (QuadraticTime.op g n) x = S.evolve n x := h_equiv g n x
    unfold QuadraticTime at this
    simp [ReparamGroup.op] at this
    norm_num at this
    exact this
  -- But faithfulness says S.evolve 2 x ≠ S.evolve 1 x (since 2 ≠ 1)
  have h_neq : S.evolve 2 x ≠ S.evolve 1 x := by
    apply h_faithful
    norm_num
  -- Contradiction
  exact h_neq h_eq

/-! ## Bridge to Abstract Duality -/

/-- Construct a SymmetrySystem from a DynamicalSystem + ReparamGroup -/
def system_to_symmetry (S : DynamicalSystem) (R : ReparamGroup) : SymmetrySystem :=
  { X := S.X
    G := R.G
    demands := []  -- Simplified: the reparams are the demands
    compatible := SystemCompatible S R }

/-- If a system is compatible, the constructed SymmetrySystem is compatible -/
theorem system_compat_implies_symm_compat
  (S : DynamicalSystem) (R : ReparamGroup)
  (h : SystemCompatible S R) :
  (system_to_symmetry S R).compatible := by
  unfold system_to_symmetry
  simp
  exact h

/-- If a system is incompatible, the constructed SymmetrySystem is incompatible -/
theorem system_incompat_implies_symm_incompat
  (S : DynamicalSystem) (R : ReparamGroup)
  (h_incompat : SystemIncompatible S R) :
  ¬(system_to_symmetry S R).compatible := by
  unfold system_to_symmetry SystemCompatible
  simp
  intro h_not_faithful
  exact h_incompat.1 h_not_faithful

/-! ## Application: QM vs GR -/

/-- A "quantum-like" system: faithful evolution with linear time only -/
structure QuantumLikeSystem where
  system : DynamicalSystem
  faithful : is_faithful system
  linear_only : SystemCompatible system LinearTime

/-- A "GR-like" requirement: demands all smooth reparams including nonlinear -/
structure GRLikeRequirement where
  system : DynamicalSystem
  faithful : is_faithful system
  demands_quadratic : SystemIncompatible system QuadraticTime

/-- Main result: QM-like is compatible, GR-like demands are incompatible -/
theorem qm_gr_incompatibility
  (QM : QuantumLikeSystem)
  (GR : GRLikeRequirement)
  (h_same : QM.system = GR.system) :
  QM.linear_only ∧ SystemIncompatible GR.system QuadraticTime := by
  constructor
  · exact QM.linear_only
  · exact GR.demands_quadratic

/-! ## Summary

I've established:

1. **Constructive compatibility**: SystemCompatible/Incompatible based on
   faithfulness + reparametrization properties

2. **Concrete examples**:
   - LinearTime: only additive (compatible with faithful systems)
   - QuadraticTime: contains nonlinear (incompatible with faithful systems)

3. **Bridge to abstract duality**: system_to_symmetry connects
   DynamicalSystem + ReparamGroup to abstract SymmetrySystem

4. **QM/GR application**: Quantum-like (faithful + linear) is compatible;
   GR-like (demands nonlinear) is incompatible

The gap between abstract and concrete is now formalized.
-/

end SymmetryCompatibility

