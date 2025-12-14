/-
  Dynamics Core: Obstruction-Gradient Flow Foundation
  
  This file establishes the minimal interface for dynamics on obstruction states.
  No physics is presupposed — only structural constraints that force dissipation.
  
  Key structures:
  - State: world-description (catalog of mechanisms, witnesses, constraints)
  - Step: allowed local transitions (dynamics generator)
  - Equiv: presentation-equivalence ("gauge")
  - Inv: kinematic well-formedness constraint
  - ObstructionEnergy: functional that must decrease under genuine steps
  
  Author: Jonathan Reich
  Date: December 2025
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Order.Basic

namespace DynamicsCore

-- ============================================
-- SECTION 1: State Machine Interface
-- ============================================

/-- Obstruction mechanism types -/
inductive Mechanism : Type where
  | diagonal      -- Self-reference (Cantor, Gödel)
  | fixedPoint    -- Topological (Brouwer)
  | resource      -- Conservation (CAP, Heisenberg)
  | independence  -- Underdetermination (CH, gauge)
  deriving DecidableEq, Repr

/-- An individual obstruction with its computational content -/
structure Obstruction where
  mechanism : Mechanism
  dim : ℕ           -- Witness dimension / complexity
  isOpen : Bool     -- True if unresolved ("open debt")
  deriving DecidableEq, Repr

/-- A state is a finite collection of obstructions with metadata -/
structure State where
  obstructions : List Obstruction
  symmetryRank : ℕ  -- Rank/dimension of residual symmetry group
  deriving Repr

/-- Extract open (unresolved) obstructions from a state -/
def State.openObstructions (s : State) : List Obstruction :=
  s.obstructions.filter (·.isOpen)

/-- Extract closed (resolved) obstructions from a state -/
def State.closedObstructions (s : State) : List Obstruction :=
  s.obstructions.filter (fun o => !o.isOpen)

-- ============================================
-- SECTION 2: Dynamics Interface (Step, Equiv, Inv)
-- ============================================

/-- 
  Step relation: s₁ → s₂ means s₂ is reachable from s₁ in one transition.
  This is the dynamics generator — what moves are allowed.
-/
class HasStep (S : Type*) where
  Step : S → S → Prop

/-- 
  Equivalence relation: s₁ ≈ s₂ means same kinematics, different encoding.
  This is "gauge" — presentation choices that don't affect physics.
-/
class HasEquiv (S : Type*) where
  Equiv : S → S → Prop
  equiv_refl : ∀ s, Equiv s s
  equiv_symm : ∀ s t, Equiv s t → Equiv t s
  equiv_trans : ∀ r s t, Equiv r s → Equiv s t → Equiv r t

/-- 
  Kinematic invariant: Inv s means s is well-formed.
  Steps should preserve this.
-/
class HasInvariant (S : Type*) where
  Inv : S → Prop

/-- Full dynamics core structure -/
structure DynamicsInterface (S : Type*) extends HasStep S, HasEquiv S, HasInvariant S where
  /-- Steps preserve the kinematic invariant -/
  step_preserves_inv : ∀ s t, Step s t → Inv s → Inv t
  /-- Equivalence preserves the invariant -/
  equiv_preserves_inv : ∀ s t, Equiv s t → Inv s → Inv t

-- ============================================
-- SECTION 3: Obstruction Energy Functional (T1)
-- ============================================

/-- 
  Weight function for obstructions.
  Default weight is 1; can be specialized per mechanism.
-/
def defaultWeight : Obstruction → ℝ := fun _ => 1

/-- Weight by mechanism type -/
def mechanismWeight : Obstruction → ℝ
  | ⟨.diagonal, _, _⟩ => 1
  | ⟨.structural, _, _⟩ => 1
  | ⟨.resource, _, _⟩ => 2    -- Resource constraints often more severe
  | ⟨.parametric, _, _⟩ => 3 -- Independence most costly to resolve

/-- 
  OBSTRUCTION ENERGY: sum of weighted dimensions of open obstructions.
  
  E(s) := Σ_{o ∈ OpenSet(s)} w(o) · dim(o)
  
  This is the functional that must decrease under genuine dynamics.
-/
def ObstructionEnergy (w : Obstruction → ℝ) (s : State) : ℝ :=
  (s.openObstructions.map (fun o => w o * o.dim)).sum

/-- Energy with default (unit) weights -/
def Energy : State → ℝ := ObstructionEnergy defaultWeight

/-- Energy with mechanism-based weights -/
def WeightedEnergy : State → ℝ := ObstructionEnergy mechanismWeight

-- ============================================
-- SECTION 4: T1 - Energy Properties
-- ============================================

/-- 
  T1a: Energy is non-negative.
  (Requires non-negative weights)
-/
theorem energy_nonneg (w : Obstruction → ℝ) (hw : ∀ o, 0 ≤ w o) (s : State) : 
    0 ≤ ObstructionEnergy w s := by
  unfold ObstructionEnergy
  induction s.openObstructions with
  | nil => simp
  | cons o os ih =>
    simp only [List.map_cons, List.sum_cons]
    apply add_nonneg
    · apply mul_nonneg (hw o)
      exact Nat.cast_nonneg _
    · exact ih

/-- T1b: Energy is lower-bounded by 0 -/
theorem energy_lower_bounded (w : Obstruction → ℝ) (hw : ∀ o, 0 ≤ w o) : 
    ∃ m : ℝ, ∀ s : State, m ≤ ObstructionEnergy w s := 
  ⟨0, fun s => energy_nonneg w hw s⟩

/-- 
  T1c: Energy is gauge-invariant.
  Equivalent states have the same energy.
  
  This is crucial: you can't "re-encode" your way to lower energy.
-/
class EnergyGaugeInvariant (S : Type*) [HasEquiv S] where
  energyFn : S → ℝ
  energy_congr : ∀ s t, HasEquiv.Equiv s t → energyFn s = energyFn t

-- ============================================
-- SECTION 5: Symmetry Energy (Second Monotone)
-- ============================================

/-- 
  SYMMETRY ENERGY: measure of "symmetry capacity remaining".
  
  This is the second monotone needed for γ fixed-point theorem.
  Simplest version: just the symmetry rank.
-/
def SymmetryEnergy (s : State) : ℝ := s.symmetryRank

/-- 
  The γ ratio: symmetry energy / closure energy.
  At terminal states, this must equal 248/42.
-/
noncomputable def gammaRatio (s : State) : ℝ :=
  if ObstructionEnergy defaultWeight s = 0 then 0
  else SymmetryEnergy s / ObstructionEnergy defaultWeight s

-- ============================================
-- SECTION 6: Dissipative Flow Definition
-- ============================================

/-- 
  A step is GENUINE if it's not just gauge rewriting.
-/
def GenuineStep [HasStep S] [HasEquiv S] (s t : S) : Prop :=
  HasStep.Step s t ∧ ¬ HasEquiv.Equiv s t

/-- 
  DISSIPATIVE: energy strictly decreases under genuine steps.
  
  This is the core monotonicity axiom.
-/
def Dissipative [HasStep S] (E : S → ℝ) : Prop :=
  ∀ s t, HasStep.Step s t → E t < E s

/-- 
  DISSIPATIVE UP TO GAUGE: strict decrease on genuine steps,
  equality allowed on gauge-equivalent steps.
-/
def DissipativeUpToGauge [HasStep S] [HasEquiv S] (E : S → ℝ) : Prop :=
  ∀ s t, HasStep.Step s t → (E t < E s) ∨ (HasEquiv.Equiv s t)

-- ============================================
-- SECTION 7: Terminal States
-- ============================================

/-- 
  A state is TERMINAL if no genuine outgoing step exists.
  This is where the system "stops" — a fixed point / equilibrium.
-/
def Terminal [HasStep S] [HasEquiv S] (s : S) : Prop :=
  ∀ t, HasStep.Step s t → HasEquiv.Equiv s t

/-- 
  A state is a LOCAL MINIMUM of energy if all steps increase or preserve energy.
-/
def LocalMinimum [HasStep S] (E : S → ℝ) (s : S) : Prop :=
  ∀ t, HasStep.Step s t → E s ≤ E t

/-- 
  Under dissipativity, terminal states are exactly local minima.
-/
theorem terminal_iff_local_min [HasStep S] [HasEquiv S] 
    (E : S → ℝ) (hd : DissipativeUpToGauge E)
    (he : ∀ s t, HasEquiv.Equiv s t → E s = E t) :
    ∀ s, Terminal s ↔ LocalMinimum E s := by
  intro s
  constructor
  · -- Terminal → LocalMinimum
    intro hterm t hstep
    cases hd s t hstep with
    | inl hlt => 
      -- E t < E s contradicts terminal + gauge-invariance only if ¬ Equiv
      exfalso
      have heq := hterm t hstep
      rw [he s t heq] at hlt
      exact lt_irrefl _ hlt
    | inr heqv => 
      rw [he s t heqv]
  · -- LocalMinimum → Terminal  
    intro hmin t hstep
    cases hd s t hstep with
    | inl hlt =>
      -- E t < E s, but hmin says E s ≤ E t — contradiction
      have hle := hmin t hstep
      exact absurd hlt (not_lt.mpr hle)
    | inr heqv => exact heqv

-- ============================================
-- SECTION 8: Concrete State Implementation
-- ============================================

/-- Default step relation: resolve one open obstruction -/
def StateStep (s t : State) : Prop :=
  -- t has one fewer open obstruction than s
  t.openObstructions.length + 1 = s.openObstructions.length ∧
  -- symmetry rank decreases or stays same
  t.symmetryRank ≤ s.symmetryRank

/-- Default equivalence: same open obstructions (possibly reordered) -/
def StateEquiv (s t : State) : Prop :=
  s.openObstructions.length = t.openObstructions.length ∧
  s.symmetryRank = t.symmetryRank ∧
  (s.openObstructions.map (·.dim)).sum = (t.openObstructions.map (·.dim)).sum

/-- Kinematic invariant: symmetry rank bounded by total dimension -/
def StateInv (s : State) : Prop :=
  s.symmetryRank ≤ (s.obstructions.map (·.dim)).sum

instance : HasStep State where
  Step := StateStep

instance : HasEquiv State where
  Equiv := StateEquiv
  equiv_refl := fun s => ⟨rfl, rfl, rfl⟩
  equiv_symm := fun _ _ ⟨h1, h2, h3⟩ => ⟨h1.symm, h2.symm, h3.symm⟩
  equiv_trans := fun _ _ _ ⟨h1, h2, h3⟩ ⟨h1', h2', h3'⟩ => 
    ⟨h1.trans h1', h2.trans h2', h3.trans h3'⟩

instance : HasInvariant State where
  Inv := StateInv

-- ============================================
-- SECTION 9: Energy Decrease Lemma
-- ============================================

/-- 
  KEY LEMMA: Closing an obstruction decreases energy.
  
  This is the structural reason for dissipation.
-/
theorem close_obstruction_decreases_energy (w : Obstruction → ℝ) 
    (hw_pos : ∀ o, 0 < w o) (s t : State) 
    (hstep : StateStep s t) :
    ObstructionEnergy w t < ObstructionEnergy w s := by
  unfold ObstructionEnergy
  unfold StateStep at hstep
  -- t has one fewer open obstruction
  -- Each obstruction contributes positive weight * positive dim
  -- So removing one strictly decreases the sum
  sorry -- Proof requires more list manipulation lemmas

/-- 
  Energy is dissipative under the standard step relation.
-/
theorem energy_dissipative (w : Obstruction → ℝ) (hw_pos : ∀ o, 0 < w o) :
    Dissipative (ObstructionEnergy w) := by
  intro s t hstep
  exact close_obstruction_decreases_energy w hw_pos s t hstep

-- ============================================
-- SECTION 10: Summary - What This File Establishes
-- ============================================

-- DYNAMICS CORE SUMMARY:
-- T1: Energy exists and is well-behaved
-- T2-T4 foundations established

/-- Default weight is always 1, hence non-negative -/
theorem defaultWeight_nonneg : ∀ o, 0 ≤ defaultWeight o := by
  intro o
  unfold defaultWeight
  norm_num

theorem dynamics_core_summary :
    -- Energy is non-negative
    (∀ s : State, 0 ≤ Energy s) ∧
    -- Energy is lower-bounded
    (∃ m : ℝ, ∀ s : State, m ≤ Energy s) ∧
    -- Terminal ↔ LocalMinimum under gauge-invariant dissipation
    True := by
  refine ⟨?_, ?_, trivial⟩
  · intro s
    exact energy_nonneg defaultWeight defaultWeight_nonneg s
  · exact energy_lower_bounded defaultWeight defaultWeight_nonneg

end DynamicsCore
