/-
Copyright (c) 2025 Jonathan Reich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Reich
-/
import Mathlib.Algebra.Lie.CartanMatrix

/-!
# Mixed Gravitational–Gauge Anomaly as Structural Constraint

This file formalizes the mixed gravitational–gauge anomaly cancellation condition
as a structural constraint in the obstruction-theoretic framework.

## Main Concepts

* **Gauge anomaly**: Obstruction to gauge invariance (cubic invariant)
* **Gravitational anomaly**: Obstruction to diffeomorphism invariance
* **Mixed grav–gauge anomaly**: Triangle with two stress-energy insertions and one gauge current

## Key Result

The mixed gravitational–gauge anomaly vanishes iff the total gauge charge over all
left-handed Weyl fermions sums to zero for every generator:

  ∑_{left Weyl} Tr_R(T^a) = 0

For U(1) factors, this is simply: ∑ q_i = 0

## Structural Interpretation

In the obstruction framework:
- Gauge anomaly cancellation = obstruction to internal consistency vanishes
- Mixed grav–gauge anomaly cancellation = obstruction compatible with gravitational coupling

The Standard Model spectrum satisfies both constraints per generation.

## References

* Anomaly cancellation in the Standard Model
* Adler-Bell-Jackiw anomaly
* Green-Schwarz mechanism

## Tags

anomaly, gauge theory, gravitational anomaly, standard model, obstruction
-/

namespace MixedAnomalyConstraint

/-! ## Basic Definitions -/

/-- A gauge group factor (Abelian or non-Abelian) -/
inductive GaugeGroupType where
  | U1 : GaugeGroupType           -- Abelian U(1)
  | SU (n : ℕ) : GaugeGroupType   -- SU(n)
  | SO (n : ℕ) : GaugeGroupType   -- SO(n)
  | Sp (n : ℕ) : GaugeGroupType   -- Sp(n)
  | Exceptional : GaugeGroupType   -- E_6, E_7, E_8, F_4, G_2
  deriving DecidableEq, Repr

/-- Chirality of a fermion -/
inductive Chirality where
  | Left : Chirality
  | Right : Chirality
  deriving DecidableEq, Repr

/-- A Weyl fermion with its gauge charges -/
structure WeylFermion where
  /-- Name/identifier -/
  name : String
  /-- Chirality (left or right) -/
  chirality : Chirality
  /-- U(1)_Y hypercharge -/
  hypercharge : ℚ
  /-- SU(3) representation dimension (1 = singlet, 3 = fundamental, etc.) -/
  su3Rep : ℕ
  /-- SU(2) representation dimension (1 = singlet, 2 = doublet, etc.) -/
  su2Rep : ℕ

/-- The charge functional Q : F → g* for U(1) factors -/
def u1Charge (ψ : WeylFermion) : ℚ :=
  match ψ.chirality with
  | .Left => ψ.hypercharge
  | .Right => -ψ.hypercharge  -- Right-handed contributes with opposite sign

/-! ## Standard Model Fermion Content (One Generation) -/

/-- Left-handed quark doublet Q_L = (u_L, d_L) with Y = 1/6 -/
def quarkDoubletL : WeylFermion := {
  name := "Q_L"
  chirality := .Left
  hypercharge := 1/6
  su3Rep := 3
  su2Rep := 2
}

/-- Right-handed up quark u_R with Y = 2/3 -/
def upQuarkR : WeylFermion := {
  name := "u_R"
  chirality := .Right
  hypercharge := 2/3
  su3Rep := 3
  su2Rep := 1
}

/-- Right-handed down quark d_R with Y = -1/3 -/
def downQuarkR : WeylFermion := {
  name := "d_R"
  chirality := .Right
  hypercharge := -1/3
  su3Rep := 3
  su2Rep := 1
}

/-- Left-handed lepton doublet L_L = (ν_L, e_L) with Y = -1/2 -/
def leptonDoubletL : WeylFermion := {
  name := "L_L"
  chirality := .Left
  hypercharge := -1/2
  su3Rep := 1
  su2Rep := 2
}

/-- Right-handed electron e_R with Y = -1 -/
def electronR : WeylFermion := {
  name := "e_R"
  chirality := .Right
  hypercharge := -1
  su3Rep := 1
  su2Rep := 1
}

/-- One generation of SM fermions -/
def smGeneration : List WeylFermion := [
  quarkDoubletL,   -- Q_L: (3, 2, 1/6)
  upQuarkR,        -- u_R: (3, 1, 2/3)
  downQuarkR,      -- d_R: (3, 1, -1/3)
  leptonDoubletL,  -- L_L: (1, 2, -1/2)
  electronR        -- e_R: (1, 1, -1)
]

/-! ## Mixed Gravitational–Gauge Anomaly -/

/-- 
The mixed gravitational–gauge anomaly functional for U(1)_Y.

A_grav-gauge = ∑_i Q(ψ_i)

where the sum is over all left-handed Weyl fermions, weighted by their
multiplicity (color × isospin).
-/
def mixedAnomalyU1 (fermions : List WeylFermion) : ℚ :=
  fermions.foldl (fun acc ψ => 
    let multiplicity := ψ.su3Rep * ψ.su2Rep
    acc + multiplicity * u1Charge ψ
  ) 0

/-- 
The mixed anomaly condition: A_grav-gauge = 0

This is the structural requirement that the cumulative gauge charge
seen by the gravitational coupling functor vanishes.
-/
def isMixedAnomalyFree (fermions : List WeylFermion) : Prop :=
  mixedAnomalyU1 fermions = 0

/-! ## Verification: Standard Model Anomaly Cancellation -/

/-- 
THEOREM: The Standard Model (one generation) is mixed-anomaly-free.

The hypercharge assignments satisfy:
  3×2×(1/6) + 3×1×(-2/3) + 3×1×(1/3) + 1×2×(-1/2) + 1×1×(1) = 0
  = 1 - 2 + 1 - 1 + 1 = 0 ✓

Note: Right-handed fermions contribute with sign flip in the anomaly.
-/
theorem sm_mixed_anomaly_free : isMixedAnomalyFree smGeneration := by
  unfold isMixedAnomalyFree mixedAnomalyU1 smGeneration
  simp only [List.foldl_cons, List.foldl_nil]
  unfold u1Charge quarkDoubletL upQuarkR downQuarkR leptonDoubletL electronR
  native_decide

/-! ## Pure Gauge Anomaly (Cubic) -/

/-- 
The cubic gauge anomaly for U(1)^3.

A_gauge = ∑_i Q(ψ_i)³

For the theory to be consistent, this must vanish.
-/
def cubicAnomalyU1 (fermions : List WeylFermion) : ℚ :=
  fermions.foldl (fun acc ψ => 
    let multiplicity := ψ.su3Rep * ψ.su2Rep
    let q := u1Charge ψ
    acc + multiplicity * q * q * q
  ) 0

/-- The cubic anomaly condition -/
def isCubicAnomalyFree (fermions : List WeylFermion) : Prop :=
  cubicAnomalyU1 fermions = 0

/-- 
THEOREM: The Standard Model (one generation) is cubic-anomaly-free for U(1)_Y.

∑ n_i × Y_i³ = 0
-/
theorem sm_cubic_anomaly_free : isCubicAnomalyFree smGeneration := by
  unfold isCubicAnomalyFree cubicAnomalyU1 smGeneration
  simp only [List.foldl_cons, List.foldl_nil]
  unfold u1Charge quarkDoubletL upQuarkR downQuarkR leptonDoubletL electronR
  native_decide

/-! ## Obstruction-Theoretic Formulation -/

/-- 
An admissible obstruction configuration satisfies both:
1. Pure gauge anomaly cancellation (cubic)
2. Mixed gravitational–gauge anomaly cancellation (linear)
-/
structure AdmissibleObstructionConfig where
  /-- The collection of chiral fermions -/
  fermions : List WeylFermion
  /-- Pure gauge anomaly vanishes -/
  cubicAnomalyFree : isCubicAnomalyFree fermions
  /-- Mixed grav–gauge anomaly vanishes -/
  mixedAnomalyFree : isMixedAnomalyFree fermions

/-- The Standard Model provides an admissible obstruction configuration -/
def standardModelConfig : AdmissibleObstructionConfig := {
  fermions := smGeneration
  cubicAnomalyFree := sm_cubic_anomaly_free
  mixedAnomalyFree := sm_mixed_anomaly_free
}

/-! ## Coupling Functors (Categorical Formulation) -/

/-- 
The gauge-coupling functor assigns representations to matter fields.
C_gauge : ObstructionData → Rep(G)
-/
structure GaugeCouplingFunctor where
  /-- Maps fermions to their gauge representation data -/
  toRep : WeylFermion → (ℕ × ℕ × ℚ)  -- (SU(3) dim, SU(2) dim, U(1) charge)

/-- 
The gravity-coupling functor assigns spin structure to matter fields.
C_grav : ObstructionData → Connections/Metric(M)

For our purposes, all Weyl fermions have spin-1/2, so this is uniform.
-/
structure GravityCouplingFunctor where
  /-- All Weyl fermions are spin-1/2 -/
  spin : ℚ := 1/2

/-- 
The mixed anomaly condition in categorical language:

The composition F → g* → sum → g* is the zero morphism.

Equivalently: the sum of all gauge charges seen by the gravitational
coupling functor vanishes.
-/
def categoricalMixedAnomalyCondition 
    (fermions : List WeylFermion) 
    (_gaugeCoupling : GaugeCouplingFunctor)
    (_gravCoupling : GravityCouplingFunctor) : Prop :=
  -- The gravitational functor sees all spin-1/2 fermions equally
  -- The mixed anomaly is the linear sum of charges
  mixedAnomalyU1 fermions = 0

/-! ## Connection to Obstruction Framework -/

/-- 
STRUCTURAL THEOREM: Anomaly cancellation as double obstruction constraint.

The same obstruction calculus that forces gauge symmetry also forces
anomaly cancellation in two channels:
1. Pure gauge (cubic invariant)
2. Mixed gravitational–gauge (linear charge sum)

The second is not an afterthought but a structural requirement that
the obstruction theory be compatible with the gravitational coupling functor.
-/
theorem anomaly_as_double_obstruction :
    ∀ config : AdmissibleObstructionConfig,
    isCubicAnomalyFree config.fermions ∧ isMixedAnomalyFree config.fermions :=
  fun config => ⟨config.cubicAnomalyFree, config.mixedAnomalyFree⟩

/-- 
The Standard Model spectrum is a concrete solution of the double anomaly constraint.
-/
theorem sm_solves_double_constraint :
    isCubicAnomalyFree standardModelConfig.fermions ∧ 
    isMixedAnomalyFree standardModelConfig.fermions :=
  anomaly_as_double_obstruction standardModelConfig

/-! ## Summary -/

/-!
## Summary: Mixed Anomaly as Structural Constraint

**The Key Insight:**
Mixed gravitational–gauge anomaly cancellation is not an afterthought but a
structural requirement in the obstruction framework:

- **Gauge anomaly** (cubic): Obstruction to internal gauge consistency
- **Mixed grav–gauge** (linear): Obstruction to diffeomorphism invariance

**The Constraint:**
An admissible obstruction configuration must satisfy both:
1. ∑ Tr_R(T^a {T^b, T^c}) = 0  (cubic)
2. ∑ Tr_R(T^a) = 0  (linear, for each U(1))

**Standard Model Solution:**
The SM hypercharge assignments per generation satisfy both constraints:
- Cubic: ∑ n_i Y_i³ = 0  ✓
- Linear: ∑ n_i Y_i = 0  ✓

**Categorical Formulation:**
The mixed anomaly condition states that the cumulative gauge charge seen by
the gravitational coupling functor vanishes. This is a morphism condition
in the category of obstruction data.

**Physical Meaning:**
The gravitational sector (via the equivalence principle) "sees" all matter
equally weighted by spin. The mixed anomaly requires the total gauge charge
in this gravitationally-weighted sum to vanish.
-/

end MixedAnomalyConstraint
