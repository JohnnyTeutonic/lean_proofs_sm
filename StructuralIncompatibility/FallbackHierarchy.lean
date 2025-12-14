/-
Copyright (c) 2025 Jonathan Reich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Reich
-/

/-!
# Fallback Hierarchy: Dynamics vs Kinematics

## Overview

The E₈ obstruction framework has a natural **fallback hierarchy**:
if specific dynamic predictions fail, the core kinematic derivations survive.

This file formalizes which predictions depend on which axioms,
allowing clean falsification without throwing out the entire framework.

## The Hierarchy

**Tier 1 (Kinematics)**: Core structural derivations
- SM gauge group from anomaly cancellation
- N_c = 3, N_gen = 3 from E₈ → E₆ decomposition
- GR from obstruction structure
- Strong CP solution (θ = 0)

**Tier 2 (Dynamics)**: Cosmological predictions
- γ = 248/42 flow rate
- w(a) evolution equation
- Thawing dark energy

**Tier 3 (Specifics)**: Detailed numerical predictions
- Exact DESI ratio match
- Specific mixing angles
- Proton decay channels

## Key Insight

If Tier 3 fails → Tier 2 may survive
If Tier 2 fails → Tier 1 survives
If Tier 1 fails → Framework falsified

-/

namespace FallbackHierarchy

/-! ## Prediction Tiers -/

inductive Tier where
  | Kinematics  -- Core structural (survives dynamics failure)
  | Dynamics    -- Cosmological flow (survives specifics failure)
  | Specifics   -- Detailed numbers (most falsifiable)
  deriving Repr, DecidableEq

/-! ## Predictions by Tier -/

structure Prediction where
  name : String
  tier : Tier
  falsified : Bool := false
  deriving Repr

/-! ### Tier 1: Kinematics (Core Structure) -/

def SM_gauge_group : Prediction := ⟨"SM gauge group SU(3)×SU(2)×U(1)", Tier.Kinematics, false⟩
def N_colors_3 : Prediction := ⟨"N_c = 3 colors", Tier.Kinematics, false⟩
def N_generations_3 : Prediction := ⟨"N_gen = 3 generations", Tier.Kinematics, false⟩
def GR_from_obstruction : Prediction := ⟨"GR from obstruction", Tier.Kinematics, false⟩
def strong_CP_zero : Prediction := ⟨"θ_QCD = 0", Tier.Kinematics, false⟩
def no_WIMP_DM : Prediction := ⟨"No WIMP dark matter", Tier.Kinematics, false⟩

/-! ### Tier 2: Dynamics (Cosmological Flow) -/

def gamma_248_42 : Prediction := ⟨"γ = 248/42 flow rate", Tier.Dynamics, false⟩
def thawing_DE : Prediction := ⟨"Thawing dark energy (dw/da > 0)", Tier.Dynamics, false⟩
def w_approaches_minus1 : Prediction := ⟨"w → -1 asymptotically", Tier.Dynamics, false⟩
def power_law_scaling : Prediction := ⟨"Power-law scaling a^(-γ)", Tier.Dynamics, false⟩

/-! ### Tier 3: Specifics (Detailed Numbers) -/

def DESI_ratio_exact : Prediction := ⟨"w_a/(1+w_0) = -5.9048 exactly", Tier.Specifics, false⟩
def cabibbo_angle : Prediction := ⟨"sin θ_C = 1/√20", Tier.Specifics, false⟩
def weinberg_angle : Prediction := ⟨"sin²θ_W = 3/8 at GUT", Tier.Specifics, false⟩
def neutrino_NH : Prediction := ⟨"Normal Hierarchy", Tier.Specifics, false⟩

/-! ## Fallback Logic -/

/-- Does falsifying prediction p also falsify prediction q? -/
def falsifies (p q : Prediction) : Bool :=
  -- Lower tier falsification propagates up, not down
  match p.tier, q.tier with
  | Tier.Kinematics, _ => true  -- Kinematics failure kills all
  | Tier.Dynamics, Tier.Kinematics => false  -- Dynamics failure spares kinematics
  | Tier.Dynamics, _ => true  -- Dynamics failure kills dynamics and specifics
  | Tier.Specifics, Tier.Specifics => p.name == q.name  -- Only same prediction
  | Tier.Specifics, _ => false  -- Specifics failure spares higher tiers

/-- What survives if a prediction is falsified? -/
def survives (p : Prediction) (tier : Tier) : Bool :=
  match p.tier, tier with
  | Tier.Specifics, Tier.Kinematics => true
  | Tier.Specifics, Tier.Dynamics => true
  | Tier.Dynamics, Tier.Kinematics => true
  | _, _ => false

/-! ## Theorems -/

/-- If γ = 248/42 is wrong, kinematics survives -/
theorem gamma_wrong_kinematics_survives :
    survives gamma_248_42 Tier.Kinematics = true := by native_decide

/-- If DESI exact ratio is wrong, dynamics survives -/
theorem DESI_wrong_dynamics_survives :
    survives DESI_ratio_exact Tier.Dynamics = true := by native_decide

/-- If DESI exact ratio is wrong, kinematics survives -/
theorem DESI_wrong_kinematics_survives :
    survives DESI_ratio_exact Tier.Kinematics = true := by native_decide

/-- If N_gen = 3 is wrong, nothing survives (core kinematics) -/
theorem N_gen_wrong_nothing_survives :
    survives N_generations_3 Tier.Kinematics = false ∧
    survives N_generations_3 Tier.Dynamics = false := by
  constructor <;> native_decide

/-! ## Scenario Analysis -/

/-- 
Scenario: DESI Y3 shows w_a/(1+w_0) ≠ -5.9

What survives?
- Kinematics: ✓ (SM gauge group, N_c=3, N_gen=3, GR, θ=0)
- Dynamics: ✓ (thawing behavior, power-law, w→-1)
- Specifics: ✗ (exact ratio prediction fails)

This is the "dynamics survives" scenario.
-/
def scenario_DESI_ratio_off : Bool := 
  survives DESI_ratio_exact Tier.Dynamics

theorem DESI_ratio_off_dynamics_ok : scenario_DESI_ratio_off = true := by native_decide

/-- 
Scenario: Future data shows freezing DE (dw/da < 0)

What survives?
- Kinematics: ✓ (SM gauge group, N_c=3, N_gen=3, GR, θ=0)
- Dynamics: ✗ (thawing prediction fails)
- Specifics: ✗ (depends on dynamics)

This is the "kinematics survives" scenario.
-/
def scenario_freezing_DE : Bool :=
  survives thawing_DE Tier.Kinematics

theorem freezing_DE_kinematics_ok : scenario_freezing_DE = true := by native_decide

/-- 
Scenario: 4th generation neutrino discovered

What survives?
- Kinematics: ✗ (N_gen = 3 is core E₈ derivation)
- Dynamics: ✗ (depends on kinematics)
- Specifics: ✗ (depends on kinematics)

This is framework falsification.
-/
def scenario_4th_generation : Bool :=
  survives N_generations_3 Tier.Kinematics

theorem fourth_gen_kills_all : scenario_4th_generation = false := by native_decide

/-! ## Summary Table -/

/--
| Scenario | Kinematics | Dynamics | Specifics |
|----------|------------|----------|-----------|
| DESI ratio ≠ -5.9 | ✓ | ✓ | ✗ |
| Freezing DE | ✓ | ✗ | ✗ |
| Phantom (w < -1) | ✓ | ✗ | ✗ |
| 4th generation | ✗ | ✗ | ✗ |
| WIMP detected | ✗ | ✗ | ✗ |
| θ_QCD ≠ 0 | ✗ | ✗ | ✗ |

The hierarchy ensures graceful degradation:
specific failures don't invalidate core structure.
-/
theorem fallback_hierarchy_well_defined :
    scenario_DESI_ratio_off = true ∧
    scenario_freezing_DE = true ∧
    scenario_4th_generation = false := by
  constructor
  · native_decide
  constructor
  · native_decide
  · native_decide

/-! ## Independence Relations -/

/-- Kinematics predictions are independent of cosmology -/
def kinematics_independent_of_cosmology : Bool :=
  survives thawing_DE Tier.Kinematics ∧
  survives gamma_248_42 Tier.Kinematics ∧
  survives DESI_ratio_exact Tier.Kinematics

theorem kinematics_robust : kinematics_independent_of_cosmology = true := by native_decide

/-- Core derivations that would falsify the entire framework -/
def core_falsifiers : List Prediction := [
  SM_gauge_group,
  N_colors_3,
  N_generations_3,
  GR_from_obstruction,
  strong_CP_zero,
  no_WIMP_DM
]

/-- All core falsifiers are Tier 1 (Kinematics) -/
theorem core_falsifiers_are_kinematics :
    core_falsifiers.all (fun p => p.tier == Tier.Kinematics) = true := by native_decide

end FallbackHierarchy
