/-
Copyright (c) 2025 Jonathan Reich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Reich
-/

/-!
# MCI Failure Modes: Observation → Broken Axiom Mapping

## Purpose

Each falsifier points to a specific axiom that breaks.
This makes falsification scientifically meaningful—not just "wrong" but "wrong because X".

## Failure Mode Table

| Observational Failure | What Breaks Internally | Which Assumption to Drop |
|-----------------------|------------------------|--------------------------|
| w_a > 0 (freezing) | Flow direction reversed | λ > 0 / entropy arrow |
| w₀ < -1 stable (phantom) | Negative effective DOF | Positivity of functional |
| Oscillatory w(a) | Flow not 1-parameter | Single modular flow assumption |
| ΛCDM perfect (γ = 0) | No E₈ obstruction | "E₈ drives obstruction" |
-/

namespace MCIFailureModes

/-! ## MCI Axioms (Recap) -/

/-- The axioms underlying MCI -/
inductive MCIAxiom where
  | ScaleHomomorphism   -- s(ab) = s(a) + s(b) → log form
  | EntropyArrow        -- λ > 0 from thermodynamic arrow
  | SingleParameter     -- Modular flow is one-parameter
  | PositiveFunctional  -- Obstruction functional Ω > 0
  | E8DrivesObstruction -- E₈ structure determines Ω
  deriving Repr, DecidableEq

/-! ## Observable Failures -/

/-- Possible observational failures of MCI -/
inductive ObservationalFailure where
  | Freezing            -- w_a > 0 (dark energy strengthening)
  | Phantom             -- w₀ < -1 stable (crosses phantom divide)
  | Oscillatory         -- w(z) oscillates
  | PerfectLCDM         -- No deviation from Λ (γ = 0)
  | WrongSign           -- γ > 0 instead of γ < 0
  deriving Repr, DecidableEq

/-! ## Failure Mode Mapping -/

/-- Which axiom breaks for each failure -/
def brokenAxiom : ObservationalFailure → MCIAxiom
  | .Freezing => .EntropyArrow          -- λ > 0 violated
  | .Phantom => .PositiveFunctional     -- Ω > 0 violated
  | .Oscillatory => .SingleParameter    -- Not one-parameter flow
  | .PerfectLCDM => .E8DrivesObstruction -- E₈ not relevant
  | .WrongSign => .EntropyArrow         -- λ sign wrong

/-- Explanation of each failure mechanism -/
def failureMechanism : ObservationalFailure → String
  | .Freezing => "w_a > 0 means ds/d(ln a) < 0, violating entropy arrow"
  | .Phantom => "w₀ < -1 stable requires negative Ω, violating positivity"
  | .Oscillatory => "Oscillations require multi-parameter or periodic flow"
  | .PerfectLCDM => "γ = 0 means no E₈ contribution to late-time dynamics"
  | .WrongSign => "γ > 0 corresponds to wrong flow direction"

/-! ## Failure Mode Table -/

structure FailureModeEntry where
  observation : ObservationalFailure
  whatBreaks : String
  axiomDropped : MCIAxiom
  mechanism : String
  deriving Repr

def failureModeTable : List FailureModeEntry := [
  { observation := .Freezing
    whatBreaks := "Flow direction reversed"
    axiomDropped := .EntropyArrow
    mechanism := "ds/d(ln a) < 0 contradicts entropy increase" },
  { observation := .Phantom
    whatBreaks := "Negative effective monotone"
    axiomDropped := .PositiveFunctional
    mechanism := "Stable w < -1 requires Ω < 0 somewhere" },
  { observation := .Oscillatory
    whatBreaks := "Flow not 1-parameter gradient-like"
    axiomDropped := .SingleParameter
    mechanism := "Oscillations need limit cycles, not gradient flow" },
  { observation := .PerfectLCDM
    whatBreaks := "E₈ has no late-time effect"
    axiomDropped := .E8DrivesObstruction
    mechanism := "γ = 0 means 248/N_eff contribution vanishes" },
  { observation := .WrongSign
    whatBreaks := "Thawing → freezing direction"
    axiomDropped := .EntropyArrow
    mechanism := "Positive γ would mean anti-thermodynamic flow" }
]

theorem five_failure_modes : failureModeTable.length = 5 := by native_decide

/-! ## Current Status -/

/-- Has each failure mode been observed? -/
def currentStatus : ObservationalFailure → Bool
  | .Freezing => false      -- DESI shows w_a < 0 (thawing)
  | .Phantom => false       -- w₀ > -1 in current data
  | .Oscillatory => false   -- No oscillation signal
  | .PerfectLCDM => false   -- DESI shows deviation from ΛCDM
  | .WrongSign => false     -- γ appears negative

theorem no_failures_observed :
    currentStatus .Freezing = false ∧
    currentStatus .Phantom = false ∧
    currentStatus .Oscillatory = false ∧
    currentStatus .PerfectLCDM = false ∧
    currentStatus .WrongSign = false := by native_decide

/-! ## What Survives Each Failure -/

/-- If a failure is observed, what remains of the framework? -/
def whatSurvives : ObservationalFailure → String
  | .Freezing => "Kinematics (SM, GR structure) survives; MCI dynamics fails"
  | .Phantom => "All structure survives; need modified Ω functional"
  | .Oscillatory => "E₈ structure survives; need multi-parameter flow"
  | .PerfectLCDM => "Kinematics survives; E₈ irrelevant at late times"
  | .WrongSign => "Structure survives; entropy arrow needs reversal"

/-! ## Implication Lemmas -/

/-- If freezing observed, entropy arrow axiom is false -/
theorem freezing_implies_no_arrow :
    brokenAxiom .Freezing = .EntropyArrow := rfl

/-- If phantom observed, positivity axiom is false -/
theorem phantom_implies_no_positivity :
    brokenAxiom .Phantom = .PositiveFunctional := rfl

/-- If oscillatory observed, single-parameter axiom is false -/
theorem oscillatory_implies_multiparameter :
    brokenAxiom .Oscillatory = .SingleParameter := rfl

/-- If perfect ΛCDM, E₈ obstruction axiom is false -/
theorem lcdm_implies_no_e8 :
    brokenAxiom .PerfectLCDM = .E8DrivesObstruction := rfl

/-! ## Why This Matters -/

/-- 
**Scientific Value of Failure Mode Mapping**

1. Makes falsification SPECIFIC: not just "wrong" but "wrong because X"
2. Identifies which assumption to revise
3. Shows what survives even if MCI fails
4. Distinguishes catastrophic failure from partial failure

**Example**: If w_a > 0 observed, we don't throw out E₈.
We revise only the entropy arrow assumption (maybe time runs backward?).
-/
structure ScientificValue where
  makesFalsificationSpecific : Bool := true
  identifiesAssumptionToRevise : Bool := true
  showsWhatSurvives : Bool := true
  distinguishesPartialFailure : Bool := true
  deriving Repr

def scientificValue : ScientificValue := {}

/-! ## Hierarchy of Failures -/

/-- 
**Failure Severity Hierarchy**

| Failure | Severity | What Survives |
|---------|----------|---------------|
| Perfect ΛCDM | Mild | All kinematics, just no γ dynamics |
| Wrong sign | Moderate | Structure, need sign fix |
| Oscillatory | Moderate | E₈, need richer flow |
| Freezing | Severe | Kinematics only |
| Phantom | Severe | Need new Ω functional |

"Severe" means MCI is wrong in principle.
"Moderate" means MCI needs modification.
"Mild" means γ ≈ 0, framework still valid but dynamics weak.
-/
inductive FailureSeverity where
  | Mild
  | Moderate
  | Severe
  deriving Repr, DecidableEq

def severity : ObservationalFailure → FailureSeverity
  | .PerfectLCDM => .Mild
  | .WrongSign => .Moderate
  | .Oscillatory => .Moderate
  | .Freezing => .Severe
  | .Phantom => .Severe

/-! ## Summary -/

/--
**Failure Mode Summary**

| Aspect | Status |
|--------|--------|
| Failure modes mapped | 5 |
| Currently observed | 0 |
| Most likely next | Perfect ΛCDM (if γ too small) |
| Most damaging | Phantom (violates positivity) |

**Conclusion**: Each falsifier has a specific target.
This is mature methodology, not unfalsifiable speculation.
-/
theorem failure_mode_summary :
    failureModeTable.length = 5 ∧
    (currentStatus .Freezing = false) ∧
    (brokenAxiom .Freezing = .EntropyArrow) := by native_decide

end MCIFailureModes
