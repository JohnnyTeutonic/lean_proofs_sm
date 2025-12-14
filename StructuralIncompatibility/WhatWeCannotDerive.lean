/-
Copyright (c) 2025 Jonathan Reich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Reich
-/

/-!
# What We Cannot Derive

## Purpose

This file is "armor" — it explicitly lists what the framework does NOT derive,
with typed reasons explaining WHY each item is not derivable.

## Three Bins

1. **Underdetermined by Kinematics**: Requires dynamics / RG input
2. **Requires Empirical Boundary Conditions**: Needs experimental input
3. **Requires Vacuum Selection**: Needs symmetry breaking / Higgs sector

## Rhetorical Effect

- We're not claiming omniscience
- We know the difference between "structural" and "dynamical"
- This prevents overclaiming and builds credibility
-/

namespace WhatWeCannotDerive

/-! ## Reason Categories -/

/-- Why something is not derivable -/
inductive NonDerivableReason where
  | UnderdeterminedByKinematics  -- Needs dynamics / RG
  | RequiresEmpiricalBC          -- Needs experimental boundary condition
  | RequiresVacuumSelection      -- Needs Higgs / symmetry breaking model
  | RequiresScaleSetting         -- Package P has no scale axiom
  | RequiresYukawaStructure      -- Flavor physics not in P
  | RequiresCPViolationPhase     -- CP phase is dynamical
  | RequiresCosmologicalIC       -- Cosmological initial conditions
  deriving Repr, DecidableEq

/-- A non-derivable parameter with its reason -/
structure NonDerivable where
  name : String
  symbol : String
  reason : NonDerivableReason
  explanation : String
  whatWeCanSay : String
  deriving Repr

/-! ## The Non-Derivables List -/

/-- Fine structure constant -/
def alpha_em : NonDerivable := {
  name := "Fine structure constant"
  symbol := "α"
  reason := .UnderdeterminedByKinematics
  explanation := "Package P fixes gauge group but not coupling strengths. RG running requires dynamics."
  whatWeCanSay := "α⁻¹(M_Z) = 128 = dim(Δ⁺) is a CONSTRAINT, not a derivation. Running to α⁻¹(0)=137 needs RG."
}

/-- Yukawa couplings -/
def yukawas : NonDerivable := {
  name := "Yukawa couplings"
  symbol := "y_f"
  reason := .RequiresYukawaStructure
  explanation := "Package P determines representations but not Yukawa matrices within those reps."
  whatWeCanSay := "Hierarchical structure (mass ratios) may follow from E₈ → E₆ branching, but absolute values need dynamics."
}

/-- Absolute fermion masses -/
def absoluteMasses : NonDerivable := {
  name := "Absolute fermion masses"
  symbol := "m_f"
  reason := .RequiresScaleSetting
  explanation := "Package P has no mass scale axiom. All masses need the Higgs VEV as input."
  whatWeCanSay := "Mass RATIOS (e.g., m_t/m_b) may be constrained; absolute masses need v = 246 GeV input."
}

/-- Higgs VEV -/
def higgsVEV : NonDerivable := {
  name := "Higgs vacuum expectation value"
  symbol := "v"
  reason := .RequiresVacuumSelection
  explanation := "The electroweak scale v = 246 GeV requires specifying the Higgs potential minimum."
  whatWeCanSay := "Nothing. This is a pure boundary condition from experiment."
}

/-- Higgs mass -/
def higgsMass : NonDerivable := {
  name := "Higgs boson mass"
  symbol := "m_H"
  reason := .RequiresVacuumSelection
  explanation := "m_H depends on the Higgs quartic coupling λ, which is not fixed by Package P."
  whatWeCanSay := "Nothing from structure. m_H = 125 GeV is experimental input."
}

/-- CP violation phase -/
def cpPhase : NonDerivable := {
  name := "CP violation phase"
  symbol := "δ_CP"
  reason := .RequiresCPViolationPhase
  explanation := "The complex phase in CKM/PMNS is dynamical, though we can say δ ≠ 0, π is forced."
  whatWeCanSay := "δ_CP ∉ {0, π} is derived (CP violation forced). But |δ_CP| ≈ π/2 is only 'preferred', not proven."
}

/-- Strong coupling constant -/
def alphaStrong : NonDerivable := {
  name := "Strong coupling constant"
  symbol := "α_s"
  reason := .UnderdeterminedByKinematics
  explanation := "Package P fixes SU(3) gauge group but α_s(M_Z) needs RG matching."
  whatWeCanSay := "α_s runs asymptotically free. Its value at any scale needs one experimental input."
}

/-- Weak mixing angle at low energy -/
def thetaWLowEnergy : NonDerivable := {
  name := "Weak mixing angle (low energy)"
  symbol := "sin²θ_W(0)"
  reason := .UnderdeterminedByKinematics
  explanation := "sin²θ_W = 3/8 at GUT scale is derived. Running to low energy needs RG dynamics."
  whatWeCanSay := "sin²θ_W(M_GUT) = 3/8 exactly. sin²θ_W(M_Z) ≈ 0.231 needs RG evolution."
}

/-- Cosmological constant magnitude -/
def lambdaMagnitude : NonDerivable := {
  name := "Cosmological constant magnitude"
  symbol := "|Λ|"
  reason := .RequiresCosmologicalIC
  explanation := "We derive Λ > 0 and γ = 248/42 for evolution, but |Λ| = 10⁻¹²² M_P⁴ needs IC."
  whatWeCanSay := "Λ > 0 (derived), γ = w_a/(1+w₀) (derived), but |Λ| magnitude needs cosmological input."
}

/-- Baryon asymmetry -/
def baryonAsymmetry : NonDerivable := {
  name := "Baryon asymmetry"
  symbol := "η_B"
  reason := .RequiresCosmologicalIC
  explanation := "η_B ~ 10⁻¹⁰ requires specific baryogenesis dynamics beyond Package P."
  whatWeCanSay := "CP violation is forced (necessary for baryogenesis). But η_B value needs dynamics."
}

/-! ## Complete List -/

def allNonDerivables : List NonDerivable := [
  alpha_em, yukawas, absoluteMasses, higgsVEV, higgsMass,
  cpPhase, alphaStrong, thetaWLowEnergy, lambdaMagnitude, baryonAsymmetry
]

theorem ten_non_derivables : allNonDerivables.length = 10 := by native_decide

/-! ## Counts by Reason -/

def countByReason (r : NonDerivableReason) : Nat :=
  (allNonDerivables.filter (·.reason == r)).length

theorem reason_counts :
    countByReason .UnderdeterminedByKinematics = 3 ∧
    countByReason .RequiresVacuumSelection = 2 ∧
    countByReason .RequiresCosmologicalIC = 2 := by native_decide

/-! ## What We CAN Say (Partial Results) -/

/-- 
**PARTIAL RESULTS**

Even for non-derivable quantities, we often have partial constraints:

| Parameter | What's Derived | What's Not |
|-----------|----------------|------------|
| α | α⁻¹(M_Z) = 128 constraint | Running to 137 |
| sin²θ_W | = 3/8 at GUT | Low-energy value |
| δ_CP | ≠ 0, π (CP forced) | Exact value |
| Λ | > 0, γ = 248/42 | Magnitude |
| masses | Ratios constrained | Absolute values |
-/
structure PartialResult where
  parameter : String
  derived : String
  notDerived : String
  deriving Repr

def partialResults : List PartialResult := [
  { parameter := "α", derived := "α⁻¹(M_Z) = 128", notDerived := "Running to 137" },
  { parameter := "sin²θ_W", derived := "= 3/8 at GUT", notDerived := "Low-energy value" },
  { parameter := "δ_CP", derived := "≠ 0, π", notDerived := "Exact value" },
  { parameter := "Λ", derived := "> 0, γ = 248/42", notDerived := "Magnitude" },
  { parameter := "masses", derived := "Ratios constrained", notDerived := "Absolute values" }
]

/-! ## Why This Matters -/

/-- 
**WHY HONESTY ABOUT NON-DERIVABLES MATTERS**

1. **Prevents Overclaiming**: We don't pretend to derive everything
2. **Shows Understanding**: We know kinematics vs dynamics difference
3. **Identifies Future Work**: What would extend the framework
4. **Builds Credibility**: Honest limitations are more convincing than claims of completeness

**The Framework Derives**:
- Gauge group structure (SU(3)×SU(2)×U(1))
- Generation number (3)
- Mixing angle structures (ratios)
- GUT-scale couplings (sin²θ_W = 3/8)
- γ = 248/42 for dark energy

**The Framework Does Not Derive**:
- Absolute masses (needs Higgs VEV)
- Coupling values (needs RG input)
- CP phase magnitude (dynamical)
- Λ magnitude (cosmological IC)
-/
structure HonestyStatement where
  whatWeDeriveCount : Nat := 5
  whatWeDontDeriveCount : Nat := 10
  keyInsight : String := "We know the difference between structure and dynamics"
  deriving Repr

def honestyStatement : HonestyStatement := {}

/-! ## Summary -/

/--
**Non-Derivables Summary**

| Category | Count | Examples |
|----------|-------|----------|
| Underdetermined by kinematics | 3 | α, α_s, θ_W(low) |
| Requires vacuum selection | 2 | v, m_H |
| Requires cosmological IC | 2 | |Λ|, η_B |
| Requires Yukawa structure | 1 | y_f |
| Requires CP phase dynamics | 1 | δ_CP |
| Requires scale setting | 1 | m_f |

**Conclusion**: 10 parameters need input beyond Package P.
This is honest acknowledgement, not weakness.
-/
theorem summary :
    allNonDerivables.length = 10 ∧
    countByReason .UnderdeterminedByKinematics = 3 := by native_decide

end WhatWeCannotDerive
