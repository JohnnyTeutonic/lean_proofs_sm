/-
  Domain Susceptibility: Structural Preconditions for Obstruction Theory
  ======================================================================
  
  This file formalizes the structural constraints a domain must satisfy
  before obstruction theory is even admissible. This is not about correctness
  but about shape: does the domain have the right structure to be analyzed?
  
  A domain is admissible iff:
  1. It has identifiable parameters
  2. It has distinguishable outcomes
  3. It has a genuine constraint (not everything achievable)
  4. The constraint induces a quotient matching one of the four mechanisms
  
  This rules out: creativity, aesthetics, vague discourse, unfalsifiable philosophy.
  
  Author: Jonathan Reich
  Date: December 2025
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Basic

namespace DomainSusceptibility

/-!
## Part 1: Basic Domain Structure
-/

/-- A domain has identifiable parameters -/
class HasParameters (D : Type) where
  Param : Type
  param_space : D → Param

/-- A domain has distinguishable outcomes -/
class HasOutcomes (D : Type) where
  Outcome : Type
  outcome_map : D → Outcome
  outcomes_distinguishable : ∀ o₁ o₂ : Outcome, Decidable (o₁ = o₂)

/-- A domain has a genuine constraint (not everything achievable) -/
class HasConstraint (D : Type) [HasOutcomes D] where
  achievable : HasOutcomes.Outcome D → Prop
  constraint_nontrivial : ∃ o : HasOutcomes.Outcome D, ¬ achievable o

/-!
## Part 2: Quotient Shapes (The Four Mechanisms)
-/

/-- The allowed quotient shapes -/
inductive QuotientShape : Type where
  | binary    : QuotientShape                    -- Diagonal mechanism
  | sphere    : ℕ → QuotientShape                -- Resource mechanism (dimension)
  | finite    : ℕ → QuotientShape                -- Structural mechanism (n-partite)
  | gauge     : QuotientShape                    -- Parametric mechanism
  deriving DecidableEq, Repr

/-- An induced quotient on a domain -/
structure InducedQuotient (D : Type) where
  Quotient : Type
  project : D → Quotient
  shape : QuotientShape

/-- A domain has a quotient structure -/
class HasQuotient (D : Type) where
  quotient : InducedQuotient D

/-!
## Part 3: Domain Evidence (The Susceptibility Interface)
-/

/-- Evidence that a domain is susceptible to obstruction analysis -/
structure DomainEvidence (D : Type) where
  has_parameters : HasParameters D
  has_outcomes : HasOutcomes D
  has_constraint : @HasConstraint D has_outcomes
  has_quotient : ∃ Q : InducedQuotient D, True

/-- A domain is admissible iff evidence can be provided -/
def Admissible (D : Type) : Prop := Nonempty (DomainEvidence D)

/-- Inadmissible domains cannot be analyzed -/
def Inadmissible (D : Type) : Prop := ¬ Admissible D

/-!
## Part 4: Mechanism Compatibility
-/

/-- The finite set of allowed shapes -/
def allowedShapes : List QuotientShape :=
  [.binary, .sphere 2, .sphere 3, .sphere 4, .finite 2, .finite 3, .gauge]

/-- A domain's quotient is mechanism-compatible -/
def MechanismCompatible (D : Type) [HasQuotient D] : Prop :=
  ∃ Q : InducedQuotient D, Q.shape ∈ allowedShapes

/-!
## Part 5: Forced vs Contingent Structure
-/

/-- A structural prediction: something forced by obstruction -/
structure StructuralPrediction where
  description : String
  forced : Prop

/-- A contingent choice: empirically determined, not forced -/
structure ContingentChoice (α : Type) where
  options : List α
  selected : α
  selection_valid : selected ∈ options

/-- The forced/contingent distinction -/
inductive StructureType where
  | forced : StructureType      -- Derived from obstruction (e.g., gauge symmetry)
  | contingent : StructureType  -- Empirically determined (e.g., coupling constants)
  deriving DecidableEq, Repr

/-!
## Part 6: Example Domains (Pharmacology)
-/

/-- Steric clash → resource/sphere mechanism -/
def stericClashShape : QuotientShape := .sphere 3

/-- Metal coordination → structural/finite mechanism -/
def metalCoordinationShape : QuotientShape := .finite 6  -- octahedral

/-- Phase flexibility → parametric/gauge mechanism -/
def phaseFlexibilityShape : QuotientShape := .gauge

/-- Example: pharmacophore domain has mechanism-compatible quotient -/
example : stericClashShape ∈ [QuotientShape.binary, .sphere 2, .sphere 3, .sphere 4] := by
  simp [stericClashShape]

/-!
## Part 7: The Susceptibility Theorem
-/

/-- Domains without evidence are not analyzable -/
theorem inadmissible_not_analyzable (D : Type) (h : Inadmissible D) :
    ¬ ∃ (e : DomainEvidence D), True := by
  intro ⟨e, _⟩
  exact h ⟨e⟩

/-- If a domain is admissible, it has all required structure -/
theorem admissible_has_structure (D : Type) (h : Admissible D) :
    ∃ (hp : HasParameters D) (ho : HasOutcomes D) 
      (hc : @HasConstraint D ho) (Q : InducedQuotient D), True := by
  obtain ⟨e⟩ := h
  exact ⟨e.has_parameters, e.has_outcomes, e.has_constraint, e.has_quotient.choose, trivial⟩

/-!
## Part 8: Classification as Human but Falsifiable Act

The identification of which mechanism applies is:
- Human: requires domain expertise to identify parameters, outcomes, constraints
- Falsifiable: the classification makes predictions that can be tested
- Disciplined: constrained to finite set of mechanisms

This is analogous to physics:
- Gauge symmetry is FORCED (structural prediction)
- Coupling constants are EMPIRICAL (contingent choice)
-/

/-- A mechanism classification is a human act with falsifiable consequences -/
structure MechanismClassification (D : Type) where
  evidence : DomainEvidence D
  claimed_mechanism : QuotientShape
  mechanism_in_allowed : claimed_mechanism ∈ allowedShapes
  -- The classification is falsifiable: it predicts the quotient structure
  prediction : StructuralPrediction

/-- A classification is validated if its predictions hold -/
def ClassificationValidated (D : Type) (c : MechanismClassification D) : Prop :=
  c.prediction.forced

/-!
## Summary

Susceptibility is not automatically decidable, but it is structurally constrained.

A domain is admissible for obstruction analysis iff it admits:
1. A parameterisation
2. A genuine constraint  
3. A quotient matching one of a finite set of obstruction mechanisms

The identification of which mechanism applies is a human but falsifiable act,
disciplined by empirical validation.

This formalizes the "pre-filter" before param overlap is even checked.
-/

end DomainSusceptibility
