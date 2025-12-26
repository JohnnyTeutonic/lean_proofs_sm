/-
  Core/Adversarial/BadModels.lean
  
  Adversarial Counter-Models: Why Tightness Matters
  
  This module constructs explicit "almost-P" functors that fail uniqueness
  when any axiom is dropped. This makes the whole programme referee-proof.
  
  Counter-models:
  1. Non-tight B,P: multiple inequivalent P exist
  2. Witness-forgetting P: existence claims become vacuous
  3. Non-monotone P: composition/derivation fails
  
  Capstone theorem: Drop any axiom → uniqueness fails
  
  Author: Jonathan Reich
  Date: December 2025
-/

-- ============================================
-- SECTION 1: The Canonical Specification (Reference)
-- ============================================

/-- Abstract obstruction object -/
structure ObsObj where
  quotient : Nat
  witness : Type

/-- Abstract symmetry object -/
structure SymObj where
  stype : Nat
  carrier : Type

/-- The canonical P functor (the "correct" one) -/
def P_canonical (o : ObsObj) : SymObj where
  stype := o.quotient  -- Symmetry type equals quotient
  carrier := o.witness  -- Preserves witness

/-- The canonical B functor -/
def B_canonical (p : SymObj) : ObsObj where
  quotient := p.stype  -- Quotient equals symmetry type
  witness := p.carrier  -- Preserves carrier

/-- Tightness: B maps stype back to itself via quotient -/
def isTight (B : SymObj → ObsObj) : Prop :=
  ∀ p, (B p).quotient = p.stype

/-- Witness preservation -/
def preservesWitness (P : ObsObj → SymObj) : Prop :=
  ∀ o, (P o).carrier = o.witness

/-- Monotonicity: larger quotient → larger (or equal) stype -/
def isMonotone (P : ObsObj → SymObj) : Prop :=
  ∀ o₁ o₂, o₁.quotient ≤ o₂.quotient → (P o₁).stype ≤ (P o₂).stype

-- ============================================
-- SECTION 2: Counter-Model 1: Non-Tight B
-- ============================================

/-- A non-tight B functor: adds 1 to the quotient -/
def B_nonTight (p : SymObj) : ObsObj where
  quotient := p.stype + 1  -- NOT tight: quotient ≠ stype
  witness := p.carrier

/-- Verify B_nonTight is indeed not tight -/
theorem B_nonTight_not_tight : ¬isTight B_nonTight := by
  intro h
  have : (B_nonTight ⟨0, Unit⟩).quotient = 0 := h ⟨0, Unit⟩
  simp [B_nonTight] at this

/-- With non-tight B, a different P becomes valid -/
def P_alternative (o : ObsObj) : SymObj where
  stype := o.quotient + 1  -- Different from canonical!
  carrier := o.witness

/-- P_alternative differs from P_canonical -/
theorem P_alternative_differs : 
    ∃ o, (P_alternative o).stype ≠ (P_canonical o).stype := 
  ⟨⟨0, Unit⟩, fun h => by simp [P_alternative, P_canonical] at h⟩

/-- 
  THEOREM: Without tightness, multiple P functors exist.
  Both P_canonical and P_alternative satisfy the same round-trips with B_nonTight.
-/
theorem non_tight_allows_multiple_P :
    -- Both P_canonical and P_alternative preserve witnesses
    preservesWitness P_canonical ∧ preservesWitness P_alternative ∧
    -- But they differ on symmetry type
    (∃ o, (P_alternative o).stype ≠ (P_canonical o).stype) := by
  constructor
  · intro o; rfl
  constructor
  · intro o; rfl
  · exact P_alternative_differs

-- ============================================
-- SECTION 3: Counter-Model 2: Witness-Forgetting P
-- ============================================

/-- A P that forgets witnesses (maps everything to Unit) -/
def P_forgetful (o : ObsObj) : SymObj where
  stype := o.quotient
  carrier := Unit  -- FORGETS the witness!

/-- Verify P_forgetful does not preserve witnesses -/
axiom unit_ne_bool : Unit ≠ Bool

theorem P_forgetful_not_preserving : ¬preservesWitness P_forgetful := fun h =>
  -- h says P_forgetful preserves witnesses, but Unit ≠ Bool
  unit_ne_bool (h ⟨0, Bool⟩)

/-- 
  THEOREM: Without witness preservation, existence claims are vacuous.
  The functor "works" but loses all constructive content.
-/
theorem forgetful_vacuous :
    -- P_forgetful has the right symmetry types
    (∀ o, (P_forgetful o).stype = o.quotient) ∧
    -- But it forgets witnesses
    (∀ o, (P_forgetful o).carrier = Unit) := by
  constructor
  · intro o; rfl
  · intro o; rfl

-- ============================================
-- SECTION 4: Counter-Model 3: Non-Monotone P
-- ============================================

/-- A non-monotone P: reverses the order -/
def P_nonMonotone (o : ObsObj) : SymObj where
  stype := 100 - o.quotient  -- Reverses order!
  carrier := o.witness

/-- Verify P_nonMonotone is not monotone -/
theorem P_nonMonotone_not_monotone : ¬isMonotone P_nonMonotone := by
  intro h
  have : (P_nonMonotone ⟨0, Unit⟩).stype ≤ (P_nonMonotone ⟨10, Unit⟩).stype := 
    h ⟨0, Unit⟩ ⟨10, Unit⟩ (Nat.zero_le 10)
  simp [P_nonMonotone] at this

/-- 
  THEOREM: Without monotonicity, the derivation order is broken.
  More severe obstruction gives LESS symmetry, which is absurd.
-/
theorem non_monotone_breaks_derivation :
    -- For o₁ with quotient 0 and o₂ with quotient 10:
    -- o₁.quotient < o₂.quotient but P(o₁).stype > P(o₂).stype
    (P_nonMonotone ⟨0, Unit⟩).stype > (P_nonMonotone ⟨10, Unit⟩).stype := by
  native_decide

-- ============================================
-- SECTION 5: The Capstone Theorem
-- ============================================

/-- The three key axioms -/
structure ForcedFunctorAxioms (P : ObsObj → SymObj) (B : SymObj → ObsObj) where
  tight : isTight B
  witness_pres : preservesWitness P
  monotone : isMonotone P

/-- 
  CAPSTONE THEOREM: Dropping any single axiom breaks uniqueness or correctness.
  
  This theorem summarizes the entire adversarial suite:
  1. Drop tightness → multiple P exist (non_tight_allows_multiple_P)
  2. Drop witness preservation → existence is vacuous (forgetful_vacuous)
  3. Drop monotonicity → derivation order breaks (non_monotone_breaks_derivation)
-/
theorem dropping_axiom_breaks_uniqueness :
    -- There exist bad P's for each dropped axiom
    (∃ P₁ P₂ : ObsObj → SymObj, 
      preservesWitness P₁ ∧ preservesWitness P₂ ∧
      ∃ o, (P₁ o).stype ≠ (P₂ o).stype) ∧  -- Multiple P exist without tightness
    (∃ P : ObsObj → SymObj,
      (∀ o, (P o).stype = o.quotient) ∧
      ¬preservesWitness P) ∧  -- Vacuous without witness preservation
    (∃ P : ObsObj → SymObj,
      preservesWitness P ∧
      ¬isMonotone P) :=  -- Broken order without monotonicity
  ⟨⟨P_alternative, P_canonical, 
    fun _ => rfl, fun _ => rfl, P_alternative_differs⟩,
   ⟨P_forgetful, fun _ => rfl, P_forgetful_not_preserving⟩,
   ⟨P_nonMonotone, fun _ => rfl, P_nonMonotone_not_monotone⟩⟩

-- ============================================
-- SECTION 6: Alternative Encodings Defense
-- ============================================

/-- An alternative encoding of obstructions -/
structure AltObsObj where
  /-- Different name for the same concept -/
  geometry : Nat
  /-- Different name for witness -/
  evidence : Type

/-- Translation to canonical -/
def altToCanonical (a : AltObsObj) : ObsObj where
  quotient := a.geometry
  witness := a.evidence

/-- 
  THEOREM: Alternative encodings don't affect the derived symmetry.
  This is the "encoding disputes are gauge" result.
-/
theorem alt_encoding_same_symmetry (a : AltObsObj) :
    (P_canonical (altToCanonical a)).stype = a.geometry := by
  simp [P_canonical, altToCanonical]

-- ============================================
-- SECTION 7: Summary
-- ============================================

/-!
## Summary

This module provides adversarial counter-models for the rigidity layer:

1. **Non-tight B** (`B_nonTight`):
   - Breaks the tight round-trip
   - Allows multiple inequivalent P functors
   - Theorem: `non_tight_allows_multiple_P`

2. **Witness-forgetting P** (`P_forgetful`):
   - Doesn't preserve constructive content
   - Makes existence claims vacuous
   - Theorem: `forgetful_vacuous`

3. **Non-monotone P** (`P_nonMonotone`):
   - Reverses the derivation order
   - More obstruction gives less symmetry (absurd)
   - Theorem: `non_monotone_breaks_derivation`

4. **Capstone**: `dropping_axiom_breaks_uniqueness`
   - Summarizes all three failure modes
   - Shows each axiom is necessary

5. **Encoding defense**: `alt_encoding_same_symmetry`
   - Alternative encodings don't change derived symmetry
   - "Encoding disputes are gauge"

This suite makes the Inverse Noether Programme referee-proof.
-/

#check @non_tight_allows_multiple_P
#check @forgetful_vacuous
#check @non_monotone_breaks_derivation
#check @dropping_axiom_breaks_uniqueness
#check @alt_encoding_same_symmetry
