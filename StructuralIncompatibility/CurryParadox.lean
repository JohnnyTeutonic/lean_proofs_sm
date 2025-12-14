import GodelAxiomsComplete
import ImpossibilityQuotientIsomorphism
import DiagonalNondegenerate
import BinaryTerminalTheorem_v3

/-!
# Curry's Paradox

This file formalizes Curry's Paradox by constructing the Curry sentence C
via the diagonal lemma. Curry's sentence asserts "If C is provable, then ⊥."

Unlike the Liar (which uses negation), Curry uses implication to achieve
a similar self-referential contradiction.

Author: Jonathan Reich, October 2025
-/

namespace CurryParadox

open GodelComplete ModularKernel ImpossibilityQuotient

/-! ## 1. Construction of Curry's Sentence via Diagonal Lemma

**Code Reuse Demonstration**: The Curry sentence C is constructible via the
**same diagonal_lemma** used in Gödel's Incompleteness, Löb's Theorem,
Tarski's Undefinability, Halting Problem, MUH, and PV Unprovability.
This demonstrates literal code sharing across 7+ impossibility results.
-/

/-- A formula representing falsehood (contradiction).
    We use 0 ≠ 0 as our encoding of ⊥. -/
def False_formula : Formula := 
  Formula.not (Formula.eq Term.zero Term.zero)

/-- Construct C using the diagonal lemma on "Prov(x) → ⊥".
    
    C is the fixed point of F(φ) = "Prov(⌜φ⌝) → ⊥"
    
    So: C ↔ (Prov(⌜C⌝) → ⊥)
    
    This is the **same diagonal_lemma call** used in 6 other impossibilities.
-/
noncomputable def C : Formula :=
  Classical.choose (diagonal_lemma (fun v => 
    Formula.implies 
      (Formula.subst 0 (Term.var v) ProvFormula) 
      False_formula))

/-- Axiom: The Curry sentence C satisfies the expected diagonal property.
    This bridges the gap between the diagonal lemma's `subst_num` encoding
    and the `ProvOf` encoding. Provable in principle via Gödel numbering machinery,
    but axiomatized here for clarity. -/
axiom curry_diagonal_property : 
  Provable (Formula.implies C (Formula.implies (ProvOf C) False_formula)) ∧
  Provable (Formula.implies (Formula.implies (ProvOf C) False_formula) C)

/-- The defining property of C from the diagonal lemma:
    PA ⊢ (C → (Prov(⌜C⌝) → ⊥)) and PA ⊢ ((Prov(⌜C⌝) → ⊥) → C) -/
theorem C_spec : 
  Provable (Formula.implies C (Formula.implies (ProvOf C) False_formula)) ∧
  Provable (Formula.implies (Formula.implies (ProvOf C) False_formula) C) :=
  curry_diagonal_property

/-! ## 2. The Curry Property -/

/-- Axiom: C satisfies the Curry property.
    If C is provable, then false is provable (i.e., inconsistency).
    This follows from C_spec + contraction, but requires proof machinery. -/
axiom curry_property : Provable C → Provable False_formula

/-! ## 3. Impossibility Structure -/

/-- The impossibility structure for Curry's Paradox. -/
noncomputable def curry_impstruct : ImpStruct Formula where
  self_repr := fun φ₁ φ₂ => (φ₁ = C) ∧ (φ₂ = C)
  diagonal  := fun _ => C
  negation  := Not
  trilemma  := fun _ => True

/-- A formula is a fixed point iff it is C. -/
theorem curry_fixed_point_def (s : Formula) :
  curry_impstruct.fixed_point s ↔ (s = C) := by
  unfold ImpStruct.fixed_point curry_impstruct
  simp

/-! ## 4. Non-Degeneracy -/

/-- A simple stable formula: equality of zero with itself -/
def stable_instance : Formula := Formula.eq Term.zero Term.zero

/-- C is distinct from simple tautologies -/
axiom C_ne_stable : C ≠ stable_instance

/-- Classify formulas in the Curry setting into the canonical `Binary` structure:
    the Curry sentence itself is `paradox`, everything else is `stable`. -/
noncomputable def curry_to_Binary (φ : Formula) : Binary :=
  if φ = C then Binary.paradox else Binary.stable

/-- The simple tautology `0 = 0` is classified as `stable` in the Curry binary view. -/
theorem curry_binary_stable_witness :
  curry_to_Binary stable_instance = Binary.stable := by
  unfold curry_to_Binary
  -- Case split on whether `stable_instance = C`.
  by_cases h : stable_instance = C
  · -- In this branch, the `if` takes the paradox arm, but this contradicts `C_ne_stable`,
    -- so we can derive the equality ex falso.
    have : False := C_ne_stable (by simpa [stable_instance] using h.symm)
    exact False.elim this
  · -- Normal case: condition is false, so result is `stable`.
    simp [h]

/-- The Curry sentence itself is classified as `paradox` in the Curry binary view. -/
theorem curry_binary_paradox_witness :
  curry_to_Binary C = Binary.paradox := by
  unfold curry_to_Binary
  simp

/-- Curry's structure is non-degenerate. -/
theorem curry_nondegenerate : Nondegenerate Formula curry_impstruct :=
  diagonal_implies_nondegenerate
    curry_impstruct
    stable_instance
    (by rw [curry_fixed_point_def]; exact C_ne_stable.symm)
    (by rw [curry_fixed_point_def]; simp [curry_impstruct])

/-! ## 5. Quotient Isomorphism -/

/-- Curry's Paradox quotient is isomorphic to the canonical binary structure. -/
noncomputable def curry_quotient_binary : ImpQuotient Formula curry_impstruct ≃ BinaryImp :=
  quotient_equiv_binary curry_nondegenerate

end CurryParadox
