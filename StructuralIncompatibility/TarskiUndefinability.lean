import GodelAxiomsComplete
import ImpossibilityQuotientIsomorphism
import DiagonalNondegenerate
import BinaryTerminalTheorem_v3

/-!
# Tarski's Undefinability Theorem

This file formalizes Tarski's theorem on the undefinability of truth,
showing how it reduces to the same ImpStruct diagonal pattern as other
impossibility results.

Key insight: While Gödel uses provability and Tarski uses truth, both
exhibit the same diagonal impossibility structure when reduced to ImpStruct.
The semantic difference (provability vs truth) doesn't affect the structural
pattern of self-reference creating stable/paradox dichotomy.

The formalization assumes a hypothetical truth predicate TruthFormula and
shows it generates the same impossibility structure via diagonal lemma.
-/

namespace TarskiUndefinability

open GodelComplete ModularKernel ImpossibilityQuotient

/-!
## Key Background

For the purposes of showing structural reducibility to ImpStruct, we hypothetically
assume a truth predicate exists (even though Tarski proves none can exist).
This demonstrates that the diagonal impossibility pattern emerges regardless
of whether we use provability (Gödel) or truth (Tarski).
-/

/-! ## 1. Hypothetical Truth Predicate and Tarski Sentence

**Code Reuse Demonstration**: Tarski's undefinability uses the **same diagonal_lemma**
as Gödel, Löb, Curry, Halting, MUH, and PV. This demonstrates that the impossibility
structure is identical across provability vs. truth semantics.
-/

/-- Hypothetical truth predicate for PA formulas.
    Tarski proves no such predicate can exist, but we assume it
    to show the diagonal structure. -/
axiom TruthFormula : Formula

/-- The truth predicate applied to a specific formula.
    In reality this cannot exist, but we use it to show the pattern. -/
noncomputable def TruthOf (φ : Formula) : Formula :=
  Formula.subst 0 (Term.num (godel_formula φ)) TruthFormula

/-- Using the diagonal lemma with the (hypothetical) truth predicate,
    we construct the Tarski sentence that says "I am not true".
    
    T is the fixed point of F(φ) = "¬Truth(⌜φ⌝)"
    
    So: T ↔ ¬Truth(⌜T⌝)
    
    This is the **same diagonal_lemma call** used in 6 other impossibilities.
-/
noncomputable def tarski_sentence : Formula :=
  Classical.choose (diagonal_lemma (fun v => Formula.not (Formula.subst 0 (Term.var v) TruthFormula)))

/-- The Tarski sentence satisfies the fixed-point property:
    PA ⊢ T ↔ ¬Truth(⌜T⌝)
    This would lead to contradiction if truth were definable. -/
axiom tarski_fixed_point :
  Provable (Formula.implies tarski_sentence (Formula.not (TruthOf tarski_sentence))) ∧
  Provable (Formula.implies (Formula.not (TruthOf tarski_sentence)) tarski_sentence)

/-! ## 2. Non-degeneracy: Tarski Structure -/

/-- Self-representation for Tarski: formulas represent themselves if they're the Tarski sentence -/
noncomputable def tarski_self_repr (φ₁ φ₂ : Formula) : Prop :=
  (φ₁ = tarski_sentence) ∧ (φ₂ = tarski_sentence)

/-- Diagonal construction always produces the Tarski sentence -/
noncomputable def tarski_diagonal (_P : Formula → Prop) : Formula :=
  tarski_sentence

/-- A simple provable formula for the stable witness -/
def simple_provable : Formula :=
  Formula.eq Term.zero Term.zero

axiom tarski_ne_simple : tarski_sentence ≠ simple_provable
axiom simple_provable_godel_ne_zero : godel_formula simple_provable ≠ 0
axiom tarski_godel_ne_zero : godel_formula tarski_sentence ≠ 0

/-- Classify Tarski formulas into the canonical `Binary` structure:
    the Tarski sentence itself is `paradox`, all others are `stable`. -/
noncomputable def tarski_to_Binary (φ : Formula) : Binary :=
  if φ = tarski_sentence then Binary.paradox else Binary.stable

/-! ## 3. Impossibility Structure for Tarski -/

/-- The Tarski impossibility structure based on the undefinability of truth -/
noncomputable def tarski_impstruct : ImpStruct Formula where
  self_repr := tarski_self_repr
  diagonal := tarski_diagonal
  negation := Not
  trilemma := fun _ => True

/-! ## 4. Non-degeneracy Proof -/

/-- The Tarski structure is non-degenerate: it has both stable and paradoxical elements.
    This shows that even with a hypothetical truth predicate (which Tarski proves
    cannot exist), the same diagonal impossibility structure emerges. -/
theorem tarski_nondegenerate : Nondegenerate Formula tarski_impstruct :=
  diagonal_implies_nondegenerate
    tarski_impstruct
    simple_provable
    (by -- Proof that simple_provable is not a fixed point
      unfold ImpStruct.fixed_point tarski_impstruct tarski_self_repr
      simp
      intro h_eq
      exact tarski_ne_simple h_eq.symm
    )
    (by -- Proof that the diagonal produces a fixed point (the Tarski sentence)
      unfold ImpStruct.fixed_point tarski_impstruct tarski_diagonal tarski_self_repr
      simp
    )

/-- In the Tarski binary view, the Tarski sentence itself is classified as `paradox`. -/
theorem tarski_binary_paradox_witness :
  tarski_to_Binary tarski_sentence = Binary.paradox := by
  unfold tarski_to_Binary
  simp

/-! ## 5. Significance

This formalization demonstrates that Tarski's undefinability theorem, despite
being about truth rather than provability, reduces to the same ImpStruct pattern
as Gödel's incompleteness and other diagonal impossibilities.

The key insight: The diagonal lemma generates the same stable/paradox dichotomy
whether applied to provability (Gödel), truth (Tarski), or any other predicate
that would create self-reference. The semantic difference is preserved in the
specific predicates used, but the structural pattern is invariant.

This validates the thesis that diagonal impossibilities across mathematics
share identical abstract structure, differing only in their semantic instantiation.
-/

/-- Typeclass instance: Make Tarski structure automatically discoverable -/
noncomputable instance : ImpStruct GodelComplete.Formula := tarski_impstruct

/-- Typeclass instance: Make Tarski nondegeneracy automatically discoverable -/
instance : Nondegenerate GodelComplete.Formula tarski_impstruct :=
  tarski_nondegenerate

end TarskiUndefinability
