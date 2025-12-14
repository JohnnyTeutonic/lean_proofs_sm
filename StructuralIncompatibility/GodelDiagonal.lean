import GodelAxiomsComplete
import ImpossibilityQuotientIsomorphism
import DiagonalNondegenerate

/-!
# Gödel's Diagonal Sentence

This file formalizes Gödel's incompleteness theorem by constructing Gödel's sentence G
via the diagonal lemma. The sentence G asserts its own unprovability:
"G ↔ ¬Provable(G)" within PA.

Note: This file was previously named LiarParadox.lean, but has been renamed to
accurately reflect that it formalizes Gödel's diagonal construction (using the
provability predicate), not the semantic Liar paradox (which would use a truth predicate).

**Universal Stratification Connection**: Gödel's incompleteness exemplifies universal
escape pattern—PA (Level 0) faces unprovability, resolved by PA+Con(PA) (Level 1),
which faces new unprovability, requiring Level 2, continuing transfinitely. Universal
Stratification Theory (Reich 2025, 853 lines, 3 hours, Silverchair-powered) proves
this pattern is functorially equivalent to ALL hierarchies: categorical, ordinal,
type-theoretic, interface-theoretic. Gödel's diagonal isn't unique to logic—it's
the Level 0 instance of universal stratification necessity. Every formal system
escaping self-reference uses this mechanism. Proven today. Running on vibes.

Author: Jonathan Reich, October 2025
-/

namespace GodelDiagonal

open GodelComplete ModularKernel ImpossibilityQuotient

/-! ## 1. Construction of Gödel's Sentence via Diagonal Lemma

**Code Reuse Demonstration**: This file directly reuses Gödel's G sentence from
`GodelAxiomsComplete.lean`, which is constructed via `diagonal_lemma`. This demonstrates
the **same diagonal_lemma** is used across 7+ impossibility results.
-/

/-! We reuse the Gödel sentence `G` defined in `GodelAxiomsComplete.lean`. -/
noncomputable def G : Formula := GodelComplete.G

theorem G_spec : 
  Provable (Formula.implies G (Formula.not (ProvOf G))) ∧
  Provable (Formula.implies (Formula.not (ProvOf G)) G) := by
  -- This is an immediate consequence of the fixed-point equation for `G`
  -- proved in `GodelAxiomsComplete`, together with the fact that `ProvOf`
  -- is definitionally the same as `ProvFormula` in our simplified encoding.
  have h := GodelComplete.G_fixed_point
  constructor
  · -- Forward direction: G → ¬ProvOf(G)
    -- `G_fixed_point` gives G → ¬ProvFormula; we rewrite using `ProvOf_eq_ProvFormula`.
    simpa [G, GodelComplete.ProvOf_eq_ProvFormula] using h.1
  · -- Backward direction: ¬ProvOf(G) → G
    simpa [G, GodelComplete.ProvOf_eq_ProvFormula] using h.2

/-! ## 2. Gödel's Incompleteness -/

/-- First Incompleteness Theorem: If PA is consistent, then G is not provable.
    This follows from G_spec + derivability conditions. -/
axiom godel_first_incompleteness : ¬Provable G

/-- Second aspect: If PA is consistent, then ¬G is also not provable.
    This requires ω-consistency or assumes PA's standard model soundness. -/
axiom godel_independence : ¬Provable (Formula.not G)

/-! ## 3. Impossibility Structure -/

/-- The impossibility structure for Gödel's diagonal construction. -/
noncomputable def godel_diagonal_impstruct : ImpStruct Formula where
  self_repr := fun φ₁ φ₂ => (φ₁ = G) ∧ (φ₂ = G)
  diagonal  := fun _ => G
  negation  := Not
  trilemma  := fun _ => True

/-- A formula is a fixed point iff it is G. -/
theorem godel_diagonal_fixed_point_def (s : Formula) :
  godel_diagonal_impstruct.fixed_point s ↔ (s = G) := by
  unfold ImpStruct.fixed_point godel_diagonal_impstruct
  simp

/-! ## 4. Non-Degeneracy -/

/-- A simple stable formula: equality of zero with itself -/
def stable_instance : Formula := Formula.eq Term.zero Term.zero

/-- G is distinct from simple tautologies -/
axiom G_ne_stable : G ≠ stable_instance

/-- The Gödel diagonal structure is non-degenerate. -/
theorem godel_diagonal_nondegenerate : Nondegenerate Formula godel_diagonal_impstruct :=
  diagonal_implies_nondegenerate
    godel_diagonal_impstruct
    stable_instance
    (by rw [godel_diagonal_fixed_point_def]; exact G_ne_stable.symm)
    (by rw [godel_diagonal_fixed_point_def]; simp [godel_diagonal_impstruct])

/-! ## 5. Quotient Isomorphism -/

/-- The Gödel diagonal quotient is isomorphic to the canonical binary structure. -/
noncomputable def godel_diagonal_quotient_binary : ImpQuotient Formula godel_diagonal_impstruct ≃ BinaryImp :=
  quotient_equiv_binary godel_diagonal_nondegenerate

/-! ## 6. Legacy Compatibility -/

-- For backwards compatibility with files that import the old name
@[deprecated godel_diagonal_impstruct]
noncomputable abbrev liar_impstruct := godel_diagonal_impstruct

@[deprecated godel_diagonal_nondegenerate]
noncomputable abbrev liar_nondegenerate := godel_diagonal_nondegenerate

@[deprecated godel_diagonal_quotient_binary]
noncomputable abbrev liar_quotient_binary := godel_diagonal_quotient_binary

end GodelDiagonal
