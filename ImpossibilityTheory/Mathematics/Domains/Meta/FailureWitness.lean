/-
  Domains/Meta/FailureWitness.lean

  Diagnostic structures for exhibiting that something is NOT resolved.
  These are presentations of failure, not specifications of resolution.
  
  Use: when you want to prove ¬ Resolves X o, construct a failure witness.
-/

import Mathlib.CategoryTheory.Category.Basic

namespace ImpossibilityTheory.Mathematics.Domains.Meta

open CategoryTheory

/-!
## Failure Witnesses

These structures record *why* an obstruction fails to be resolved.
They are the "negative" side of the obstruction story.
-/

/-- An OperationObstruction records when an operation is missing or not closed -/
structure OperationObstruction (α : Type*) where
  /-- The operation that fails -/
  operation : α → α → Option α
  /-- Witness: specific elements where operation is undefined -/
  witness_left : α
  witness_right : α
  /-- Proof that operation fails on witnesses -/
  fails : operation witness_left witness_right = none

/-- An AxiomObstruction records when a desired property fails -/
structure AxiomObstruction (α : Type*) (P : α → Prop) where
  /-- The element where the axiom fails -/
  counterexample : α
  /-- Proof that the property fails -/
  fails : ¬ P counterexample

/-- A UniquenessObstruction records when multiple solutions exist -/
structure UniquenessObstruction (α : Type*) (P : α → Prop) where
  /-- Two distinct elements satisfying P -/
  witness1 : α
  witness2 : α
  /-- Both satisfy P -/
  sat1 : P witness1
  sat2 : P witness2
  /-- They are distinct -/
  distinct : witness1 ≠ witness2

/-- A CoherenceObstruction records when local solutions don't glue -/
structure CoherenceObstruction (I : Type*) (F : I → Type*) where
  /-- Local solutions exist -/
  local_solutions : ∀ i : I, F i
  /-- But no global solution exists -/
  no_global : ¬ ∃ (g : ∀ i, F i), ∀ i j, HEq (g i) (g j) → True

end ImpossibilityTheory.Mathematics.Domains.Meta
