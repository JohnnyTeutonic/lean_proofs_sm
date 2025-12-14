/-
  LinguisticHierarchy.lean
  ========================
  
  HIERARCHY CLOSURE IMPOSSIBILITY THEOREM
  
  Machine-verified proof that *ABA patterns are impossible in linguistic
  hierarchies due to closure under structural containment.
  
  This unifies Bobaljik's *ABA generalization with other hierarchy constraints.
  
  Author: Jonathan Reich
  Date: December 2025
  Status: PROVEN (0 sorrys)
-/

namespace LinguisticHierarchy

/-! ## 1. Three-Level Hierarchy -/

inductive Level : Type where
  | pos : Level   -- Positive (lowest)
  | comp : Level  -- Comparative (middle)
  | sup : Level   -- Superlative (highest)
  deriving DecidableEq, Repr

/-! ## 2. Patterns -/

abbrev Pattern := Level → Bool

def isStarABA (p : Pattern) : Prop :=
  p .pos = p .sup ∧ p .pos ≠ p .comp

def isStarAAB (p : Pattern) : Prop :=
  p .pos = p .comp ∧ p .pos ≠ p .sup

/-! ## 3. Bidirectional Closure

Key insight: In Bobaljik's containment structure [Sup [Comp [Root]]]:
- Downward: If sup triggers suppletion, comp (contained) also does
- Upward: If comp triggers suppletion, sup (containing) also shows it

This means: F .comp = true ↔ F .sup = true
-/

structure BidirectionalClosed (F : Pattern) : Prop where
  comp_to_sup : F .comp = true → F .sup = true
  sup_to_comp : F .sup = true → F .comp = true

/-! ## 4. Core Lemma -/

theorem comp_eq_sup (F : Pattern) (hbc : BidirectionalClosed F) :
    F .comp = F .sup := by
  cases hC : F .comp <;> cases hS : F .sup
  · rfl
  · have := hbc.sup_to_comp hS; simp_all
  · have := hbc.comp_to_sup hC; simp_all
  · rfl

/-! ## 5. Main Impossibility Theorems -/

theorem no_star_ABA (F : Pattern) (hbc : BidirectionalClosed F) :
    ¬isStarABA F := by
  intro ⟨hPosEqSup, hPosNeComp⟩
  have hCeqS := comp_eq_sup F hbc
  rw [← hCeqS] at hPosEqSup
  exact hPosNeComp hPosEqSup

theorem no_star_AAB (F : Pattern) (hbc : BidirectionalClosed F) :
    ¬isStarAAB F := by
  intro ⟨hPosEqComp, hPosNeSup⟩
  have hCeqS := comp_eq_sup F hbc
  rw [hCeqS] at hPosEqComp
  exact hPosNeSup hPosEqComp

/-! ## 6. Bobaljik's Complete Theorem -/

structure BobaljikConstraints (F : Pattern) : Prop extends BidirectionalClosed F where
  pos_is_base : F .pos = false

theorem bobaljik_patterns (F : Pattern) (hb : BobaljikConstraints F) :
    (F .pos = false ∧ F .comp = false ∧ F .sup = false) ∨
    (F .pos = false ∧ F .comp = true ∧ F .sup = true) := by
  have hCeqS := comp_eq_sup F hb.toBidirectionalClosed
  have hPos := hb.pos_is_base
  cases hC : F .comp
  · left; simp_all
  · right; simp_all

theorem bobaljik_no_ABA (F : Pattern) (hb : BobaljikConstraints F) :
    ¬isStarABA F := no_star_ABA F hb.toBidirectionalClosed

theorem bobaljik_no_AAB (F : Pattern) (hb : BobaljikConstraints F) :
    ¬isStarAAB F := no_star_AAB F hb.toBidirectionalClosed

/-! ## 7. Summary

PROVEN with 0 sorrys:
- *ABA impossible under bidirectional closure
- *AAB impossible under bidirectional closure  
- Only AAA and ABB patterns possible under Bobaljik constraints

MECHANISM: Structural impossibility from containment hierarchy
-/

end LinguisticHierarchy
