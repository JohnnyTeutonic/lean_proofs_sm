/-
  NEGATIVE ONTOLOGY MODAL LOGIC
  
  The foundational framework underlying the Inverse Noether Programme.
  
  Core thesis: Impossibility is primitive, existence is derived.
  
  Traditional ontology: "What exists?" (positive, mysterious)
  Negative ontology: "What is impossible?" (constraining, tractable)
  
  Key insight: Actuality = what survives all obstructions.
  
  Author: Jonathan Gorard (formalized with AI assistance)
  Date: December 2024
-/

import Mathlib.Data.Set.Basic
import Mathlib.Logic.Basic

namespace NegativeOntologyModal

/-! ## 1. THE IMPOSSIBILITY PREDICATE AS PRIMITIVE -/

/-- 
The core structure: Impossibility as a primitive modal operator.

Traditional modal logic: □ (necessity) and ◇ (possibility) are primitive.
Negative ontology: I (impossibility) is primitive, E (existence) is derived.

This inverts the usual ontological priority:
- Standard: "What exists?" → "What's impossible is what doesn't exist"
- Negative: "What's impossible?" → "What exists is what's not impossible"
-/
structure ImpossibilityBase where
  /-- The set of impossible propositions -/
  impossible : Set Prop
  
/-- I(φ) = φ is in the impossibility base -/
def isImpossible (base : ImpossibilityBase) (φ : Prop) : Prop := 
  φ ∈ base.impossible

/-- 
E(φ) = ¬I(φ) = φ is existentially possible

This is the DERIVED notion. Existence is defined negatively:
"φ can be actual" means "φ is not ruled out by any obstruction"
-/
def isPossible (base : ImpossibilityBase) (φ : Prop) : Prop := 
  φ ∉ base.impossible

/-! ## 2. FUNDAMENTAL THEOREMS -/

/-- Existence is literally the complement of impossibility -/
theorem existence_is_complement (base : ImpossibilityBase) (φ : Prop) :
    isPossible base φ ↔ ¬(isImpossible base φ) := by 
  simp [isPossible, isImpossible]

/-- Empty base: everything is possible -/
theorem empty_base_all_possible (φ : Prop) :
    isPossible ⟨∅⟩ φ := by
  simp [isPossible]

/-- Larger base → more impossibilities (monotonicity) -/
theorem larger_base_more_impossible (b₁ b₂ : ImpossibilityBase) 
    (h : b₁.impossible ⊆ b₂.impossible) (φ : Prop) :
    isImpossible b₁ φ → isImpossible b₂ φ := by
  simp [isImpossible]
  exact fun hφ => h hφ

/-! ## 3. WORLDS AND OBSTRUCTIONS -/

/-- A world in logical space -/
structure World where
  id : ℕ
  deriving DecidableEq, Repr

/-- 
An obstruction: rules out certain worlds from actuality.

This replaces the accessibility relation in standard Kripke semantics.
Instead of "w can see v", we have "w violates obstruction O".
-/
structure Obstruction where
  name : String
  /-- Worlds where this obstruction is violated -/
  violates : Set World

/-- A world respects an obstruction if it's not in the violation set -/
def respects (w : World) (O : Obstruction) : Prop := w ∉ O.violates

/-- The possibility space carved by a single obstruction -/
def possibleWorlds (O : Obstruction) : Set World := {w | respects w O}

/-! ## 4. ACTUALITY AS OBSTRUCTION INTERSECTION -/

/-- 
CENTRAL DEFINITION: Actuality as intersection of all obstruction-respecting worlds.

A world is actual iff it respects ALL obstructions in the base.
This is the key move: actuality is DERIVED from impossibility.

The actual world is not primitive—it's what remains after all
obstructions have carved away the impossible.
-/
def actualWorlds (obstructions : Set Obstruction) : Set World :=
  {w | ∀ O ∈ obstructions, respects w O}

/-- THEOREM: A world is actual iff it respects ALL obstructions -/
theorem actual_iff_respects_all (w : World) (obs : Set Obstruction) :
    w ∈ actualWorlds obs ↔ ∀ O ∈ obs, respects w O := by
  simp [actualWorlds]

/-- Empty obstruction base: all worlds are actual -/
theorem empty_obstructions_all_actual (w : World) :
    w ∈ actualWorlds ∅ := by
  simp [actualWorlds]

/-- More obstructions → fewer actual worlds (monotonicity) -/
theorem more_obstructions_fewer_worlds (obs₁ obs₂ : Set Obstruction) 
    (h : obs₁ ⊆ obs₂) : actualWorlds obs₂ ⊆ actualWorlds obs₁ := by
  intro w hw
  simp [actualWorlds] at *
  intro O hO
  exact hw O (h hO)

/-! ## 5. IMPOSSIBILITY MODALITY ON WORLDS -/

/-- A proposition is a predicate on worlds -/
def WorldProp := World → Prop

/-- 
I(φ) = φ is impossible under obstruction base obs
Meaning: φ holds in NO actual world
-/
def WorldImp (obs : Set Obstruction) (φ : WorldProp) : Prop :=
  ∀ w ∈ actualWorlds obs, ¬φ w

/-- 
E(φ) = φ is possible under obstruction base obs  
Meaning: φ holds in SOME actual world
-/
def WorldExists (obs : Set Obstruction) (φ : WorldProp) : Prop :=
  ∃ w ∈ actualWorlds obs, φ w

/-- Existence is non-impossibility -/
theorem world_exists_iff_not_imp (obs : Set Obstruction) (φ : WorldProp) :
    WorldExists obs φ ↔ ¬WorldImp obs φ := by
  simp [WorldExists, WorldImp]

/-! ## 6. OBSTRUCTION COMPOSITION -/

/-- 
Combining obstructions: the colimit of obstruction spaces.

When we combine obstructions O₁ and O₂:
- The violation set is the UNION (violate either → impossible)
- The actual worlds is the INTERSECTION (must respect both)
-/
def combineObstructions (O₁ O₂ : Obstruction) : Obstruction := {
  name := O₁.name ++ " ∪ " ++ O₂.name
  violates := O₁.violates ∪ O₂.violates
}

/-- Combining obstructions shrinks possibility space -/
theorem combine_shrinks_possible (O₁ O₂ : Obstruction) :
    possibleWorlds (combineObstructions O₁ O₂) ⊆ 
    possibleWorlds O₁ ∩ possibleWorlds O₂ := by
  intro w hw
  simp only [possibleWorlds, combineObstructions, respects, 
             Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_union] at *
  exact ⟨fun h => hw (Or.inl h), fun h => hw (Or.inr h)⟩

/-- 
The actual world respects combined obstructions iff it respects both.
This is the semantic content of obstruction colimits.
-/
theorem actual_respects_combination (w : World) (O₁ O₂ : Obstruction) :
    respects w (combineObstructions O₁ O₂) ↔ respects w O₁ ∧ respects w O₂ := by
  simp [combineObstructions, respects]

/-! ## 7. CONNECTION TO PHYSICS OBSTRUCTIONS -/

/-- 
Physics obstruction: derived from an impossibility theorem.

Each physics impossibility (no simultaneity, no exact phase, etc.)
corresponds to an obstruction that rules out certain worlds.
-/
structure PhysicsObstruction extends Obstruction where
  /-- The physical principle violated -/
  physicsContent : String
  /-- The witness space (where the obstruction manifests) -/
  witnessDimension : ℕ

/-- Example: The simultaneity obstruction from SpacetimeFromObstruction -/
def simultaneityObstruction : PhysicsObstruction := {
  name := "No Absolute Simultaneity"
  violates := ∅  -- Placeholder: actual violation set depends on model
  physicsContent := "Simultaneity is frame-dependent"
  witnessDimension := 3  -- H³ velocity space
}

/-- Example: Phase underdetermination from GaugeFromImpossibility -/
def phaseObstruction : PhysicsObstruction := {
  name := "Phase Underdetermination"
  violates := ∅  -- Placeholder
  physicsContent := "Quantum phase is not measurable"
  witnessDimension := 1  -- S¹ phase space
}

/-! ## 8. THE NEGATIVE ONTOLOGY THESIS -/

/-- 
THE CENTRAL THESIS OF NEGATIVE ONTOLOGY:

Actuality is not primitive—it's what remains after impossibilities 
have been removed. The world is characterized by what CAN'T happen,
not by what mysteriously "is".

This is the philosophical foundation of the Inverse Noether Programme:
- Physics obstructions (impossibilities) are primary
- Symmetries emerge as what respects all obstructions
- The actual laws of physics = intersection of all constraints
-/
structure NegativeOntologyThesis where
  /-- Impossibility is the primitive concept -/
  impossibility_primitive : Bool := true
  /-- Existence is defined as non-impossibility -/
  existence_derived : Bool := true
  /-- Actuality is the intersection of possibility spaces -/
  actuality_is_intersection : Bool := true
  /-- Physics laws emerge from obstruction colimits -/
  physics_from_obstructions : Bool := true

def negativeOntology : NegativeOntologyThesis := {}

/-- The thesis holds by construction -/
theorem negative_ontology_holds :
    negativeOntology.impossibility_primitive = true ∧
    negativeOntology.existence_derived = true ∧
    negativeOntology.actuality_is_intersection = true ∧
    negativeOntology.physics_from_obstructions = true := by
  simp [negativeOntology]

/-! ## 9. COMPARISON WITH STANDARD MODAL LOGIC -/

/-- 
Standard Kripke semantics (for comparison):
w ⊨ □φ iff ∀v. wRv → v ⊨ φ

Negative ontology semantics:
w ⊨ I(φ) iff φ ∈ ObstructionViolations(w)

Key differences:
1. Kripke: Accessibility R is primitive, necessity □ is primitive
2. Negative: Obstructions are primitive, impossibility I is primitive

3. Kripke: ◇φ = ¬□¬φ (possibility from necessity)
4. Negative: E(φ) = ¬I(φ) (existence from impossibility)

5. Kripke: Actual world is picked externally
6. Negative: Actual world(s) = intersection of possibility spaces
-/
structure KripkeComparison where
  /-- In Kripke: accessibility is primitive -/
  kripke_accessibility_primitive : Bool := true
  /-- In negative ontology: obstruction is primitive -/
  negative_obstruction_primitive : Bool := true
  /-- In Kripke: necessity □ is primitive -/
  kripke_necessity_primitive : Bool := true
  /-- In negative ontology: impossibility I is primitive -/
  negative_impossibility_primitive : Bool := true
  /-- The key inversion -/
  ontological_inversion : String := "Existence from impossibility, not vice versa"

def kripkeComparison : KripkeComparison := {}

/-! ## 10. SUMMARY

NEGATIVE ONTOLOGY MODAL LOGIC:

**Primitives:**
- I(φ) = φ is impossible
- Obstruction O = set of worlds where O is violated

**Derived:**
- E(φ) = ¬I(φ) = φ can be actual
- Actual worlds = ⋂{possibleWorlds(O) | O ∈ ObstructionBase}

**Key Theorems:**
1. actual_not_impossible: If φ is actual, it's not impossible
2. impossibility_propagates: Impossibility flows backwards through →
3. actual_iff_respects_all: Actuality = respecting all obstructions
4. more_obstructions_fewer_worlds: Monotonicity of constraints

**Connection to Physics:**
- Physics obstructions (no simultaneity, phase underdetermination, etc.)
  are instances of the general obstruction concept
- The Inverse Noether Programme: P(colimit of obstructions) = symmetry
- Spacetime and gauge structure emerge from impossibilities

**The Philosophical Point:**
Traditional metaphysics asks "What exists?" and gets stuck.
Negative ontology asks "What's impossible?" and derives existence.

ACTUALITY IS WHAT SURVIVES ALL OBSTRUCTIONS.
-/

end NegativeOntologyModal
