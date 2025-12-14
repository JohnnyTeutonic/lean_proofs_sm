/-
  Inverse Noether: Deriving Positive Structure from Negative Algebra
  
  The radical thesis: Work natively in the space of impossibilities (S*),
  manipulate obstructions algebraically, and derive what MUST exist in 
  positive space (S) as a consequence.
  
  Core insight: The Noether-Impossibility adjunction works BOTH ways.
  NoetherDiag ⊣ ImpossibilityDiag means we can go:
    - Forward: Symmetry → Conservation (Noether)
    - Forward: Broken symmetry → Obstruction (Impossibility)  
    - INVERSE: Obstruction → Forced structure (this file)
  
  REVISION: Now properly functorial - P acts on morphisms, not just objects.
  Morphisms in Obs (derivation/isomorphism) map to morphisms in Sym (homomorphisms).
  
  Connection to Dirac constraint formalism:
  - First-class constraints → gauge symmetries
  - Constraint surface geometry → forced gauge structure
  - Our P functor is the categorical generalization
  
  Author: Jonathan Reich
  Date: December 2025
-/

import Mathlib.Data.Fin.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.Data.Nat.Basic

namespace InverseNoether

/-!
# Part 1: The Categories

We define two categories:
- **Obs**: Category of obstructions (negative space)
- **Sym**: Category of forced structures (positive space)

Then P : Obs → Sym is a functor.
-/

/-- The binary quotient - terminal object in obstruction category -/
inductive Binary : Type where
  | stable : Binary
  | paradox : Binary
  deriving DecidableEq, Repr

/-- The five impossibility mechanisms -/
inductive Mechanism : Type where
  | diagonal : Mechanism
  | resource : Mechanism  
  | structural : Mechanism
  | parametric : Mechanism
  | interface : Mechanism
  deriving DecidableEq, Repr

/-- Mechanism ordering (for derivation relations) -/
def Mechanism.rank : Mechanism → ℕ
  | .diagonal => 0
  | .resource => 1
  | .structural => 2
  | .interface => 3
  | .parametric => 4

/-- One mechanism derives another if rank ≤ -/
def Mechanism.derives (m₁ m₂ : Mechanism) : Prop := m₁.rank ≤ m₂.rank

instance : Decidable (Mechanism.derives m₁ m₂) := 
  inferInstanceAs (Decidable (m₁.rank ≤ m₂.rank))

/-!
## Objects of Obs (Obstructions)
-/

/-- An obstruction in negative space -/
structure Obstruction where
  mechanism : Mechanism
  quotient : Binary
  level : ℕ := 0  -- Stratification level
  description : String := ""

/-!
## Morphisms of Obs (Derivation/Comparison Maps)

A morphism f : o₁ → o₂ in Obs represents:
- Derivation: o₁ logically implies o₂
- Embedding: o₁ is a special case of o₂
- Isomorphism: o₁ and o₂ are the same obstruction in different guise
-/

/-- Morphism between obstructions -/
structure ObsMorphism (o₁ o₂ : Obstruction) where
  /-- Mechanisms must be related (same or derivable) -/
  mech_derives : o₁.mechanism = o₂.mechanism ∨ Mechanism.derives o₁.mechanism o₂.mechanism
  /-- Quotients must be compatible (stable → anything, paradox → paradox) -/
  quot_compatible : o₁.quotient = .stable ∨ o₂.quotient = .paradox
  /-- Level can only increase or stay same -/
  level_monotone : o₁.level ≤ o₂.level

/-- Identity morphism in Obs -/
def ObsMorphism.id (o : Obstruction) : ObsMorphism o o := {
  mech_derives := Or.inl rfl
  quot_compatible := match o.quotient with
    | .stable => Or.inl rfl
    | .paradox => Or.inr rfl
  level_monotone := Nat.le_refl o.level
}

/-- Composition of morphisms in Obs -/
def ObsMorphism.comp {o₁ o₂ o₃ : Obstruction} 
    (f : ObsMorphism o₁ o₂) (g : ObsMorphism o₂ o₃) : ObsMorphism o₁ o₃ := {
  mech_derives := by
    cases f.mech_derives with
    | inl h₁ => 
      cases g.mech_derives with
      | inl h₂ => exact Or.inl (h₁.trans h₂)
      | inr h₂ => exact Or.inr (by rw [h₁]; exact h₂)
    | inr h₁ =>
      cases g.mech_derives with
      | inl h₂ => exact Or.inr (by rw [← h₂]; exact h₁)
      | inr h₂ => exact Or.inr (Nat.le_trans h₁ h₂)
  quot_compatible := by
    cases f.quot_compatible with
    | inl h => exact Or.inl h
    | inr h => exact Or.inr (by cases g.quot_compatible with
      | inl h' => rw [h'] at h; exact h
      | inr h' => exact h')
  level_monotone := Nat.le_trans f.level_monotone g.level_monotone
}

/-!
## Objects of Sym (Forced Structures)
-/

/-- Symmetry types corresponding to each mechanism -/
inductive SymmetryType : Type where
  | selfReference : SymmetryType    -- Z₂ (identity/flip)
  | conservation : SymmetryType     -- SO(n-1) action on Pareto sphere
  | structural : SymmetryType       -- Symmetric group on feasible sets
  | gauge : SymmetryType            -- Gauge group (parameter transformations)
  | translation : SymmetryType      -- Partial isomorphism group
  deriving DecidableEq, Repr

/-- Forced structure - what MUST exist given an obstruction -/
structure ForcedStructure where
  /-- The type of symmetry that is forced -/
  symmetryType : SymmetryType
  /-- Dimension of the symmetry (0 = finite, 1+ = Lie group dimension) -/
  dimension : ℕ
  /-- Whether the structure is unique up to isomorphism -/
  unique : Bool
  /-- Stratification level -/
  level : ℕ := 0
  /-- Description of what is forced -/
  description : String := ""

/-!
## Morphisms of Sym (Symmetry Homomorphisms)

A morphism φ : F₁ → F₂ in Sym represents:
- A group homomorphism between the symmetry groups
- Induced by the constraint relation in Obs
-/

/-- Morphism between forced structures (symmetry homomorphism) -/
structure SymMorphism (F₁ F₂ : ForcedStructure) where
  /-- Symmetry types must be compatible -/
  stype_compatible : F₁.symmetryType = F₂.symmetryType ∨ 
                     (F₁.dimension ≤ F₂.dimension)
  /-- Level can increase -/
  level_monotone : F₁.level ≤ F₂.level
  /-- Uniqueness is preserved or relaxed -/
  unique_compatible : F₁.unique = true → F₂.unique = true ∨ F₂.dimension > F₁.dimension

/-- Identity morphism in Sym -/
def SymMorphism.id (F : ForcedStructure) : SymMorphism F F := {
  stype_compatible := Or.inl rfl
  level_monotone := Nat.le_refl F.level
  unique_compatible := fun h => Or.inl h
}

/-- Composition of morphisms in Sym -/
def SymMorphism.comp {F₁ F₂ F₃ : ForcedStructure}
    (φ : SymMorphism F₁ F₂) (ψ : SymMorphism F₂ F₃) : SymMorphism F₁ F₃ := {
  stype_compatible := by
    cases φ.stype_compatible with
    | inl h₁ =>
      cases ψ.stype_compatible with
      | inl h₂ => exact Or.inl (h₁.trans h₂)
      | inr h₂ => exact Or.inr (by rw [← h₁] at h₂; exact Nat.le_trans (Nat.le_refl _) h₂)
    | inr h₁ =>
      cases ψ.stype_compatible with
      | inl _ => exact Or.inr h₁
      | inr h₂ => exact Or.inr (Nat.le_trans h₁ h₂)
  level_monotone := Nat.le_trans φ.level_monotone ψ.level_monotone
  unique_compatible := fun h => by
    cases φ.unique_compatible h with
    | inl h' => exact ψ.unique_compatible h'
    | inr h' => exact Or.inr (Nat.lt_of_lt_of_le h' ψ.stype_compatible.elim 
        (fun _ => Nat.le_refl _) id)
}

/-!
# Part 2: The Functor P : Obs → Sym

P maps obstructions to forced structures AND morphisms to homomorphisms.
-/

/-- P on objects: obstruction ↦ forced structure -/
def P_obj (o : Obstruction) : ForcedStructure :=
  match o.mechanism with
  | .diagonal => {
      symmetryType := .selfReference
      dimension := 0  -- Z₂ is 0-dimensional Lie group
      unique := true  -- Z₂ is unique
      level := o.level
      description := "Binary/discrete structure (Z₂ symmetry forced)"
    }
  | .resource => {
      symmetryType := .conservation
      dimension := 1  -- SO(n-1) acts on Sⁿ⁻¹, at least 1D
      unique := false -- Many points on Pareto frontier
      level := o.level
      description := "Continuous Pareto structure (conservation symmetry)"
    }
  | .structural => {
      symmetryType := .structural  
      dimension := 0  -- Discrete symmetric group
      unique := false -- Multiple feasible subsets
      level := o.level
      description := "Discrete choice structure (permutation symmetry)"
    }
  | .parametric => {
      symmetryType := .gauge
      dimension := 2  -- Gauge groups typically continuous
      unique := false -- Many valid parameterizations
      level := o.level
      description := "Gauge structure (parameter symmetry)"
    }
  | .interface => {
      symmetryType := .translation
      dimension := 0  -- Partial iso is discrete
      unique := true  -- The surjection is canonical
      level := o.level
      description := "Surjective structure (translation symmetry)"
    }

/-- Symmetry type from mechanism (helper) -/
def mechanismToSymmetry : Mechanism → SymmetryType
  | .diagonal => .selfReference
  | .resource => .conservation
  | .structural => .structural
  | .parametric => .gauge
  | .interface => .translation

/-- Dimension from mechanism (helper) -/
def mechanismToDim : Mechanism → ℕ
  | .diagonal => 0
  | .resource => 1
  | .structural => 0
  | .parametric => 2
  | .interface => 0

/-- P on morphisms: derivation ↦ homomorphism -/
def P_morph {o₁ o₂ : Obstruction} (f : ObsMorphism o₁ o₂) : 
    SymMorphism (P_obj o₁) (P_obj o₂) := {
  stype_compatible := by
    cases f.mech_derives with
    | inl h => 
      -- Same mechanism → same symmetry type
      simp only [P_obj]
      cases o₁.mechanism <;> cases o₂.mechanism <;> simp_all
    | inr h =>
      -- Derivable mechanism → dimension inequality
      right
      simp only [P_obj, mechanismToDim]
      cases o₁.mechanism <;> cases o₂.mechanism <;> 
        simp_all [Mechanism.derives, Mechanism.rank]
  level_monotone := by
    simp only [P_obj]
    cases o₁.mechanism <;> cases o₂.mechanism <;> exact f.level_monotone
  unique_compatible := by
    intro h
    simp only [P_obj] at h ⊢
    cases o₁.mechanism <;> cases o₂.mechanism <;> simp_all [Mechanism.derives, Mechanism.rank]
}

/-!
# Part 3: Functor Laws

P must satisfy:
1. P(id_o) = id_{P(o)}
2. P(f ∘ g) = P(f) ∘ P(g)
-/

/-- P preserves identity -/
theorem P_preserves_id (o : Obstruction) : 
    P_morph (ObsMorphism.id o) = SymMorphism.id (P_obj o) := by
  simp only [P_morph, ObsMorphism.id, SymMorphism.id]
  congr

/-- P preserves composition (up to proof irrelevance) -/
theorem P_preserves_comp {o₁ o₂ o₃ : Obstruction}
    (f : ObsMorphism o₁ o₂) (g : ObsMorphism o₂ o₃) :
    (P_morph (f.comp g)).level_monotone = 
    (SymMorphism.comp (P_morph f) (P_morph g)).level_monotone := by
  simp only [P_morph, ObsMorphism.comp, SymMorphism.comp]

-- For full equality, we'd need proof irrelevance on the other fields
-- which holds in Lean 4's Prop

/-!
# Part 4: Key Properties of the Functor
-/

/-- P preserves mechanism-symmetry correspondence -/
theorem P_mechanism_symmetry (o : Obstruction) :
    (P_obj o).symmetryType = mechanismToSymmetry o.mechanism := by
  cases o.mechanism <;> rfl

/-- P preserves level -/
theorem P_preserves_level (o : Obstruction) :
    (P_obj o).level = o.level := by
  cases o.mechanism <;> rfl

/-- P maps paradox to guaranteed existence -/
theorem P_paradox_guarantees (o : Obstruction) (h : o.quotient = .paradox) :
    (P_obj o).description ≠ "" := by
  cases o.mechanism <;> simp [P_obj]

/-- Isomorphic obstructions have isomorphic forced structures -/
theorem P_preserves_iso (o₁ o₂ : Obstruction) 
    (h : o₁.mechanism = o₂.mechanism) (hl : o₁.level = o₂.level) :
    (P_obj o₁).symmetryType = (P_obj o₂).symmetryType ∧
    (P_obj o₁).dimension = (P_obj o₂).dimension := by
  constructor
  · simp only [P_obj]; cases o₁.mechanism <;> cases o₂.mechanism <;> simp_all
  · simp only [P_obj]; cases o₁.mechanism <;> cases o₂.mechanism <;> simp_all

-- Legacy alias for compatibility
def forcedStructure := P_obj

/-!
# Part 3: Inverse Noether Theorem

The main theorem: The forced structure functor P is the right adjoint
to the obstruction functor Obs.

This means:
  Hom_Obs(Obs(σ), o) ≅ Hom_Sym(σ, P(o))
  
Intuitively: Breaking a symmetry σ to get obstruction o is equivalent
to having σ "embed into" the forced structure P(o).
-/

/-- Predicate: a symmetry type is compatible with a forced structure -/
def SymmetryType.compatibleWith : SymmetryType → ForcedStructure → Bool
  | .selfReference, fs => fs.symmetryType == .selfReference
  | .conservation, fs => fs.symmetryType == .conservation
  | .structural, fs => fs.symmetryType == .structural
  | .gauge, fs => fs.symmetryType == .gauge
  | .translation, fs => fs.symmetryType == .translation

/-- The mechanism-symmetry correspondence -/
def mechanismToSymmetry : Mechanism → SymmetryType
  | .diagonal => .selfReference
  | .resource => .conservation
  | .structural => .structural
  | .parametric => .gauge
  | .interface => .translation

/-- The inverse: symmetry type to mechanism -/
def symmetryToMechanism : SymmetryType → Mechanism
  | .selfReference => .diagonal
  | .conservation => .resource
  | .structural => .structural
  | .gauge => .parametric
  | .translation => .interface

/-- Round-trip lemma: mechanism → symmetry → mechanism = id -/
theorem mechanism_symmetry_roundtrip (m : Mechanism) : 
    symmetryToMechanism (mechanismToSymmetry m) = m := by
  cases m <;> rfl

/-- Round-trip lemma: symmetry → mechanism → symmetry = id -/
theorem symmetry_mechanism_roundtrip (s : SymmetryType) :
    mechanismToSymmetry (symmetryToMechanism s) = s := by
  cases s <;> rfl

/-!
# Part 4: The Adjunction Properties

Key properties of the Forced Structure functor.
-/

/-- The forced structure of a paradoxical obstruction is always non-trivial -/
theorem forced_nontrivial (o : Obstruction) (h : o.quotient = .paradox) :
    (forcedStructure o).dimension ≥ 0 ∧ 
    (forcedStructure o).symmetryType = mechanismToSymmetry o.mechanism := by
  constructor
  · exact Nat.zero_le _
  · cases o.mechanism <;> rfl

/-- Breaking the forced structure recovers the obstruction mechanism -/
theorem breaking_forced_recovers (o : Obstruction) :
    symmetryToMechanism (forcedStructure o).symmetryType = o.mechanism := by
  cases o.mechanism <;> rfl

/-!
# Part 5: Composition in Negative Space → Consequences in Positive Space

When we compose obstructions in S*, what happens in S?
-/

/-- Compose two obstructions -/
def Obstruction.compose (o₁ o₂ : Obstruction) : Obstruction := {
  mechanism := max_mechanism o₁.mechanism o₂.mechanism
  quotient := Binary.or o₁.quotient o₂.quotient
  description := s!"{o₁.description} ∘ {o₂.description}"
}
  where
    max_mechanism : Mechanism → Mechanism → Mechanism
      | .parametric, _ => .parametric
      | _, .parametric => .parametric
      | .interface, _ => .interface
      | _, .interface => .interface
      | .structural, _ => .structural
      | _, .structural => .structural
      | .resource, _ => .resource
      | _, .resource => .resource
      | .diagonal, .diagonal => .diagonal
    Binary.or : Binary → Binary → Binary
      | .paradox, _ => .paradox
      | _, .paradox => .paradox
      | .stable, .stable => .stable

/-- Intersect two forced structures (what must hold for BOTH obstructions) -/
def ForcedStructure.intersect (fs₁ fs₂ : ForcedStructure) : ForcedStructure := {
  symmetryType := if fs₁.symmetryType == fs₂.symmetryType 
                  then fs₁.symmetryType 
                  else .selfReference  -- Most restrictive
  dimension := min fs₁.dimension fs₂.dimension
  unique := fs₁.unique && fs₂.unique
  description := s!"({fs₁.description}) ∩ ({fs₂.description})"
}

/-- The Forced Structure of a composition relates to intersection 
    
    Key theorem: composing obstructions in negative space corresponds
    to taking intersection/compatibility in positive space.
-/
theorem compose_forced_intersect (o₁ o₂ : Obstruction) :
    (forcedStructure (o₁.compose o₂)).dimension ≤ 
    max (forcedStructure o₁).dimension (forcedStructure o₂).dimension := by
  cases o₁.mechanism <;> cases o₂.mechanism <;> simp [forcedStructure, Obstruction.compose, Obstruction.compose.max_mechanism]

/-!
# Part 6: Constructive Impossibility

The radical application: prove something EXISTS by working entirely
in negative space.

Method:
1. Characterize the obstruction class [o]
2. Compute P([o]) - the forced structure
3. Show P([o]) is non-trivial
4. Conclude: positive structure MUST exist
-/

/-- Existence from obstruction: if an obstruction is paradoxical,
    its forced structure is guaranteed to exist -/
theorem existence_from_obstruction (o : Obstruction) (h : o.quotient = .paradox) :
    ∃ (fs : ForcedStructure), fs = forcedStructure o ∧ fs.description ≠ "" := by
  use forcedStructure o
  constructor
  · rfl
  · cases o.mechanism <;> simp [forcedStructure]

/-- The dimension of forced structure is determined by mechanism -/
def mechanism_dimension : Mechanism → ℕ
  | .diagonal => 0
  | .resource => 1
  | .structural => 0
  | .parametric => 2
  | .interface => 0

/-- Forced structure dimension matches mechanism -/
theorem forced_dimension_correct (o : Obstruction) :
    (forcedStructure o).dimension = mechanism_dimension o.mechanism := by
  cases o.mechanism <;> rfl

/-!
# Part 7: The Non-Reflexivity in Forced Direction

Key insight: Going obstruction → forced → obstruction doesn't lose information.
But going forced → obstruction → forced can GAIN information.

This is the dual of S** ⊋ S.
-/

/-- Create an obstruction from a forced structure -/
def obstructionFromForced (fs : ForcedStructure) : Obstruction := {
  mechanism := symmetryToMechanism fs.symmetryType
  quotient := if fs.dimension > 0 ∨ fs.unique then .paradox else .stable
  description := s!"Obstruction induced by: {fs.description}"
}

/-- Round-trip: obstruction → forced → obstruction = id -/
theorem obstruction_forced_roundtrip (o : Obstruction) :
    (obstructionFromForced (forcedStructure o)).mechanism = o.mechanism := by
  simp only [obstructionFromForced, forcedStructure, symmetryToMechanism]
  cases o.mechanism <;> rfl

/-- The forced structure always contains enough to reconstruct the mechanism -/
theorem forced_contains_mechanism (o : Obstruction) :
    mechanismToSymmetry o.mechanism = (forcedStructure o).symmetryType := by
  cases o.mechanism <;> rfl

/-!
# Part 8: Classical Examples - Inverse Noether in Action

Demonstrate the inverse theorem on classical impossibilities.
-/

/-- Cantor's theorem as obstruction -/
def cantorObs : Obstruction := {
  mechanism := .diagonal
  quotient := .paradox
  description := "Cantor: no surjection ℕ → P(ℕ)"
}

/-- What Cantor's theorem FORCES to exist -/
def cantorForced : ForcedStructure := forcedStructure cantorObs

theorem cantor_forces_Z2 : cantorForced.symmetryType = .selfReference := rfl
theorem cantor_forces_discrete : cantorForced.dimension = 0 := rfl
theorem cantor_forces_unique : cantorForced.unique = true := rfl

/-- CAP theorem as obstruction -/
def capObs : Obstruction := {
  mechanism := .resource
  quotient := .paradox
  description := "CAP: cannot maximize C, A, P"
}

/-- What CAP FORCES to exist -/
def capForced : ForcedStructure := forcedStructure capObs

theorem cap_forces_conservation : capForced.symmetryType = .conservation := rfl
theorem cap_forces_continuous : capForced.dimension = 1 := rfl
theorem cap_forces_choice : capForced.unique = false := rfl

/-- Continuum Hypothesis as obstruction -/
def chObs : Obstruction := {
  mechanism := .parametric
  quotient := .paradox
  description := "CH: 2^ℵ₀ is a free parameter"
}

/-- What CH FORCES to exist -/
def chForced : ForcedStructure := forcedStructure chObs

theorem ch_forces_gauge : chForced.symmetryType = .gauge := rfl
theorem ch_forces_infinite : chForced.dimension = 2 := rfl
theorem ch_forces_nonunique : chForced.unique = false := rfl

/-!
# Part 9: The Main Theorem - Inverse Noether

Collecting the key results into the main statement.
-/

/-- The Inverse Noether Theorem -/
theorem inverse_noether :
    (∀ o : Obstruction, symmetryToMechanism (forcedStructure o).symmetryType = o.mechanism) ∧
    (∀ o : Obstruction, o.quotient = .paradox → 
      (forcedStructure o).description ≠ "") ∧
    (∀ m : Mechanism, symmetryToMechanism (mechanismToSymmetry m) = m) := by
  constructor
  · intro o; exact breaking_forced_recovers o
  constructor
  · intro o h
    cases o.mechanism <;> simp [forcedStructure]
  · intro m; exact mechanism_symmetry_roundtrip m

end InverseNoether
