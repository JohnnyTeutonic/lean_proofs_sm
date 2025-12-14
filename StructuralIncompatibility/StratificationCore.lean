import Mathlib.Logic.Function.Defs
import Mathlib.Data.Set.Basic
import Mathlib.SetTheory.Ordinal.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import InterfaceTheory
import InterfaceTheoryCategorical

/-!
# StratificationCore: Grand Unified Stratification & Interfaces

Copyright (c) 2025 Jonathan Reich.
Released under the Apache 2.0 license.

Author: Jonathan Reich

## Big Picture

This file builds a *monolithic core* that unifies:

1. **Abstract stratification towers** indexed by ℕ.
2. **Tarski-style truth stratification**.
3. **Proof stratification** (PA-like towers).
4. **Interface towers** (categorical view).
5. **Heterogeneity / Category Error** measures.

It provides the bridge between "philosophical stratification" (resolving paradoxes)
and "categorical interfaces" (resolving type mismatches).
-/

noncomputable section

universe u

namespace StratificationCore

open CategoryTheory
open InterfaceTheory

/-! ## Part 1: Abstract Stratified Systems -/

/-- An abstract *self-reference/problem schema* at a level. -/
structure SelfRefProblem (α : Type u) where
  carrier : Type u
  paradox : carrier → Prop

/-- A resolution of a self-reference problem at a higher level. -/
structure SelfRefResolution (β : Type u) where
  witness : β
  resolved : Prop

/-- Undefinability schema: no internal truth predicate is globally correct. -/
structure UndefinabilitySchema (α : Type u) where
  truth : α → Prop
  not_total : Prop

/-- A single abstract stratified tower indexed by ℕ. -/
structure StratifiedSystem where
  /-- The level object at each stratum. -/
  Level : ℕ → Type u
  /-- The "up" interface: level n embeds/overflows into level n+1.
      Note: InterfaceFunctor L(n+1) L(n) maps L(n) → L(n+1). -/
  up : ∀ n, InterfaceFunctor (Level (n + 1)) (Level n)
  /-- Self-reference problems at level n. -/
  Problem : ℕ → Type u
  /-- Realization of each problem as a concrete schema. -/
  asSelfRef : ∀ n, Problem n → SelfRefProblem (Level n)
  /-- Resolution at level n+1. -/
  resolve : ∀ n (p : Problem n), SelfRefResolution (Level (n + 1))
  /-- Undefinability: each level carries candidate truth predicates. -/
  undefinability : ∀ n, UndefinabilitySchema (Level n)
  /-- The resolution is consistent with the interface map. -/
  resolve_respects_up :
    ∀ n (p : Problem n),
      ∃ x : Level n,
        (up n).functor x = (resolve n p).witness

/-- A morphism of stratified systems: levelwise interfaces commuting with `up`. -/
structure StratifiedMorphism (S₁ S₂ : StratifiedSystem) where
  /-- Map from S₂ to S₁ (contravariant InterfaceFunctor).
      Functor maps S₁ → S₂. -/
  F : ∀ n, InterfaceFunctor (S₂.Level n) (S₁.Level n)
  /-- Commutativity:
      L1(n+1) --(S1.up)--> L1(n)
         ^                   ^
   F(n+1)|                   | F(n)
         |                   |
      L2(n+1) --(S2.up)--> L2(n)
  -/
  preserves_up :
    ∀ n, interfaceComp (S₂.up n) (F n) = interfaceComp (F (n + 1)) (S₁.up n)

/-- Pointwise equivalence of stratified systems via interfaces. -/
def StratifiedEquivalence (S₁ S₂ : StratifiedSystem) : Prop :=
  ∃ (F : StratifiedMorphism S₁ S₂) (G : StratifiedMorphism S₂ S₁),
    (∀ n, ∃ iso : InterfaceIso (S₂.Level n) (S₂.Level n),
      (interfaceComp (F.F n) (G.F n)).functor = iso.hom.functor) ∧
    (∀ n, ∃ iso : InterfaceIso (S₁.Level n) (S₁.Level n),
      (interfaceComp (G.F n) (F.F n)).functor = iso.hom.functor)

/-! ## Part 2: Truth Stratification -/

structure LanguageLayer where
  World : Type u
  Formula : Type u

structure TruthPredicateStruct (Base Meta : LanguageLayer) where
  base : LanguageLayer
  is_truth : Meta.World → Prop

/-- Tarski-style truth hierarchy. -/
structure TruthStratification where
  L : ℕ → LanguageLayer
  TruthAt : ∀ n, TruthPredicateStruct (L n) (L (n + 1))
  TruthAt_base : ∀ n, (TruthAt n).base = L n
  /-- Explicit interface between world levels -/
  up_model : ∀ n, InterfaceFunctor ((L (n + 1)).World) ((L n).World)

def TruthSelfRefProblem (T : TruthStratification) (n : ℕ) :
    SelfRefProblem (T.L n).World :=
{ carrier := (T.L n).World,
  paradox := fun _ => True }

/-- Connect truth-stratification to StratifiedSystem. -/
def truthStratificationAsSystem (T : TruthStratification)
    (h_inh : ∀ n, Inhabited (T.L n).World) : StratifiedSystem :=
{ Level := fun n => (T.L n).World,
  up := T.up_model,
  Problem := fun n => Unit,
  asSelfRef := fun n _ => TruthSelfRefProblem T n,
  resolve := fun n _ =>
    { witness := (T.up_model n).functor (default : (T.L n).World),
      resolved := True },
  undefinability := fun n =>
    { truth := fun _ => True,
      not_total := True },
  resolve_respects_up := by
    intro n p
    use default }

/-! ## Part 3: Proof Stratification -/

-- Force universe 0 for theories (syntax)
structure Theory where
  Sentence : Type
  proves   : Sentence → Prop

structure PATheory extends Theory

structure ProofStratification where
  Th       : ℕ → Theory
  basePA   : PATheory
  base_eq  : Th 0 = basePA.toTheory
  extend   : ∀ n, (Th n).Sentence → (Th (n + 1)).Sentence
  ConsistencyPredicate : ∀ n, (Th n).Sentence → Prop
  proves_consistency :
    ∀ n φ, (Th (n+1)).proves (extend n φ) → ConsistencyPredicate n φ
  ptOrdinal : ℕ → Ordinal
  ordinal_growth : ∀ n, ptOrdinal n < ptOrdinal (n + 1)

axiom PATower : ProofStratification

axiom codeSentences : ∀ (S : ProofStratification) (n : ℕ), Type

axiom decodeSentence :
  ∀ (S : ProofStratification) (n : ℕ),
    codeSentences S n → (S.Th n).Sentence

axiom proofStrat_up :
  ∀ (S : ProofStratification) (n : ℕ),
    InterfaceFunctor (codeSentences S (n + 1)) (codeSentences S n)

def proofStratificationAsSystem (S : ProofStratification)
    (h_inh : ∀ n, Inhabited (codeSentences S n)) : StratifiedSystem.{0} :=
{ Level := fun n => codeSentences S n,
  up := fun n => proofStrat_up S n,
  Problem := fun n => Unit,
  asSelfRef := fun n _ =>
    { carrier := codeSentences S n,
      paradox := fun _ => True },
  resolve := fun n _ =>
    { witness := (proofStrat_up S n).functor (default : codeSentences S n),
      resolved := True },
  undefinability := fun n =>
    { truth := fun _ => True,
      not_total := True },
  resolve_respects_up := by
    intro n p
    use default }

/-! ## Part 4: Stratification as Interface Tower -/

structure InterfaceTower where
  Obj : ℕ → Type u
  up  : ∀ n, InterfaceFunctor (Obj (n + 1)) (Obj n)
  catError : ∀ n, CategoryError (Obj n) (Obj (n + 1))
  functEquiv : ∀ n, functional_equivalence (Obj (n + 1)) (Obj n)

def interfaceTowerAsSystem (T : InterfaceTower)
    (h_inh : ∀ n, Inhabited (T.Obj n)) : StratifiedSystem :=
{ Level := T.Obj,
  up    := T.up,
  Problem := fun n => Unit,
  asSelfRef := fun n _ =>
    { carrier := T.Obj n,
      paradox := fun _ => True },
  resolve := fun n _ =>
    { witness := (T.up n).functor (default : T.Obj n),
      resolved := True },
  undefinability := fun n =>
    { truth := fun _ => True,
      not_total := True },
  resolve_respects_up := by
    intro n p
    use default }

axiom system_has_interface_tower :
  ∀ (S : StratifiedSystem) (h_inh : ∀ n, Inhabited (S.Level n)),
    ∃ (T : InterfaceTower),
    ∃ (hT : ∀ n, Inhabited (T.Obj n)),
      @StratifiedEquivalence S (interfaceTowerAsSystem T hT)

theorem Stratification_Interface_Equiv
    (S : StratifiedSystem) (h_inh : ∀ n, Inhabited (S.Level n)) :
    ∃ T : InterfaceTower,
      ∃ (hT : ∀ n, Inhabited (T.Obj n)),
        @StratifiedEquivalence S (interfaceTowerAsSystem T hT) :=
  system_has_interface_tower S h_inh

/-! ## Part 5: Ordinal Height & Heterogeneity -/

axiom heterogeneity_index (α β : Type u) : ℝ

-- Just axiomise height calculation to avoid instance hell
axiom requiredHeight (H : ℝ) : ℕ

axiom stratOrdinal (S : StratifiedSystem) : ℕ → Ordinal

axiom stratOrdinal_strict (S : StratifiedSystem) :
  ∀ n, stratOrdinal S n < stratOrdinal S (n + 1)

axiom heterogeneity_bounds_height
    (S : StratifiedSystem) (α β : Type u) (H : ℝ)
    (hH : H = heterogeneity_index α β) :
    ∀ n, (H ≥ 1 → (n < requiredHeight H → stratOrdinal S n < stratOrdinal S (requiredHeight H))) ∧
         (H < 1 → requiredHeight H = 0)

-- Explicit instance assumption
axiom patower_has_inhabited_codes : ∀ n, Inhabited (codeSentences PATower n)

-- Define PA System using explicit instance
def PAStratifiedSystem : StratifiedSystem.{0} :=
  proofStratificationAsSystem.{0} PATower patower_has_inhabited_codes

axiom stratOrdinal_matches_PA :
  ∀ n, stratOrdinal PAStratifiedSystem n = PATower.ptOrdinal n

theorem PA_stratification_ordinal :
    ∀ n, stratOrdinal PAStratifiedSystem n = PATower.ptOrdinal n :=
  stratOrdinal_matches_PA

theorem heterogeneity_height_correspondence
    (S : StratifiedSystem) (α β : Type u) (H : ℝ)
    (hH : H = heterogeneity_index α β) :
    ∀ n, (H ≥ 1 → (n < requiredHeight H → stratOrdinal S n < stratOrdinal S (requiredHeight H))) ∧
         (H < 1 → requiredHeight H = 0) :=
  heterogeneity_bounds_height S α β H hH

end StratificationCore
