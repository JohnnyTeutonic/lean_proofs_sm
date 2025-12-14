import TripartiteImpossibility
import Mathlib.Topology.Defs.Basic  -- For BaireSpace
import Mathlib.Topology.Instances.Nat

open TripartiteImpossibility Set MeasureTheory Function

/-!
# Proof of the Minimality of the Tripartite Basis

This file begins the campaign to prove the `MinimalityVerification` axioms from
the `TripartiteImpossibility` framework. This is a process of creative
mathematical construction, where for each axiom, we must build a counter-example
space that satisfies two of the three requirements but fails the third, and then
show that this space admits a `CardinalityFunctor`.

We begin with the first axiom: `separability_baire_insufficient`.

To prove this, we construct a space that is separable and Baire, but fails the
`MeasurabilityRequirement`, and show that a `CardinalityFunctor` can exist for it.
Our counterexample is the set of natural numbers `ℕ` with the discrete topology
and the trivial σ-algebra.
-/

section MinimalityProof1

-- We define our counterexample using `ℕ` with specific instances.
-- Topology: Discrete. This makes it Separable and Baire.
-- MeasurableSpace: Trivial (`{∅, univ}`). This makes it fail `MeasurabilityRequirement`.
def Counterexample1.topologicalSpace : TopologicalSpace ℕ := ⊥
def Counterexample1.measurableSpace : MeasurableSpace ℕ := measurableSpace_bot

/--
### Theorem: A counterexample space exists for the first minimality axiom.

This theorem provides a proof by construction for `separability_baire_insufficient`.
It demonstrates the existence of a space `α` that:
1. Is Separable (`SeparabilityRequirement`).
2. Is a Baire space (`BaireCategoryRequirement`).
3. Fails the strong measurability requirement (`¬ MeasurabilityRequirement`).
4. And for which a `CardinalityFunctor` can be constructed.
-/
theorem separability_baire_insufficient_proof :
  ∃ (α : Type*) [TopologicalSpace α] [MeasurableSpace α],
    (SeparabilityRequirement α ∧ BaireCategoryRequirement α ∧ ¬ MeasurabilityRequirement α) ∧
    (∃ (β : Type*), Nonempty (CardinalityFunctor α β)) :=
by
  -- We instantiate our proof with the specific counterexample structure.
  letI : TopologicalSpace ℕ := Counterexample1.topologicalSpace
  letI : MeasurableSpace ℕ := Counterexample1.measurableSpace
  use ℕ

  -- The proof has two main goals: prove the properties of the space,
  -- and prove that a CardinalityFunctor exists for it.
  constructor

  -- Goal 1: Prove the properties of `ℕ` with this structure.
  · refine ⟨?_, ?_, ?_⟩
    -- 1a. Prove Separability
    · unfold SeparabilityRequirement
      use Set.univ
      exact ⟨countable_univ, dense_univ⟩
    -- 1b. Prove Baire
    · unfold BaireCategoryRequirement
      -- Any discrete space is a Baire space.
      exact BaireSpace.of_discrete
    -- 1c. Prove it fails the Measurability Requirement
    · unfold MeasurabilityRequirement
      push_neg
      -- We provide a non-measurable set. The singleton {0} works.
      use {0}
      -- In `measurableSpace_bot`, only ∅ and univ are measurable. We prove {0} is neither.
      rw [measurableSet_bot_iff]; push_neg
      refine ⟨?_, ?_⟩
      · exact singleton_ne_empty 0
      · intro h_univ
        have h1 : (1 : ℕ) ∈ {0} := by rw [h_univ]; exact mem_univ 1
        simp at h1

  -- Goal 2: Prove that a `CardinalityFunctor` exists for this space.
  · use ℕ
    fconstructor
    -- Because our space is `ℕ`, a `CardinalityFunctor` to `ℕ` is trivial to construct.
    exact {
      functor := id,
      ordinal_target := ⟨id, injective_id⟩,
      bijection_preservation := by simp [Injective.eq_iff injective_id]
    }

end MinimalityProof1

section MinimalityProof2

/--
### Theorem: A counterexample space exists for the second minimality axiom.

This theorem provides a proof by construction for `separability_measurability_insufficient`.
It demonstrates the existence of a space `α` that:
1. Is Separable (`SeparabilityRequirement`).
2. Is fully measurable (`MeasurabilityRequirement`).
3. Fails the Baire Category requirement (`¬ BaireCategoryRequirement`).
4. And for which a `CardinalityFunctor` can be constructed.

Our counterexample is the set of rational numbers `ℚ` with its standard topology
and Borel sigma-algebra.
-/
theorem separability_measurability_insufficient_proof :
  ∃ (α : Type*) [TopologicalSpace α] [MeasurableSpace α],
    (SeparabilityRequirement α ∧ MeasurabilityRequirement α ∧ ¬ BaireCategoryRequirement α) ∧
    (∃ (β : Type*), Nonempty (CardinalityFunctor α β)) :=
by
  -- We use the rational numbers `ℚ` as our space.
  use ℚ
  constructor

  -- Goal 1: Prove the properties of `ℚ`.
  · refine ⟨?_, ?_, ?_⟩
    -- 1a. Prove Separability
    · unfold SeparabilityRequirement
      -- `ℚ` is its own countable dense subset.
      exact ⟨univ, ⟨countable_univ, dense_univ⟩⟩
    -- 1b. Prove Measurability
    · unfold MeasurabilityRequirement
      -- For a countable space, every subset is measurable.
      intro S
      exact measurableSet_discrete S
    -- 1c. Prove it fails the Baire Category Requirement
    · unfold BaireCategoryRequirement
      -- `ℚ` is famously not a Baire space.
      rw [← not_meager_univ]
      push_neg
      exact meager_univ

  -- Goal 2: Prove that a `CardinalityFunctor` exists.
  · use ℚ
    fconstructor
    -- Since `ℚ` is countable, a CardinalityFunctor is trivial.
    exact {
      functor := id,
      ordinal_target := ⟨id, injective_id⟩,
      bijection_preservation := by simp [Injective.eq_iff injective_id]
    }

end MinimalityProof2

section MinimalityProof3

/-!
This section proves the *third* minimality theorem of the Tripartite Impossibility
framework: `SeparabilityRequirement` is logically necessary.

It constructs an explicit counterexample — an uncountable discrete space —
which is Baire and fully measurable but **not** separable, and yet admits a
`CardinalityFunctor` into an uncountable target.
-/

universe u

section DiscreteWitness

variable (γ : Type u)

/-- Discrete topology and total σ-algebra on any type. -/
instance discrete_topology : TopologicalSpace γ := ⊥
instance total_measurable_space : MeasurableSpace γ := ⊤

/-- Every discrete space is Baire (the only dense open is `univ`). -/
theorem discrete_is_baire : BaireSpace γ := inferInstance

/-- In a discrete uncountable space, no countable subset can be dense. -/
theorem discrete_uncountable_not_separable (h : Uncountable γ) :
    ¬ ∃ (S : Set γ), S.Countable ∧ Dense S := by
  rintro ⟨S, hS_count, hS_dense⟩
  -- In a discrete space, closure S = S, so dense ⇒ S = univ.
  have hS_eq : S = (Set.univ : Set γ) :=
    by simpa [dense_iff_closure_eq] using hS_dense
  -- Then S = univ is countable ⇒ γ countable ⇒ contradiction.
  exact (h.not_countable (hS_count.mono (by simp [hS_eq])))

/-- The identity map is a trivial injective cardinality functor. -/
def idCardFunctor : CardinalityFunctor γ γ :=
  { toFun := id, inj := fun _ _ h => h }

/-- Bundled witness of insufficiency. -/
theorem baire_measurable_insufficient_witness (h : Uncountable γ) :
    BaireSpace γ ∧ (∀ S : Set γ, MeasurableSet S)
    ∧ ¬ ∃ (S : Set γ), S.Countable ∧ Dense S
    ∧ UncountableTarget γ ∧ Nonempty (CardinalityFunctor γ γ) := by
  refine ⟨discrete_is_baire γ, ?_, discrete_uncountable_not_separable γ h, h, ⟨idCardFunctor γ⟩⟩
  intro S; simp  -- all sets measurable

end DiscreteWitness

/-- **Baire–Measurability Insufficiency**

If a space is Baire and measurable but not separable, then there exists a
cardinality functor into an uncountable target. -/
theorem baire_measurable_insufficient_proof :
    ∃ (α β : Type*), BaireSpace α ∧ (∀ S : Set α, MeasurableSet S)
      ∧ ¬ (∃ (S : Set α), S.Countable ∧ Dense S)
      ∧ UncountableTarget β ∧ Nonempty (CardinalityFunctor α β) := by
  -- Choose α = β = an uncountable discrete type, e.g. `ℝ`.
  have h : Uncountable (Set.univ : Set ℝ) := by simp [Real.uncountable_univ]
  exact ⟨ℝ, ℝ, baire_measurable_insufficient_witness ℝ h⟩

end MinimalityProof3
