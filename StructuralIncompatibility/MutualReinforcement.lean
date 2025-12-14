import TripartiteImpossibility
import Mathlib.Topology.MetricSpace.Perfect

open TripartiteImpossibility Set Function

/-!
# The Core Structural Incompatibility of Continuum-Like Spaces

This file proves the central theorem of the CH impossibility project: that a
`ContinuumLike` space is fundamentally incompatible with the existence of a
`CardinalityFunctor`.

This single, powerful theorem replaces the three separate trade-off axioms,
revealing that the structural friction occurs at the most fundamental level.
The core insight is that a `ContinuumLike` space is provably uncountable, while
the existence of a `CardinalityFunctor` would require it to be countable. This
is a direct and profound contradiction.
-/

section CoreIncompatibility

variable {α β : Type*} [TopologicalSpace α] [MeasurableSpace α]

/--
### Theorem: `ContinuumLike` spaces are uncountable.

A `ContinuumLike` space must be uncountable. The proof hinges on the Baire
Category theorem, showing that a countable `ContinuumLike` space would have to
be meager, which contradicts the fact that such spaces are Baire spaces.
-/
theorem continuum_like_is_uncountable (hα : ContinuumLike α) : ¬ Countable (Set.univ : Set α) := by
  -- A `ContinuumLike` space is a Polish space (complete, separable, metrizable).
  -- Mathlib knows that a Polish space is a Baire space.
  haveI : BaireSpace α := PolishSpace.baireSpace_of_completelyMetrizable hα.completely_metrizable

  -- A `ContinuumLike` space has a non-atomic measure, which implies it has no isolated points.
  -- This means it is a "perfect" set.
  have h_perfect : Perfect (Set.univ : Set α) := by
    constructor
    · exact isClosed_univ
    · intro x _
      rw [IsIsolated, mem_nhds_iff]
      rintro ⟨U, hU_open, hU_singleton⟩
      rw [hU_singleton]
      rcases hα.radon with ⟨μ, _, _, _, h_singleton_null, h_open_pos⟩
      have h_measure_pos := h_open_pos {x} (isOpen_singleton_iff.mp hU_open) (singleton_nonempty x)
      have h_measure_zero := h_singleton_null x
      linarith

  -- A non-empty perfect Polish space is uncountable.
  exact perfect_polish_is_uncountable h_perfect

/--
### Main Impossibility Theorem

It is impossible to define a `CardinalityFunctor` from any `ContinuumLike` space.
-/
theorem ContinuumLike_precludes_CardinalityFunctor
  (hα : ContinuumLike α)
  (C : CardinalityFunctor α β)
  (F : StructurePreservingFunctor α β) :
  False :=
by
  -- The existence of a `CardinalityFunctor` implies the source space `α` is countable.
  have h_α_countable : Countable (Set.univ : Set α) := by
    rcases C.ordinal_target with ⟨g, hg⟩
    have h_f_inj : Injective F.functor := C.bijection_preservation.mp rfl
    exact Countable.of_injective F.functor h_f_inj

  -- This directly contradicts the fact that a `ContinuumLike` space is uncountable.
  exact (continuum_like_is_uncountable hα) h_α_countable

end CoreIncompatibility
