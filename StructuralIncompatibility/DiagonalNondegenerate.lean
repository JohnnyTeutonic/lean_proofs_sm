import ModularKernel
import ImpossibilityQuotientIsomorphism

open ModularKernel ImpossibilityQuotient

/--
Generic theorem to prove Non-degeneracy from witnesses.

This lemma formalizes a common pattern in the impossibility proofs:
establishing that a structure is non-degenerate by providing:
1. An explicit `stable_witness` that is provably not a fixed point.
2. A proof that the structure's `diagonal` operator produces a fixed point.
-/
theorem diagonal_implies_nondegenerate
  {S : Type*} (I : ImpStruct S)
  -- Witness for a stable element
  (stable_witness : S)
  (h_stable : ¬I.fixed_point stable_witness)
  -- Proof that the diagonal construction creates a paradoxical element
  (h_paradox : I.fixed_point (I.diagonal (fun s => I.negation (I.fixed_point s))))
  : Nondegenerate S I := {
    exists_stable := ⟨stable_witness, h_stable⟩,
    exists_paradox := ⟨I.diagonal (fun s => I.negation (I.fixed_point s)), h_paradox⟩
}
