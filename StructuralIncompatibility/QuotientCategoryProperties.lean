import ImpossibilityQuotientIsomorphism

namespace QuotientCategoryProperties

open ImpossibilityQuotient
open ModularKernel

/-!
This file proves two key categorical properties of the impossibility quotient category:
1. Uniqueness of Morphisms: There is only one structure-preserving map between any two quotients.
2. Initiality: The canonical `BinaryImp` is also the initial object in the category.
-/

/--
### Theorem: Uniqueness of Structure-Preserving Morphisms

This theorem proves that for any two non-degenerate impossibility quotients,
there exists exactly one structure-preserving morphism between them.

The `preserves_structure` condition forces the paradox class to map to the
paradox class, which uniquely determines the entire function.
-/
theorem unique_morphism_between_quotients
  {S T : Type*} {I_S : ImpStruct S} {I_T : ImpStruct T}
  (nd_S : Nondegenerate S I_S) (nd_T : Nondegenerate T I_T) :
  ∃! f : ImpQuotient S I_S → ImpQuotient T I_T,
    (∀ q, (quotient_to_binary I_S q = paradox) ↔ (quotient_to_binary I_T (f q) = paradox)) :=
begin
  -- Existence: We know an isomorphism exists from `all_quotients_isomorphic`
  have h_exists : ∃ f, ∀ q, (quotient_to_binary I_S q = paradox) ↔ (quotient_to_binary I_T (f q) = paradox),
  {
    have iso_exists := all_quotients_isomorphic nd_S nd_T,
    cases iso_exists with f _,
    use f,
    intro q,
    -- The isomorphism is composed of maps to and from BinaryImp, which preserve the structure.
    -- f = g_T ∘ f_S
    -- is_paradox(f(q)) ↔ is_paradox(g_T(f_S(q)))
    -- is_paradox(q) ↔ is_paradox_binary(f_S(q))
    -- is_paradox_binary(b) ↔ is_paradox(g_T(b))
    -- By transitivity, is_paradox(q) ↔ is_paradox(f(q))
    let f_S := quotient_to_binary I_S,
    let g_T := binary_to_quotient nd_T,
    have h_fS : ∀ q, (quotient_to_binary I_S q = paradox) ↔ (f_S q = paradox) := by intro q; rfl,
    have h_gT : ∀ b, (b = paradox) ↔ (quotient_to_binary I_T (g_T b) = paradox),
    {
      intro b,
      conv_rhs { rw ← binary_quotient_binary nd_T b },
      rfl
    },
    exact (h_fS q).trans (h_gT (f_S q)),
  },
  
  -- Uniqueness
  rcases h_exists with ⟨f, hf⟩,
  use f,
  split,
  { exact hf },
  {
    intro g hg,
    funext q,
    -- Proof by case analysis on whether q is stable or paradox
    by_cases is_para_q : quotient_to_binary I_S q = paradox,
    {
      -- If q is paradox, f(q) and g(q) must both be paradox
      have f_is_para : quotient_to_binary I_T (f q) = paradox := (hf q).mp is_para_q,
      have g_is_para : quotient_to_binary I_T (g q) = paradox := (hg q).mp is_para_q,
      -- Since the map to binary is a bijection, if f(q) and g(q) both map to paradox, they must be equal.
      let iso_T := quotient_equiv_binary nd_T,
      have fq_eq : f q = iso_T.invFun paradox := iso_T.left_inv (f q) ▸ (congr_arg iso_T.invFun f_is_para),
      have gq_eq : g q = iso_T.invFun paradox := iso_T.left_inv (g q) ▸ (congr_arg iso_T.invFun g_is_para),
      rw [fq_eq, gq_eq],
    },
    {
      -- If q is stable, f(q) and g(q) must both be stable
      have f_is_stable : quotient_to_binary I_T (f q) ≠ paradox := mt (hf q).mpr is_para_q,
      have g_is_stable : quotient_to_binary I_T (g q) ≠ paradox := mt (hg q).mpr is_para_q,
      -- If they are not paradox, they must be stable
      have f_maps_to_stable : quotient_to_binary I_T (f q) = stable, by cases h:quotient_to_binary I_T (f q); trivial; contradiction,
      have g_maps_to_stable : quotient_to_binary I_T (g q) = stable, by cases h:quotient_to_binary I_T (g q); trivial; contradiction,

      let iso_T := quotient_equiv_binary nd_T,
      have fq_eq : f q = iso_T.invFun stable := iso_T.left_inv (f q) ▸ (congr_arg iso_T.invFun f_maps_to_stable),
      have gq_eq : g q = iso_T.invFun stable := iso_T.left_inv (g q) ▸ (congr_arg iso_T.invFun g_maps_to_stable),
      rw [fq_eq, gq_eq],
    }
  }
end

/--
### Theorem: Initiality of BinaryImp

This theorem proves that `BinaryImp` is the initial object in the category of
impossibility quotients. This means there is a unique structure-preserving
morphism from `BinaryImp` to any other non-degenerate impossibility quotient.

Since we already proved terminality, this establishes that all objects in the
category are isomorphic, forming a groupoid where every object is both initial
and terminal.
-/
theorem binary_is_initial {S : Type*} (I_S : ImpStruct S) (nd_S : Nondegenerate S I_S) :
  ∃! f : BinaryImp → ImpQuotient S I_S,
    (∀ b, (b = paradox) ↔ (quotient_to_binary I_S (f b) = paradox)) :=
begin
  -- Existence: The inverse of the canonical isomorphism is such a map.
  let f_exists := (quotient_equiv_binary nd_S).invFun,
  use f_exists,
  split,
  { 
    intro b,
    -- We need to show is_paradox(b) ↔ is_paradox(f_exists(b))
    -- We know is_paradox(g(b)) ↔ is_paradox(b) for g = quotient_to_binary
    -- f_exists is the inverse of g.
    let g := quotient_to_binary I_S,
    have hg := (quotient_equiv_binary nd_S).right_inv, -- g(f_exists(b)) = b
    conv_lhs { rw ← hg b},
    show (g (f_exists b) = paradox) ↔ (quotient_to_binary I_S (f_exists b) = paradox),
    rfl,
  },
  {
    -- Uniqueness
    intro g hg,
    funext b,
    cases b,
    { -- stable case
      have g_maps_to_stable : quotient_to_binary I_S (g stable) = stable,
      {
        have prop := (hg stable).not,
        simp only [neq_self_iff_false, not_false_iff] at prop,
        by_cases h : quotient_to_binary I_S (g stable) = paradox; contradiction; trivial,
      },
      have f_maps_to_stable : quotient_to_binary I_S (f_exists stable) = stable,
      {
        let iso := quotient_equiv_binary nd_S,
        have := iso.right_inv stable,
        simp [iso] at this,
        exact this
      },
      let iso := quotient_equiv_binary nd_S,
      have g_eq : g stable = iso.invFun stable := iso.left_inv (g stable) ▸ (congr_arg iso.invFun g_maps_to_stable),
      have f_eq : f_exists stable = iso.invFun stable := iso.left_inv (f_exists stable) ▸ (congr_arg iso.invFun f_maps_to_stable),
      rw [g_eq, f_eq],
    },
    { -- paradox case
      have g_maps_to_paradox : quotient_to_binary I_S (g paradox) = paradox := (hg paradox).mp rfl,
      have f_maps_to_paradox : quotient_to_binary I_S (f_exists paradox) = paradox,
      {
        let iso := quotient_equiv_binary nd_S,
        have := iso.right_inv paradox,
        simp [iso] at this,
        exact this
      },
      let iso := quotient_equiv_binary nd_S,
      have g_eq : g paradox = iso.invFun paradox := iso.left_inv (g paradox) ▸ (congr_arg iso.invFun g_maps_to_paradox),
      have f_eq : f_exists paradox = iso.invFun paradox := iso.left_inv (f_exists paradox) ▸ (congr_arg iso.invFun f_maps_to_paradox),
      rw [g_eq, f_eq],
    }
  }
end

end QuotientCategoryProperties
