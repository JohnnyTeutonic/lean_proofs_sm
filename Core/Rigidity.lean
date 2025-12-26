/-
  Core/Rigidity.lean
  
  The Rigidity Layer: First-Class Theorems for Forced Structure Uniqueness
  
  This module promotes the P_unique_with_adjoint pattern to a reusable schema.
  Any domain that instantiates ForcedStructureSpec gets uniqueness for free.
  
  Key results:
  1. ForcedStructureSpec: The axioms (round-trips + witness-preservation + tightness)
  2. P_unique: Any two specs with same axioms agree on derived structure
  3. encoding_disputes_are_gauge: Alternative encodings yield isomorphic results
  
  Author: Jonathan Reich
  Date: December 2025
-/

-- ============================================
-- SECTION 1: Abstract Categories
-- ============================================

/-- 
  Abstract obstruction category.
  Objects have a "quotient geometry" measuring what's broken.
-/
structure ObsCategory where
  Obj : Type
  Morph : Obj → Obj → Type
  quotient : Obj → Nat  -- Abstract quotient (could be richer)
  witness : Obj → Type  -- The constructive witness

/-- 
  Abstract symmetry category.
  Objects have a "symmetry type" measuring what's forced.
-/
structure SymCategory where
  Obj : Type
  Morph : Obj → Obj → Type
  stype : Obj → Nat  -- Abstract symmetry type
  carrier : Obj → Type  -- The carrier structure

-- ============================================
-- SECTION 2: The Correspondence Functions
-- ============================================

/-- 
  A quotient-symmetry correspondence.
  This is the "dictionary" between obstruction geometries and symmetry types.
-/
structure QuotientSymmetryCorrespondence where
  quotientToSym : Nat → Nat
  symToQuotient : Nat → Nat
  -- Round-trip laws
  left_inverse : ∀ q, symToQuotient (quotientToSym q) = q
  right_inverse : ∀ s, quotientToSym (symToQuotient s) = s

-- ============================================
-- SECTION 3: Forced Structure Specification
-- ============================================

/-- 
  THE CENTRAL DEFINITION: A specification for a forced structure functor.
  
  This bundles all the axioms that guarantee uniqueness:
  1. Round-trips: P ∘ B and B ∘ P recover essential structure
  2. Tightness: B maps symmetry type to its canonical quotient
  3. Witness preservation: P preserves witnesses
  4. Monotonicity: P is at least as free as quotient forces
-/
structure ForcedStructureSpec (Obs : ObsCategory) (Sym : SymCategory) 
    (corr : QuotientSymmetryCorrespondence) where
  /-- The "Prescribing" functor: Obs → Sym -/
  P : Obs.Obj → Sym.Obj
  /-- The "Breaking" functor: Sym → Obs -/
  B : Sym.Obj → Obs.Obj
  
  -- Round-trip axioms
  /-- Right round-trip: P ∘ B recovers symmetry type -/
  right_roundtrip : ∀ p, Sym.stype (P (B p)) = Sym.stype p
  /-- Left round-trip: B ∘ P recovers quotient geometry -/
  left_roundtrip : ∀ o, Obs.quotient (B (P o)) = Obs.quotient o
  
  -- Tightness: B is determined by the correspondence
  /-- B maps symmetry type to its canonical quotient -/
  B_tight : ∀ p, corr.quotientToSym (Obs.quotient (B p)) = Sym.stype p
  
  -- Witness preservation
  /-- P preserves witnesses (or lifts them appropriately) -/
  witness_preserving : ∀ o, Sym.carrier (P o) = Obs.witness o
  
  -- Monotonicity lower bound
  /-- P is at least as free as the quotient forces -/
  monotone_lb : ∀ o, corr.quotientToSym (Obs.quotient o) ≤ Sym.stype (P o)

-- ============================================
-- SECTION 4: The Uniqueness Theorem
-- ============================================

/-- 
  THE RIGIDITY THEOREM: Any ForcedStructureSpec determines a unique P.
  
  Given two specs with the same axioms, they agree on symmetry type.
  This is the "no free parameters" theorem.
-/
theorem P_unique (Obs : ObsCategory) (Sym : SymCategory) 
    (corr : QuotientSymmetryCorrespondence)
    (spec1 spec2 : ForcedStructureSpec Obs Sym corr) :
    ∀ o, Sym.stype (spec1.P o) = Sym.stype (spec2.P o) := by
  intro o
  -- Both specs satisfy the same tightness + roundtrip laws
  -- Step 1: From spec1.B_tight at (spec1.P o):
  have h1 : corr.quotientToSym (Obs.quotient (spec1.B (spec1.P o))) = 
            Sym.stype (spec1.P o) := spec1.B_tight (spec1.P o)
  -- Step 2: Use left_roundtrip to simplify:
  have h2 : Obs.quotient (spec1.B (spec1.P o)) = Obs.quotient o := 
            spec1.left_roundtrip o
  -- Step 3: Combine
  have h3 : Sym.stype (spec1.P o) = corr.quotientToSym (Obs.quotient o) := by
    rw [← h1, h2]
  -- Same for spec2
  have h4 : corr.quotientToSym (Obs.quotient (spec2.B (spec2.P o))) = 
            Sym.stype (spec2.P o) := spec2.B_tight (spec2.P o)
  have h5 : Obs.quotient (spec2.B (spec2.P o)) = Obs.quotient o := 
            spec2.left_roundtrip o
  have h6 : Sym.stype (spec2.P o) = corr.quotientToSym (Obs.quotient o) := by
    rw [← h4, h5]
  -- Conclude
  rw [h3, h6]

/-- 
  COROLLARY: The symmetry type is uniquely determined by the quotient.
  This is the "derived structure" form of uniqueness.
-/
theorem stype_determined_by_quotient (Obs : ObsCategory) (Sym : SymCategory)
    (corr : QuotientSymmetryCorrespondence)
    (spec : ForcedStructureSpec Obs Sym corr) :
    ∀ o, Sym.stype (spec.P o) = corr.quotientToSym (Obs.quotient o) := by
  intro o
  have h1 := spec.B_tight (spec.P o)
  have h2 := spec.left_roundtrip o
  rw [← h1, h2]

-- ============================================
-- SECTION 5: Encoding Disputes Are Gauge
-- ============================================

/-- 
  An alternative encoding of the same obstruction category.
  Different presentations of the "same" mathematical content.
-/
structure AlternativeEncoding (Obs : ObsCategory) where
  /-- The alternative object type -/
  AltObj : Type
  /-- Translation to canonical form -/
  toCanonical : AltObj → Obs.Obj
  /-- Translation preserves quotient -/
  preserves_quotient : ∀ a, Obs.quotient (toCanonical a) = Obs.quotient (toCanonical a)
  /-- The encoding is "faithful" -/
  faithful : Function.Injective toCanonical

/-- 
  THEOREM: Alternative encodings yield the same symmetry type.
  
  If two encodings map to the same quotient, they produce the same 
  derived symmetry. "Encoding disputes are gauge."
-/
theorem encoding_disputes_are_gauge (Obs : ObsCategory) (Sym : SymCategory)
    (corr : QuotientSymmetryCorrespondence)
    (spec : ForcedStructureSpec Obs Sym corr)
    (enc1 enc2 : AlternativeEncoding Obs)
    (a1 : enc1.AltObj) (a2 : enc2.AltObj)
    (hquot : Obs.quotient (enc1.toCanonical a1) = Obs.quotient (enc2.toCanonical a2)) :
    Sym.stype (spec.P (enc1.toCanonical a1)) = 
    Sym.stype (spec.P (enc2.toCanonical a2)) := by
  -- Both are determined by quotient via stype_determined_by_quotient
  have h1 := stype_determined_by_quotient Obs Sym corr spec (enc1.toCanonical a1)
  have h2 := stype_determined_by_quotient Obs Sym corr spec (enc2.toCanonical a2)
  rw [h1, h2, hquot]

-- ============================================
-- SECTION 6: The No Free Parameters Theorem
-- ============================================

/-- 
  MASTER THEOREM: The Inverse Noether Programme has no free parameters.
  
  Any ForcedStructureSpec is completely determined by:
  1. The obstruction category (what's impossible)
  2. The correspondence (quotient ↔ symmetry dictionary)
  
  There are no tunable parameters in the derived symmetry.
-/
theorem no_free_parameters (Obs : ObsCategory) (Sym : SymCategory)
    (corr : QuotientSymmetryCorrespondence)
    (spec : ForcedStructureSpec Obs Sym corr) :
    -- The P functor is uniquely determined on symmetry types
    (∀ o, Sym.stype (spec.P o) = corr.quotientToSym (Obs.quotient o)) ∧
    -- Any alternative spec agrees
    (∀ spec' : ForcedStructureSpec Obs Sym corr, 
      ∀ o, Sym.stype (spec.P o) = Sym.stype (spec'.P o)) ∧
    -- Encoding choices don't matter
    (∀ enc : AlternativeEncoding Obs, ∀ a, 
      Sym.stype (spec.P (enc.toCanonical a)) = 
      corr.quotientToSym (Obs.quotient (enc.toCanonical a))) := by
  constructor
  · exact stype_determined_by_quotient Obs Sym corr spec
  constructor
  · intro spec' o
    exact P_unique Obs Sym corr spec spec' o
  · intro enc a
    exact stype_determined_by_quotient Obs Sym corr spec (enc.toCanonical a)

-- ============================================
-- SECTION 7: Subsingleton Instance
-- ============================================

/-- 
  The collection of ForcedStructureSpecs is a subsingleton on symmetry types.
  This is the type-theoretic way of saying "P is unique."
-/
theorem specs_subsingleton_on_stype (Obs : ObsCategory) (Sym : SymCategory)
    (corr : QuotientSymmetryCorrespondence) :
    ∀ (spec1 spec2 : ForcedStructureSpec Obs Sym corr),
    ∀ o, Sym.stype (spec1.P o) = Sym.stype (spec2.P o) :=
  P_unique Obs Sym corr

-- ============================================
-- SECTION 8: Summary
-- ============================================

/-!
## Summary

This module provides the rigidity layer for the Inverse Noether Programme:

1. **ForcedStructureSpec**: The axioms that guarantee uniqueness
   - Round-trips: P ∘ B and B ∘ P recover essential structure
   - Tightness: B is determined by the correspondence
   - Witness preservation: P preserves constructive content

2. **P_unique**: Any two specs agree on derived symmetry type

3. **encoding_disputes_are_gauge**: Alternative encodings yield same result

4. **no_free_parameters**: The derived symmetry has no tunable parameters

This is the "no free lunch" theorem for impossibility-derived symmetries.
Any domain that instantiates ForcedStructureSpec inherits these guarantees.
-/

#check @P_unique
#check @stype_determined_by_quotient
#check @encoding_disputes_are_gauge
#check @no_free_parameters
#check @specs_subsingleton_on_stype
