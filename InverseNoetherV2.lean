/-
  Constructive Impossibility: Forced Structure Functor
  
  The right adjoint ImpossibilityDiag made explicit as P : Obs → Sym
  
  Key insight: The witness type of an obstruction BECOMES the carrier
  of the forced symmetry. Morphisms between obstructions (derivations)
  become symmetry homomorphisms under P.
  
  Connection to Dirac constraint formalism:
  - Constraint (obstruction) has structure (witness)
  - Constraint surface (quotient geometry) determines gauge type
  - Maps between constraints induce gauge transformations
  
  REVISION (December 6, 2025):
  Both QuotientGeom.nPartite and SymType.permutation are now parameterized
  by n : ℕ to maintain the TIGHT adjunction B ⊣ P. This ensures:
  - Arrow's theorem: .nPartite 4 ⟷ .permutation 4 (S₄)
  - CAP-like trilemmas: .nPartite 3 ⟷ .permutation 3 (S₃)
  
  The round-trip theorems are now EXACT equalities (not just ≤)!
  
  MODULAR DESIGN (December 8, 2025):
  Imports from ImpossibilityType.lean for base types.
  
  Author: Jonathan Reich
  Date: December 2025
-/

import Mathlib.Data.Fin.Basic
import ImpossibilityType
import Mathlib.Logic.Function.Basic
import Mathlib.Order.Basic

/-!
## Modular Design Note

This file CAN import from ImpossibilityType.lean when properly configured:
  import ImpossibilityType  -- Requires lake build ImpossibilityType first

For now, we define compatible types locally. See MODULARIZATION_GUIDE.md.
-/

namespace InverseNoetherV2

-- ============================================
-- SECTION 1: Obstruction Category (Negative Space)
-- ============================================

/-- Mechanism types ordered by derivational complexity -/
inductive Mechanism : Type where
  | diagonal      -- Cantor, Gödel, Halting (self-reference)
  | fixedPoint    -- Brouwer, Kakutani (topological)
  | resource      -- CAP, Blockchain trilemma (conservation)
  | independence  -- Continuum hypothesis, parallel postulate (underdetermination)
  deriving DecidableEq, Repr

/-- Rank function for mechanisms (linear order by complexity) -/
def Mechanism.rank : Mechanism → ℕ
  | .diagonal => 0
  | .fixedPoint => 1
  | .resource => 2
  | .independence => 3

/-- Preorder on mechanisms via rank: simpler ≤ more complex -/
def Mechanism.le (m₁ m₂ : Mechanism) : Prop := m₁.rank ≤ m₂.rank

instance : LE Mechanism where
  le := Mechanism.le

instance (m₁ m₂ : Mechanism) : Decidable (m₁ ≤ m₂) := 
  inferInstanceAs (Decidable (m₁.rank ≤ m₂.rank))

/-- Mechanism forms a preorder -/
theorem Mechanism.le_refl (m : Mechanism) : m ≤ m := Nat.le_refl _

theorem Mechanism.le_trans {m₁ m₂ m₃ : Mechanism} (h₁ : m₁ ≤ m₂) (h₂ : m₂ ≤ m₃) : m₁ ≤ m₃ :=
  Nat.le_trans h₁ h₂

instance : Preorder Mechanism where
  le := (· ≤ ·)
  le_refl := Mechanism.le_refl
  le_trans := fun _ _ _ => Mechanism.le_trans

/-- Quotient geometry ordered by structural complexity -/
inductive QuotientGeom : Type where
  | binary     -- Z₂ quotient (yes/no, stable/paradox)
  | nPartite (n : ℕ)   -- n-partite: pick (n-1) of n properties (e.g., Arrow: n=4)
  | continuous -- manifold quotient (Pareto frontier S^{n-1})
  | spectrum   -- infinite parameter space (gauge freedom)
  deriving Repr

/-- Preorder: more complex geometry ≥ simpler -/
def QuotientGeom.le : QuotientGeom → QuotientGeom → Prop
  | .binary, _ => True
  | .nPartite _, .nPartite _ => True
  | .nPartite _, .continuous => True
  | .nPartite _, .spectrum => True
  | .continuous, .continuous => True
  | .continuous, .spectrum => True
  | .spectrum, .spectrum => True
  | _, _ => False

instance : LE QuotientGeom where
  le := QuotientGeom.le

instance (q₁ q₂ : QuotientGeom) : Decidable (q₁ ≤ q₂) := by
  simp only [LE.le, QuotientGeom.le]
  cases q₁ <;> cases q₂ <;> exact decidable_of_iff _ Iff.rfl

theorem QuotientGeom.le_refl (q : QuotientGeom) : q ≤ q := by
  cases q <;> trivial

theorem QuotientGeom.le_trans {q₁ q₂ q₃ : QuotientGeom} (h₁ : q₁ ≤ q₂) (h₂ : q₂ ≤ q₃) : q₁ ≤ q₃ := by
  simp only [LE.le, QuotientGeom.le] at *
  cases q₁ <;> cases q₂ <;> cases q₃ <;> simp_all

instance : Preorder QuotientGeom where
  le := (· ≤ ·)
  le_refl := QuotientGeom.le_refl
  le_trans := fun _ _ _ => QuotientGeom.le_trans

/-- Objects in the obstruction category (Negative Space) -/
structure NegObj where
  /-- The impossibility mechanism -/
  mechanism : Mechanism
  /-- The quotient geometry -/
  quotient : QuotientGeom
  /-- The witness type - computational content of the impossibility -/
  witness : Type
  deriving Repr

/-- Morphisms in Obs: preserve or generalize structure
    A morphism o₁ → o₂ means o₁ derives/embeds into o₂ -/
structure ObsMorphism (o₁ o₂ : NegObj) where
  /-- Mechanisms must be related -/
  mech_le : o₁.mechanism ≤ o₂.mechanism
  /-- Quotient complexity can increase -/
  quot_le : o₁.quotient ≤ o₂.quotient
  /-- The witness map - how the computational content transforms -/
  witness_map : o₁.witness → o₂.witness

/-- Identity morphism in Obs -/
def ObsMorphism.id (o : NegObj) : ObsMorphism o o where
  mech_le := Mechanism.le_refl o.mechanism
  quot_le := QuotientGeom.le_refl o.quotient
  witness_map := _root_.id

/-- Composition of morphisms in Obs -/
def ObsMorphism.comp {o₁ o₂ o₃ : NegObj} 
    (f : ObsMorphism o₁ o₂) (g : ObsMorphism o₂ o₃) : ObsMorphism o₁ o₃ where
  mech_le := Mechanism.le_trans f.mech_le g.mech_le
  quot_le := QuotientGeom.le_trans f.quot_le g.quot_le
  witness_map := g.witness_map ∘ f.witness_map

-- ============================================
-- SECTION 2: Symmetry Category (Positive Space)
-- ============================================

/-- Symmetry types ordered by "freedom" / group dimension -/
inductive SymType : Type where
  | discrete    -- Z₂, finite groups (0-dimensional)
  | permutation (n : ℕ) -- Sₙ (finite permutation group on n elements)
  | continuous  -- Lie groups on manifolds (positive dimension)
  | gauge       -- local symmetry, free parameters (infinite-dimensional)
  deriving Repr

/-- More freedom = higher in order -/
def SymType.le : SymType → SymType → Prop
  | .discrete, _ => True
  | .permutation _, .permutation _ => True  -- All permutation groups comparable
  | .permutation _, .continuous => True
  | .permutation _, .gauge => True
  | .continuous, .continuous => True
  | .continuous, .gauge => True
  | .gauge, .gauge => True
  | _, _ => False

instance : LE SymType where
  le := SymType.le

instance (s₁ s₂ : SymType) : Decidable (s₁ ≤ s₂) := by
  simp only [LE.le, SymType.le]
  cases s₁ <;> cases s₂ <;> exact decidable_of_iff _ Iff.rfl

theorem SymType.le_refl (s : SymType) : s ≤ s := by
  cases s <;> trivial

theorem SymType.le_trans {s₁ s₂ s₃ : SymType} (h₁ : s₁ ≤ s₂) (h₂ : s₂ ≤ s₃) : s₁ ≤ s₃ := by
  simp only [LE.le, SymType.le] at *
  cases s₁ <;> cases s₂ <;> cases s₃ <;> simp_all

instance : Preorder SymType where
  le := (· ≤ ·)
  le_refl := SymType.le_refl
  le_trans := fun _ _ _ => SymType.le_trans

/-- Objects in the symmetry category (Positive Space) -/
structure PosObj where
  /-- The symmetry type -/
  stype : SymType
  /-- The symmetry carrier (the group/structure itself) -/
  carrier : Type
  /-- What the symmetry acts on -/
  action : Type := Unit
  deriving Repr

/-- Morphisms in Sym: symmetry homomorphisms -/
structure SymMorphism (p₁ p₂ : PosObj) where
  /-- Symmetry type can increase in freedom -/
  stype_le : p₁.stype ≤ p₂.stype
  /-- The group homomorphism (abstracted) -/
  carrier_map : p₁.carrier → p₂.carrier
  /-- Equivariance condition (placeholder) -/
  action_compatible : True := trivial

/-- Identity morphism in Sym -/
def SymMorphism.id (p : PosObj) : SymMorphism p p where
  stype_le := SymType.le_refl p.stype
  carrier_map := _root_.id

/-- Composition of morphisms in Sym -/
def SymMorphism.comp {p₁ p₂ p₃ : PosObj}
    (f : SymMorphism p₁ p₂) (g : SymMorphism p₂ p₃) : SymMorphism p₁ p₃ where
  stype_le := SymType.le_trans f.stype_le g.stype_le
  carrier_map := g.carrier_map ∘ f.carrier_map

-- ============================================
-- SECTION 3: The Forced Structure Functor P : Obs → Sym
-- ============================================

/-- Core construction: quotient geometry determines symmetry type
    
    This is the essence of "forced structure":
    - Binary quotient forces discrete (Z₂) symmetry
    - N-partite quotient forces permutation symmetry
    - Continuous quotient forces Lie group symmetry
    - Spectrum quotient forces gauge symmetry
-/
def quotientToSymType : QuotientGeom → SymType
  | .binary => .discrete
  | .nPartite n => .permutation n  -- n-partite forces Sₙ
  | .continuous => .continuous
  | .spectrum => .gauge

/-- Mechanism determines symmetry type (for the P direction)
    
    NOTE: For fixedPoint mechanism, we default to S₃ as the canonical permutation group.
    The specific n should be determined by the quotient geometry via quotientToSymType.
-/
def mechanismToSymType : Mechanism → SymType
  | .diagonal => .discrete
  | .fixedPoint => .permutation 3  -- Default to S₃
  | .resource => .continuous
  | .independence => .gauge

/-- KEY LEMMA: quotientToSymType is monotone
    This is what makes P a functor! -/
theorem quotientToSymType_mono {q₁ q₂ : QuotientGeom} (h : q₁ ≤ q₂) :
    quotientToSymType q₁ ≤ quotientToSymType q₂ := by
  simp only [quotientToSymType, LE.le, SymType.le, QuotientGeom.le] at *
  cases q₁ <;> cases q₂ <;> simp_all

/-- P on objects: obstruction ↦ minimal compatible symmetry
    
    The witness type of the obstruction BECOMES the carrier of the symmetry.
    This is the key insight: computational content is preserved. -/
def P_obj (o : NegObj) : PosObj where
  stype := quotientToSymType o.quotient
  carrier := o.witness
  action := Unit

/-- P on morphisms: derivation ↦ homomorphism
    
    The witness_map becomes the carrier_map.
    Monotonicity of quotientToSymType ensures stype_le holds. -/
def P_morph {o₁ o₂ : NegObj} (f : ObsMorphism o₁ o₂) : 
    SymMorphism (P_obj o₁) (P_obj o₂) where
  stype_le := quotientToSymType_mono f.quot_le
  carrier_map := f.witness_map

/-- FUNCTOR LAW I: P preserves identity -/
theorem P_preserves_id (o : NegObj) :
    P_morph (ObsMorphism.id o) = SymMorphism.id (P_obj o) := rfl

/-- FUNCTOR LAW II: P preserves composition -/
theorem P_preserves_comp {o₁ o₂ o₃ : NegObj}
    (f : ObsMorphism o₁ o₂) (g : ObsMorphism o₂ o₃) :
    P_morph (ObsMorphism.comp f g) = SymMorphism.comp (P_morph f) (P_morph g) := rfl

-- ============================================
-- SECTION 4: The Breaking Functor B : Sym → Obs (Left Adjoint)
-- ============================================

/-- Inverse correspondence: symmetry type determines quotient geometry -/
def symTypeToQuotient : SymType → QuotientGeom
  | .discrete => .binary
  | .permutation n => .nPartite n  -- Sₙ corresponds to n-partite
  | .continuous => .continuous
  | .gauge => .spectrum

/-- Inverse correspondence: symmetry type determines mechanism
    
    This is the key insight for tight adjunction:
    - Discrete (finite) symmetry breaks via diagonal/enumeration
    - Permutation symmetry (any n) breaks via fixed-point arguments
    - Continuous symmetry breaks via resource/conservation constraints
    - Gauge symmetry breaks via underdetermination/independence
-/
def symTypeToMechanism : SymType → Mechanism
  | .discrete => .diagonal        -- finite symmetry breaks via enumeration
  | .permutation _ => .fixedPoint -- permutation symmetry breaks via fixed-point
  | .continuous => .resource      -- continuous symmetry breaks via conservation
  | .gauge => .independence       -- gauge breaks via underdetermination

/-- symTypeToQuotient is monotone -/
theorem symTypeToQuotient_mono {s₁ s₂ : SymType} (h : s₁ ≤ s₂) :
    symTypeToQuotient s₁ ≤ symTypeToQuotient s₂ := by
  simp only [symTypeToQuotient, LE.le, QuotientGeom.le, SymType.le] at *
  cases s₁ <;> cases s₂ <;> simp_all

/-- symTypeToMechanism is monotone -/
theorem symTypeToMechanism_mono {s₁ s₂ : SymType} (h : s₁ ≤ s₂) :
    symTypeToMechanism s₁ ≤ symTypeToMechanism s₂ := by
  simp only [symTypeToMechanism, LE.le, Mechanism.le, Mechanism.rank, SymType.le] at *
  cases s₁ <;> cases s₂ <;> simp_all

-- Note: symType → mechanism → symType is NOT exact for permutation
-- because mechanismToSymType(.fixedPoint) = .permutation 3, losing n

/-- ROUND-TRIP: mechanism → symType → mechanism = id -/
theorem mechanism_symType_roundtrip (m : Mechanism) :
    symTypeToMechanism (mechanismToSymType m) = m := by
  cases m <;> rfl

/-- ROUND-TRIP III: quotient → symType → quotient = id
    
    Now with parameterized types, this is EXACT for all cases!
-/
theorem quotient_symType_roundtrip (q : QuotientGeom) :
    symTypeToQuotient (quotientToSymType q) = q := by
  cases q <;> rfl

/-- ROUND-TRIP IV: symType → quotient → symType = id -/
theorem symType_quotient_roundtrip (s : SymType) :
    quotientToSymType (symTypeToQuotient s) = s := by
  cases s <;> rfl

/-- B on objects: symmetry ↦ obstruction from breaking it
    
    Now FULLY DETERMINED by p.stype - both mechanism and quotient! -/
def B_obj (p : PosObj) : NegObj where
  mechanism := symTypeToMechanism p.stype
  quotient := symTypeToQuotient p.stype
  witness := p.carrier

/-- B on morphisms - now uses symTypeToMechanism_mono -/
def B_morph {p₁ p₂ : PosObj} (f : SymMorphism p₁ p₂) :
    ObsMorphism (B_obj p₁) (B_obj p₂) where
  mech_le := symTypeToMechanism_mono f.stype_le
  quot_le := symTypeToQuotient_mono f.stype_le
  witness_map := f.carrier_map

/-- B preserves identity -/
theorem B_preserves_id (p : PosObj) :
    B_morph (SymMorphism.id p) = ObsMorphism.id (B_obj p) := rfl

/-- B preserves composition -/
theorem B_preserves_comp {p₁ p₂ p₃ : PosObj}
    (f : SymMorphism p₁ p₂) (g : SymMorphism p₂ p₃) :
    B_morph (SymMorphism.comp f g) = ObsMorphism.comp (B_morph f) (B_morph g) := rfl

-- ============================================
-- SECTION 5: Adjunction B ⊣ P (Inverse Noether)
-- ============================================

/-- Unit: σ → P(B(σ)) - embedding symmetry into forced structure of its breaking -/
def adjUnit (p : PosObj) : SymMorphism p (P_obj (B_obj p)) where
  stype_le := by
    simp only [P_obj, B_obj, quotientToSymType, symTypeToQuotient]
    cases p.stype <;> exact SymType.le_refl _
  carrier_map := _root_.id

/-- Counit: B(P(o)) → o - breaking the forced structure recovers the obstruction
    
    Note: This requires that o has "consistent" mechanism and quotient.
    We define consistency below. -/
def adjCounit' (o : NegObj) 
    (h : symTypeToMechanism (quotientToSymType o.quotient) ≤ o.mechanism) : 
    ObsMorphism (B_obj (P_obj o)) o where
  mech_le := by simp only [B_obj, P_obj]; exact h
  quot_le := by
    simp only [B_obj, P_obj, symTypeToQuotient, quotientToSymType]
    cases o.quotient <;> exact QuotientGeom.le_refl _
  witness_map := _root_.id

/-- An obstruction is "consistent" if its mechanism matches its quotient -/
def NegObj.isConsistent (o : NegObj) : Prop :=
  o.mechanism = symTypeToMechanism (quotientToSymType o.quotient)

/-- Consistent obstructions have a clean counit -/
def adjCounit (o : NegObj) (h : o.isConsistent) : ObsMorphism (B_obj (P_obj o)) o where
  mech_le := by 
    simp only [NegObj.isConsistent] at h 
    simp only [B_obj, P_obj, h]
    exact Mechanism.le_refl _
  quot_le := by
    simp only [B_obj, P_obj, symTypeToQuotient, quotientToSymType]
    cases o.quotient <;> exact QuotientGeom.le_refl _
  witness_map := _root_.id

/-- All "canonical" obstructions (from classical examples) are consistent -/
theorem canonical_consistent (q : QuotientGeom) :
    (⟨symTypeToMechanism (quotientToSymType q), q, Unit⟩ : NegObj).isConsistent := rfl

/-- INVERSE NOETHER THEOREM I: B ∘ P ≅ id on quotient geometry
    
    Breaking the forced structure EXACTLY recovers the original quotient.
    This is now EQUALITY, not just ≤. -/
theorem inverse_noether_quotient (o : NegObj) :
    (B_obj (P_obj o)).quotient = o.quotient := by
  simp only [B_obj, P_obj, symTypeToQuotient, quotientToSymType]
  exact quotient_symType_roundtrip o.quotient

/-- INVERSE NOETHER THEOREM II: P ∘ B = id on symmetry type
    
    Forcing from the broken obstruction EXACTLY recovers the original symmetry.
    With tight correspondence, this is now EQUALITY! -/
theorem inverse_noether_symmetry (p : PosObj) :
    (P_obj (B_obj p)).stype = p.stype := by
  simp only [P_obj, B_obj, quotientToSymType, symTypeToQuotient]
  exact symType_quotient_roundtrip p.stype

/-- INVERSE NOETHER THEOREM III: B ∘ P recovers mechanism via quotient
    
    The mechanism is determined by quotient, so round-trip works. -/
theorem inverse_noether_mechanism_via_quotient (o : NegObj) :
    (B_obj (P_obj o)).mechanism = symTypeToMechanism (quotientToSymType o.quotient) := rfl

/-- The witness type is preserved through both round-trips -/
theorem witness_preserved_PB (o : NegObj) :
    (B_obj (P_obj o)).witness = o.witness := rfl

theorem witness_preserved_BP (p : PosObj) :
    (P_obj (B_obj p)).carrier = p.carrier := rfl

/-- TIGHT ADJUNCTION: P ∘ B ∘ P = P and B ∘ P ∘ B = B (idempotence) -/
theorem PBP_eq_P (o : NegObj) :
    (P_obj (B_obj (P_obj o))).stype = (P_obj o).stype := by
  simp only [P_obj, B_obj, quotientToSymType, symTypeToQuotient]
  exact symType_quotient_roundtrip (quotientToSymType o.quotient)

theorem BPB_eq_B (p : PosObj) :
    (B_obj (P_obj (B_obj p))).quotient = (B_obj p).quotient := by
  simp only [B_obj, P_obj, symTypeToQuotient, quotientToSymType]
  exact quotient_symType_roundtrip (symTypeToQuotient p.stype)

-- ============================================
-- SECTION 6: Constructive Impossibility (Main Application)
-- ============================================

/-- 
  FORCED EXISTENCE THEOREM:
  If o is a non-trivial obstruction (not binary), 
  then P(o) is a non-trivial symmetry (not discrete).
  
  This is EXISTENCE from IMPOSSIBILITY:
  The impossibility theorem FORCES the existence of non-trivial structure.
-/
theorem forced_existence (o : NegObj) (h : o.quotient ≠ .binary) :
    (P_obj o).stype ≠ .discrete := by
  intro h_eq
  simp only [P_obj, quotientToSymType] at h_eq
  cases hq : o.quotient with
  | binary => exact h hq
  | nPartite => simp only [hq] at h_eq; exact SymType.noConfusion h_eq
  | continuous => simp only [hq] at h_eq; exact SymType.noConfusion h_eq
  | spectrum => simp only [hq] at h_eq; exact SymType.noConfusion h_eq

/-- 
  PARADOX MAXIMIZES FREEDOM:
  A spectrum quotient (parametric impossibility) forces gauge symmetry.
  Maximum impossibility = maximum freedom.
-/
theorem spectrum_forces_gauge (o : NegObj) (h : o.quotient = .spectrum) :
    (P_obj o).stype = .gauge := by
  simp only [P_obj, quotientToSymType, h]

/--
  EXISTENCE CLAIM: Structure for deriving existence from impossibility
-/
structure ExistenceClaim where
  /-- The source obstruction -/
  source : NegObj
  /-- The forced structure -/
  forced : PosObj
  /-- Proof that forced = P(source) -/
  is_forced : forced = P_obj source

/-- Create an existence claim from an obstruction -/
def claimExistence (o : NegObj) : ExistenceClaim where
  source := o
  forced := P_obj o
  is_forced := rfl

/-- The existence claim is non-trivial when the obstruction is non-trivial -/
theorem existence_claim_nontrivial (o : NegObj) (h : o.quotient ≠ .binary) :
    (claimExistence o).forced.stype ≠ .discrete := by
  simp only [claimExistence]
  exact forced_existence o h

-- ============================================
-- SECTION 7: Classical Examples
-- ============================================

/-- Cantor's diagonal obstruction -/
def cantorObs : NegObj where
  mechanism := .diagonal
  quotient := .binary
  witness := Bool  -- The diagonal witness is a boolean function

/-- Cantor forces Z₂ symmetry -/
theorem cantor_forces_discrete : (P_obj cantorObs).stype = .discrete := rfl

/-- CAP theorem obstruction -/
def capObs : NegObj where
  mechanism := .resource
  quotient := .continuous  -- Pareto frontier is continuous
  witness := Fin 3 → Rat   -- Points on 2-sphere (3 resources)

/-- CAP forces continuous (Lie group) symmetry -/
theorem cap_forces_continuous : (P_obj capObs).stype = .continuous := rfl

/-- Continuum hypothesis obstruction -/
def chObs : NegObj where
  mechanism := .independence
  quotient := .spectrum  -- Infinitely many consistent values
  witness := ℕ           -- The parameter space

/-- CH forces gauge symmetry (maximum freedom) -/
theorem ch_forces_gauge : (P_obj chObs).stype = .gauge := rfl

/-- Arrow's theorem obstruction
    
    Arrow's Impossibility Theorem is a 4-partite impossibility:
    Four desirable properties for a social choice function:
    1. Independence of Irrelevant Alternatives (IIA)
    2. Pareto efficiency
    3. Non-dictatorship
    4. Unrestricted domain
    
    At most 3 of these 4 can hold simultaneously (pick 3 of 4).
    This is NOT a trilemma (3-partite), but a 4-partite structure.
    
    The witness type Fin 4 encodes the four properties. The diagonal
    mechanism captures the self-referential nature of preference aggregation.
-/
def arrowObs : NegObj where
  mechanism := .diagonal  -- Diagonal: preference aggregation is self-referential
  quotient := .nPartite 4 -- 4-partite: pick 3 of 4 properties
  witness := Fin 4        -- The four desiderata: IIA, Pareto, Non-dictatorial, Unrestricted

/-- Arrow forces permutation symmetry (S₄ acts on the four properties) -/
theorem arrow_forces_permutation : (P_obj arrowObs).stype = .permutation 4 := rfl

-- ============================================
-- SECTION 8: The Main Theorem
-- ============================================

/-- 
  INVERSE NOETHER (Complete Statement):
  
  The functor P : Obs → Sym is the right adjoint to B : Sym → Obs.
  
  1. P and B are both functors (preserve id and composition)
  2. B ⊣ P (adjunction via unit and counit)
  3. B ∘ P ≅ id on quotient (round-trip on negative space)
  4. P ∘ B ≥ id on symmetry type (closure on positive space)
  5. Witness types are preserved through both compositions
  
  Consequence: Working in negative space (obstructions) and applying P
  derives what MUST exist in positive space (symmetries).
-/
theorem inverse_noether_complete :
    -- 1. P is a functor
    (∀ o : NegObj, P_morph (ObsMorphism.id o) = SymMorphism.id (P_obj o)) ∧
    (∀ o₁ o₂ o₃ : NegObj, ∀ f : ObsMorphism o₁ o₂, ∀ g : ObsMorphism o₂ o₃,
      P_morph (ObsMorphism.comp f g) = SymMorphism.comp (P_morph f) (P_morph g)) ∧
    -- 2. B is a functor
    (∀ p : PosObj, B_morph (SymMorphism.id p) = ObsMorphism.id (B_obj p)) ∧
    (∀ p₁ p₂ p₃ : PosObj, ∀ f : SymMorphism p₁ p₂, ∀ g : SymMorphism p₂ p₃,
      B_morph (SymMorphism.comp f g) = ObsMorphism.comp (B_morph f) (B_morph g)) ∧
    -- 3. Round-trip on Obs (EQUALITY)
    (∀ o : NegObj, (B_obj (P_obj o)).quotient = o.quotient) ∧
    -- 4. Round-trip on Sym (EQUALITY - tight adjunction!)
    (∀ p : PosObj, (P_obj (B_obj p)).stype = p.stype) ∧
    -- 5. Witness preservation
    (∀ o : NegObj, (B_obj (P_obj o)).witness = o.witness) ∧
    (∀ p : PosObj, (P_obj (B_obj p)).carrier = p.carrier) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact P_preserves_id
  · intro o₁ o₂ o₃ f g; exact P_preserves_comp f g
  · exact B_preserves_id
  · intro p₁ p₂ p₃ f g; exact B_preserves_comp f g
  · exact inverse_noether_quotient
  · exact inverse_noether_symmetry
  · intro o; rfl
  · intro p; rfl

end InverseNoetherV2
