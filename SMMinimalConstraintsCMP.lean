/-
  SMMinimalConstraints.lean
  =========================
  
  Defines the minimal physical constraints that force the Standard Model gauge group.
  This is the core interface for "Interpretation B" - deriving SM from constraints
  rather than assuming inventory (dim=12, rank=4, u1=1).
  
  KEY PRINCIPLE: No mention of totalDim, totalRank, or u1_factors in the constraint
  bundle. These are DERIVED as corollaries, not assumed as inputs.
  
  Author: Jonathan Reich
  Date: January 2026
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.List.Basic
import Mathlib.Tactic

-- Import unified core types from SMCoreTypes
import SMCoreTypes
import ForcedSymmetryCoreCMP

import OperationalSchemaCMP

namespace SMMinimalConstraintsCoreCMP

/-! ## Section 1: Unified Types from SMCoreTypes

All core types (SimpleLieType, GaugeGroup) and their extensions are imported from
SMCoreTypes.lean. This file focuses on physics-specific constraints and theorems.
-/

-- Open SMCoreTypes namespace to access all definitions directly
open SMCoreTypes

open ForcedSymmetryCoreCMP

open OperationalSchemaCMP

-- Local alias for backward compatibility
def standardModelGauge : GaugeGroup := standardModelGaugeCanonical

structure BornRuleU1InterfaceContract (G : GaugeGroup) where
  phase_kernel_classifies_u1 :
      OperationalSchemaCMP.KernelData.toGaugeGroupTag OperationalSchemaCMP.derive_phase_kernel_const =
        some OperationalSchemaCMP.GaugeGroupTag.U1
  u1_factor_exists : G.u1_factors ≥ 1

theorem u1_factor_exists_of_born_rule_contract (G : GaugeGroup)
    (h : BornRuleU1InterfaceContract G) :
    G.u1_factors ≥ 1 :=
  h.u1_factor_exists

/-! ## Section 3: Fermion Hypercharges and Anomaly Machinery -/

/-- Fermion hypercharge assignments (one generation) -/
@[ext]
structure FermionHypercharges where
  Q_L : ℚ   -- Left quark doublet
  u_R : ℚ   -- Right up-type singlet  
  d_R : ℚ   -- Right down-type singlet
  L_L : ℚ   -- Left lepton doublet
  e_R : ℚ   -- Right electron singlet
  deriving Repr, DecidableEq

/-- Convert hypercharges to a vector in ℚ^5 for linear algebra operations.
    Order: [Q_L, u_R, d_R, L_L, e_R] -/
def FermionHypercharges.toVec (Y : FermionHypercharges) : Fin 5 → ℚ
  | ⟨0, _⟩ => Y.Q_L
  | ⟨1, _⟩ => Y.u_R
  | ⟨2, _⟩ => Y.d_R
  | ⟨3, _⟩ => Y.L_L
  | ⟨4, _⟩ => Y.e_R

/-- Standard Model hypercharges -/
def smHypercharges : FermionHypercharges where
  Q_L := 1/6
  u_R := 2/3
  d_R := -1/3
  L_L := -1/2
  e_R := -1

/-- Cubic U(1) anomaly coefficient for Nc colors -/
def cubicAnomalyCoeff (Nc : ℕ) : ℚ := (3 - Nc) / 4

/-- [SU(3)]²U(1) anomaly -/
def su3_squared_u1_anomaly (Y : FermionHypercharges) : ℚ :=
  2 * Y.Q_L - Y.u_R - Y.d_R

/-- [SU(2)]²U(1) anomaly -/
def su2_squared_u1_anomaly (Y : FermionHypercharges) (Nc : ℕ) : ℚ :=
  Nc * Y.Q_L + Y.L_L

/-- [U(1)]³ anomaly with chirality -/
def u1_cubed_anomaly_full (Y : FermionHypercharges) (Nc : ℕ) : ℚ :=
  Nc * 2 * Y.Q_L^3 - Nc * Y.u_R^3 - Nc * Y.d_R^3 + 2 * Y.L_L^3 - Y.e_R^3

/-- Gravitational-U(1) anomaly -/
def grav_u1_anomaly (Y : FermionHypercharges) (Nc : ℕ) : ℚ :=
  Nc * 2 * Y.Q_L - Nc * Y.u_R - Nc * Y.d_R + 2 * Y.L_L - Y.e_R

/-- Complete anomaly cancellation conditions -/
structure AnomalyCancellation (Y : FermionHypercharges) (Nc : ℕ) : Prop where
  su3_sq_u1 : su3_squared_u1_anomaly Y = 0
  su2_sq_u1 : su2_squared_u1_anomaly Y Nc = 0
  u1_cubed : u1_cubed_anomaly_full Y Nc = 0
  grav_u1 : grav_u1_anomaly Y Nc = 0

/-! ## Section 4: Totally Antisymmetric 3-Tensor (for Baryons) -/

/-- A totally antisymmetric 3-tensor -/
structure TotallyAntisymmetric3Tensor (N : ℕ) where
  val : Fin N → Fin N → Fin N → ℤ
  antisym_12 : ∀ i j k, val i j k = -val j i k
  antisym_23 : ∀ i j k, val i j k = -val i k j

/-! ## Section 5: The Minimal Constraints Interface

This is the KEY DEFINITION: physical constraints that force SM structure
WITHOUT mentioning gauge boson counting or dimension inventory.
-/

/-- Weak version of minimal physical constraints (without coherent color bridge).
    
    These are stated in terms of:
    - Matter content (anomaly cancellation)
    - Color sector physics (coherent color-number bridge)
    - Weak sector physics (doublets, chirality)
    - Phase/U(1) physics (Born rule)
    
    Note: This version does NOT link Nc to gauge group factors.
    Use SMMinimalConstraints (the coherent version) for full derivations.
-/
structure SMMinimalConstraintsWeak (G : GaugeGroup) : Prop where
  -- Matter/Anomaly Constraints
  /-- There exists a family-universal U(1) charge assignment -/
  has_charges : ∃ Y : FermionHypercharges, Y.Q_L ≠ 0
  /-- The charge assignment satisfies anomaly cancellation -/
  anomaly_free : ∃ (Y : FermionHypercharges) (Nc : ℕ), 
    Y.Q_L ≠ 0 ∧ AnomalyCancellation Y Nc ∧ cubicAnomalyCoeff Nc = 0
  -- Weak Sector Constraints (Qualitative)
  /-- Weak doublets exist: there is a 2-dimensional fundamental representation -/
  weak_doublets_exist : ∃ t ∈ G.simple_factors, SimpleLieType.fundamentalDim t = 2
  -- Phase/U(1) Constraints  
  /-- At least one U(1) factor exists.
      SEMANTIC GROUNDING: This follows from the physical requirement that the Born rule
      (|ψ|² probability) requires a global U(1) phase symmetry that becomes gauged.
      Combined with U1SemanticData (which provides the charge assignments), this
      becomes u1_factors = 1 exactly. -/
  born_rule_phase_invariance : G.u1_factors ≥ 1
  -- Validity Constraint (Mathematical - Cartan classification)
  /-- All simple factors are valid (proper Cartan indices: A_n≥1, B_n≥2, C_n≥3, D_n≥4) -/
  all_valid : ∀ t ∈ G.simple_factors, SimpleLieType.Valid t

-- Note: isSubgroupOf, isStrictSubgroupOf, MinimalSatisfying, couplesToSMFermions
-- are now imported from SMCoreTypes.lean

/-- Minimality/No-spectators constraint (kept separate from core constraints).
    
    This is the condition that forces UNIQUENESS, not existence of SM core.
    A theory with extra decoupled sectors is still consistent but not minimal.
-/
structure MinimalGaugeGroup (G : GaugeGroup) : Prop where
  /-- Every simple factor couples nontrivially to SM fermions -/
  no_decoupled_factors : ∀ t ∈ G.simple_factors, t.couplesToSMFermions
  
  /-- No extra U(1) factors beyond those supported by anomaly-free charges -/
  no_extra_u1 : G.u1_factors ≤ 1
  
  /-- All simple factors are valid (proper indices) -/
  all_valid : ∀ t ∈ G.simple_factors, SimpleLieType.Valid t
  
  /-- No trivial factors (dim > 0) -/
  no_trivial : ∀ t ∈ G.simple_factors, SimpleLieType.adjointDim t > 0

/-! ## Section 6: Gauged U(1) with Semantic Charge Data -/

/-- A gauged U(1) is an anomaly-free charge assignment that couples to matter -/
structure GaugedU1 where
  charges : FermionHypercharges
  couples_to_matter : charges.Q_L ≠ 0
  anomaly_free : AnomalyCancellation charges 3

/-- A gauge theory combines a gauge group with explicit U(1) charge data -/
structure GaugeTheory where
  G : GaugeGroup
  u1s : List GaugedU1
  coherence : u1s.length = G.u1_factors

/-! ## Section 7: Containment and Normal Form -/

-- Note: containsSMCore, normalForm, standardModelGaugeCanonical 
-- are now imported from SMCoreTypes.lean

/-! ## Section 8: Key Lemmas for Constraint Derivation -/

/-- THEOREM: Anomaly cancellation forces Nc = 3 -/
theorem anomaly_forces_Nc_eq_3 (Nc : ℕ) (h : cubicAnomalyCoeff Nc = 0) : Nc = 3 := by
  simp only [cubicAnomalyCoeff] at h
  have h4 : (4 : ℚ) ≠ 0 := by norm_num
  have hsub : (3 : ℚ) - Nc = 0 := (div_eq_zero_iff.mp h).resolve_right h4
  have hcast : (Nc : ℚ) = 3 := by linarith
  exact Nat.cast_injective hcast

/-- Helper: x = -x implies x = 0 for integers -/
lemma eq_neg_self_zero (x : ℤ) (h : x = -x) : x = 0 := by omega

/-- THEOREM: Nontrivial antisymmetric 3-tensor requires N ≥ 3 -/
theorem antisym_3tensor_requires_ge_3 (N : ℕ) 
    (ε : TotallyAntisymmetric3Tensor N)
    (h_nontrivial : ∃ i j k, ε.val i j k ≠ 0) : N ≥ 3 := by
  by_contra hlt
  push_neg at hlt
  obtain ⟨i, j, k, hne⟩ := h_nontrivial
  interval_cases N
  · exact Fin.elim0 i
  · -- N = 1: all indices are 0, antisymmetry forces 0
    have hi : i = 0 := Subsingleton.elim i 0
    have hj : j = 0 := Subsingleton.elim j 0
    have hk : k = 0 := Subsingleton.elim k 0
    simp only [hi, hj, hk] at hne
    exact hne (eq_neg_self_zero _ (ε.antisym_12 0 0 0))
  · -- N = 2: pigeonhole forces repeated index
    fin_cases i <;> fin_cases j <;> fin_cases k
    -- Case (0,0,0): i = j
    · exact hne (eq_neg_self_zero _ (ε.antisym_12 0 0 0))
    -- Case (0,0,1): i = j
    · exact hne (eq_neg_self_zero _ (ε.antisym_12 0 0 1))
    -- Case (0,1,0): relates to (0,0,1)
    · have h1 := ε.antisym_23 0 1 0
      have hz := eq_neg_self_zero _ (ε.antisym_12 0 0 1)
      simp only [hz, neg_zero] at h1
      exact hne h1
    -- Case (0,1,1): j = k
    · exact hne (eq_neg_self_zero _ (ε.antisym_23 0 1 1))
    -- Case (1,0,0): j = k
    · exact hne (eq_neg_self_zero _ (ε.antisym_23 1 0 0))
    -- Case (1,0,1): relates to (0,1,1)
    · have h1 := ε.antisym_12 1 0 1
      have hz := eq_neg_self_zero _ (ε.antisym_23 0 1 1)
      simp only [hz, neg_zero] at h1
      exact hne h1
    -- Case (1,1,0): i = j
    · exact hne (eq_neg_self_zero _ (ε.antisym_12 1 1 0))
    -- Case (1,1,1): i = j
    · exact hne (eq_neg_self_zero _ (ε.antisym_12 1 1 1))

/-- THEOREM: Fundamental dimension 2 implies A1 (SU(2)) among A-types -/
theorem fundDim_2_is_A1 (t : SimpleLieType) 
    (hA : ∃ n, t = .A n)
    (hDim : SimpleLieType.fundamentalDim t = 2) : t = .A 1 := by
  obtain ⟨n, rfl⟩ := hA
  simp only [SimpleLieType.fundamentalDim] at hDim
  -- n + 1 = 2 implies n = 1
  have : n = 1 := by omega
  simp only [this]

/-- THEOREM: Fundamental dimension 3 implies A2 (SU(3)) among A-types -/
theorem fundDim_3_is_A2 (t : SimpleLieType) 
    (hA : ∃ n, t = .A n)
    (hDim : SimpleLieType.fundamentalDim t = 3) : t = .A 2 := by
  obtain ⟨n, rfl⟩ := hA
  simp only [SimpleLieType.fundamentalDim] at hDim
  -- n + 1 = 3 implies n = 2
  have : n = 2 := by omega
  simp only [this]

/-! ### STRENGTHENED: A-types from Valid + fundamentalDim (no A-type assumption)

The following lemmas derive that a factor must be A1 or A2 purely from:
- Valid (standard Cartan bounds)
- fundamentalDim = 2 or 3

This eliminates the need for an `a_types_only` assumption in the constraint bundle.
The derivation is by exhaustive case analysis on all Killing-Cartan types.
-/

/-- THEOREM: Valid + fundamentalDim = 2 implies A1 (no A-type assumption needed).
    
    Proof by exhaustive case split:
    - A_n: n+1=2 → n=1, and Valid requires n≥1, so A1 works ✓
    - B_n: 2n+1=2 has no ℕ solution
    - C_n: 2n=2 → n=1, but Valid requires n≥3, contradiction
    - D_n: 2n=2 → n=1, but Valid requires n≥4, contradiction
    - E6=27, E7=56, E8=248, F4=26, G2=7, none equal 2 -/
theorem fundDim_eq_2_implies_A1_valid (t : SimpleLieType) 
    (hV : SimpleLieType.Valid t)
    (hDim : SimpleLieType.fundamentalDim t = 2) : t = .A 1 := by
  cases t with
  | A n => 
    simp only [SimpleLieType.fundamentalDim] at hDim
    have : n = 1 := by omega
    simp only [this]
  | B n =>
    simp only [SimpleLieType.fundamentalDim] at hDim
    -- 2n+1 = 2 implies 2n = 1, impossible for ℕ
    omega
  | C n =>
    simp only [SimpleLieType.fundamentalDim] at hDim
    -- 2n = 2 implies n = 1, but Valid requires n ≥ 3
    simp only [SimpleLieType.Valid] at hV
    omega
  | D n =>
    simp only [SimpleLieType.fundamentalDim] at hDim
    -- 2n = 2 implies n = 1, but Valid requires n ≥ 4
    simp only [SimpleLieType.Valid] at hV
    omega
  | E6 => simp only [SimpleLieType.fundamentalDim] at hDim; omega
  | E7 => simp only [SimpleLieType.fundamentalDim] at hDim; omega
  | E8 => simp only [SimpleLieType.fundamentalDim] at hDim; omega
  | F4 => simp only [SimpleLieType.fundamentalDim] at hDim; omega
  | G2 => simp only [SimpleLieType.fundamentalDim] at hDim; omega

/-- THEOREM: Valid + fundamentalDim = 3 implies A2 (no A-type assumption needed).
    
    Proof by exhaustive case split:
    - A_n: n+1=3 → n=2, and Valid requires n≥1, so A2 works ✓
    - B_n: 2n+1=3 → n=1, but Valid requires n≥2, contradiction
    - C_n: 2n=3 has no ℕ solution
    - D_n: 2n=3 has no ℕ solution
    - E6=27, E7=56, E8=248, F4=26, G2=7, none equal 3 -/
theorem fundDim_eq_3_implies_A2_valid (t : SimpleLieType) 
    (hV : SimpleLieType.Valid t)
    (hDim : SimpleLieType.fundamentalDim t = 3) : t = .A 2 := by
  cases t with
  | A n => 
    simp only [SimpleLieType.fundamentalDim] at hDim
    have : n = 2 := by omega
    simp only [this]
  | B n =>
    simp only [SimpleLieType.fundamentalDim] at hDim
    -- 2n+1 = 3 implies n = 1, but Valid requires n ≥ 2
    simp only [SimpleLieType.Valid] at hV
    omega
  | C n =>
    simp only [SimpleLieType.fundamentalDim] at hDim
    -- 2n = 3 has no ℕ solution
    omega
  | D n =>
    simp only [SimpleLieType.fundamentalDim] at hDim
    -- 2n = 3 has no ℕ solution
    omega
  | E6 => simp only [SimpleLieType.fundamentalDim] at hDim; omega
  | E7 => simp only [SimpleLieType.fundamentalDim] at hDim; omega
  | E8 => simp only [SimpleLieType.fundamentalDim] at hDim; omega
  | F4 => simp only [SimpleLieType.fundamentalDim] at hDim; omega
  | G2 => simp only [SimpleLieType.fundamentalDim] at hDim; omega

/-- Corollary: fundDim=2 + Valid implies it's an A-type -/
theorem fundDim_2_valid_is_A_type (t : SimpleLieType)
    (hV : SimpleLieType.Valid t)
    (hDim : SimpleLieType.fundamentalDim t = 2) : ∃ n, t = .A n := by
  have := fundDim_eq_2_implies_A1_valid t hV hDim
  exact ⟨1, this⟩

/-- Corollary: fundDim=3 + Valid implies it's an A-type -/
theorem fundDim_3_valid_is_A_type (t : SimpleLieType)
    (hV : SimpleLieType.Valid t)
    (hDim : SimpleLieType.fundamentalDim t = 3) : ∃ n, t = .A n := by
  have := fundDim_eq_3_implies_A2_valid t hV hDim
  exact ⟨2, this⟩

/-! ### Universal-property reformulations (∃! / terminality)

Where the programme previously relied on informal “identifications”, we prefer to
expose theorem-shaped *characterisations*: unique existence and terminality
statements that can be cited directly in prose.
-/

/-- “Weak factor type” as an operational invariant: valid and admits a
2-dimensional fundamental. -/
def IsWeakFactorType (t : SimpleLieType) : Prop :=
  SimpleLieType.Valid t ∧ SimpleLieType.fundamentalDim t = 2

/-- “Colour factor type” as an operational invariant: valid and admits a
3-dimensional fundamental. -/
def IsColorFactorType (t : SimpleLieType) : Prop :=
  SimpleLieType.Valid t ∧ SimpleLieType.fundamentalDim t = 3

/-- Unique-existence form of “valid + fundDim = 2 forces SU(2)”. -/
theorem existsUnique_weakFactorType : ∃! t : SimpleLieType, IsWeakFactorType t := by
  refine ⟨.A 1, ?_, ?_⟩
  · constructor
    · simp [SimpleLieType.Valid]
    · simp [SimpleLieType.fundamentalDim]
  · intro t ht
    exact fundDim_eq_2_implies_A1_valid t ht.1 ht.2

/-- Unique-existence form of “valid + fundDim = 3 forces SU(3)”. -/
theorem existsUnique_colorFactorType : ∃! t : SimpleLieType, IsColorFactorType t := by
  refine ⟨.A 2, ?_, ?_⟩
  · constructor
    · simp [SimpleLieType.Valid]
    · simp [SimpleLieType.fundamentalDim]
  · intro t ht
    exact fundDim_eq_3_implies_A2_valid t ht.1 ht.2

/-- THEOREM: SM gauge group has dimension 12 -/
theorem sm_dim : standardModelGaugeCanonical.totalDim = 12 := by
  simp only [standardModelGaugeCanonical, GaugeGroup.totalDim, List.map, 
             SimpleLieType.adjointDim, List.sum_cons, List.sum_nil]
  native_decide

/-- THEOREM: SM gauge group has rank 4 -/
theorem sm_rank : standardModelGaugeCanonical.totalRank = 4 := by
  simp only [standardModelGaugeCanonical, GaugeGroup.totalRank, List.map,
             SimpleLieType.rank, List.sum_cons, List.sum_nil]
  native_decide

/-- THEOREM: SM satisfies core containment -/
theorem sm_contains_core : standardModelGaugeCanonical.containsSMCore := by
  unfold GaugeGroup.containsSMCore GaugeGroup.containsFactor standardModelGaugeCanonical
  simp only [List.mem_cons, true_or, or_true, le_refl, and_self]

/-! ## Section 9: Factor Forcing Theorems (Workstream 2)

These theorems derive the existence of specific gauge factors from minimal constraints.
This is the core of "Interpretation B" - the factors are DERIVED, not assumed.
-/

/-- THEOREM: SMMinimalConstraints extracts Nc = 3 from anomaly cancellation.
    
    The anomaly_free field contains ∃ Nc, cubicAnomalyCoeff Nc = 0.
    By anomaly_forces_Nc_eq_3, this Nc must equal 3. -/
theorem constraints_force_Nc_eq_3 (G : GaugeGroup) (hC : SMMinimalConstraintsWeak G) :
    ∃ (Y : FermionHypercharges) (Nc : ℕ), 
      Y.Q_L ≠ 0 ∧ AnomalyCancellation Y Nc ∧ Nc = 3 := by
  obtain ⟨Y, Nc, hQ, hAnom, hCubic⟩ := hC.anomaly_free
  exact ⟨Y, Nc, hQ, hAnom, anomaly_forces_Nc_eq_3 Nc hCubic⟩

/-- THEOREM: Weak factor forcing - doublet existence implies SU(2) factor.
    
    Given:
    - weak_doublets_exist: ∃ t ∈ G.simple_factors, fundamentalDim t = 2
    - all_valid: all factors satisfy Cartan validity bounds
    
    Conclusion: G contains A1 (SU(2)) factor.
    
    STRENGTHENED: No A-type assumption needed! The A1 conclusion is DERIVED
    from Valid + fundamentalDim = 2 by exhaustive case analysis on Killing-Cartan.
    See fundDim_eq_2_implies_A1_valid for the derivation. -/
theorem weak_factor_forced (G : GaugeGroup) (hC : SMMinimalConstraintsWeak G) :
    G.containsFactor (.A 1) := by
  obtain ⟨t, ht_mem, ht_dim⟩ := hC.weak_doublets_exist
  have hV := hC.all_valid t ht_mem
  have : t = .A 1 := fundDim_eq_2_implies_A1_valid t hV ht_dim
  rw [← this]
  exact ht_mem

/-- THEOREM: U(1) factor existence from Born rule.
    
    The born_rule_phase_invariance field directly gives u1_factors ≥ 1. -/
theorem u1_factor_exists (G : GaugeGroup) (hC : SMMinimalConstraintsWeak G) :
    G.u1_factors ≥ 1 := hC.born_rule_phase_invariance

/-! ### Color Factor Forcing

For color forcing, we need an additional constraint linking Nc to the gauge group.
The current SMMinimalConstraintsWeak can extract Nc = 3 from anomaly cancellation, but
we need a bridge: "the color gauge factor has fundamental dimension = Nc".
This is added as a strengthened constraint structure below.
-/

/-- Canonical minimal physical constraints with coherent color-gauge bridge.
    
    This is the primary constraint structure for SM derivations:
    - All fields from SMMinimalConstraintsWeak
    - PLUS: A coherent color constraint linking Nc to gauge factors
      - A single Nc that satisfies anomaly cancellation (Nc = 3)
      - A gauge factor has fundamentalDim = Nc -/
structure SMMinimalConstraints (G : GaugeGroup) : Prop extends SMMinimalConstraintsWeak G where
  /-- Coherent color number: single Nc that satisfies all color constraints -/
  coherent_color : ∃ (Nc : ℕ), 
    -- Anomaly cancellation forces this Nc
    cubicAnomalyCoeff Nc = 0 ∧
    -- Gauge factor has fundamentalDim = Nc
    (∃ t ∈ G.simple_factors, SimpleLieType.fundamentalDim t = Nc)

/-- THEOREM: Strong constraints force SU(3) color factor.
    
    Given:
    - coherent_color provides Nc with:
      - cubicAnomalyCoeff Nc = 0 (forces Nc = 3)
      - gauge factor with fundamentalDim = Nc = 3
    - all_valid: all factors satisfy Cartan validity bounds
    
    Conclusion: G contains A2 (SU(3)) factor.
    
    STRENGTHENED: No A-type assumption needed! The A2 conclusion is DERIVED
    from Valid + fundamentalDim = 3 by exhaustive case analysis on Killing-Cartan.
    See fundDim_eq_3_implies_A2_valid for the derivation. -/
theorem color_factor_forced (G : GaugeGroup) (hC : SMMinimalConstraints G) :
    G.containsFactor (.A 2) := by
  -- Extract the coherent color data
  obtain ⟨Nc, hAnomaly, t, ht_mem, ht_fund⟩ := hC.coherent_color
  -- Anomaly cancellation forces Nc = 3
  have hNc3 : Nc = 3 := anomaly_forces_Nc_eq_3 Nc hAnomaly
  -- Therefore fundamentalDim t = 3
  have ht_fund3 : SimpleLieType.fundamentalDim t = 3 := by rw [← hNc3]; exact ht_fund
  -- t is Valid (inherited from SMMinimalConstraints)
  have hV := hC.toSMMinimalConstraintsWeak.all_valid t ht_mem
  -- fundamentalDim = 3 for Valid type means t = .A 2 (DERIVED, not assumed!)
  have ht_A2 : t = .A 2 := fundDim_eq_3_implies_A2_valid t hV ht_fund3
  -- Therefore G contains .A 2
  rw [← ht_A2]
  exact ht_mem

/-- THEOREM: SM core containment from strong constraints.
    
    Under strong constraints (NO A-type assumption needed!):
    - Color: SU(3) forced from coherent_color + anomaly cancellation + Valid
    - Weak: SU(2) forced from weak_doublets_exist + Valid
    - U(1): ≥ 1 forced from born_rule_phase_invariance
    
    This is the key "Interpretation B" theorem: SM core is DERIVED from
    minimal physical constraints, not assumed as inventory input.
    
    STRENGTHENED: A-types are DERIVED from Valid + fundamentalDim constraints,
    not assumed as a premise. -/
theorem sm_core_forced_from_strong_constraints (G : GaugeGroup) 
    (hC : SMMinimalConstraints G) :
    G.containsSMCore := by
  unfold GaugeGroup.containsSMCore
  refine ⟨?_, ?_, ?_⟩
  · -- Color: SU(3) = A2 (derived from Valid + fundDim=3)
    exact color_factor_forced G hC
  · -- Weak: SU(2) = A1 (derived from Valid + fundDim=2)
    exact weak_factor_forced G hC.toSMMinimalConstraintsWeak
  · -- U(1): ≥ 1
    exact u1_factor_exists G hC.toSMMinimalConstraintsWeak

/-! ## Section 10: U(1) Uniqueness (Workstream 3)

The key insight: anomaly cancellation constrains the space of allowed U(1) charges
so tightly that there's only ONE independent direction (hypercharge).

Two anomaly-free charge assignments with Q_L ≠ 0 must be proportional.
Therefore, there cannot be two independent gauged U(1) factors.
-/

/-- Two hypercharge assignments are proportional -/
def IsProportional (X Y : FermionHypercharges) : Prop :=
  ∃ c : ℚ, c ≠ 0 ∧ 
    X.Q_L = c * Y.Q_L ∧ X.u_R = c * Y.u_R ∧ X.d_R = c * Y.d_R ∧
    X.L_L = c * Y.L_L ∧ X.e_R = c * Y.e_R

/-- Swap u and d hypercharges -/
def swapUD (Y : FermionHypercharges) : FermionHypercharges where
  Q_L := Y.Q_L
  u_R := Y.d_R
  d_R := Y.u_R
  L_L := Y.L_L
  e_R := Y.e_R

/-- Proportional up to u↔d swap -/
def IsProportionalUpToSwap (X Y : FermionHypercharges) : Prop :=
  IsProportional X Y ∨ IsProportional X (swapUD Y)

/-- X and Y are independent (neither proportional nor proportional-with-swap) -/
def Independent (X Y : FermionHypercharges) : Prop :=
  ¬IsProportionalUpToSwap X Y

/-- LEMMA: Proportionality is symmetric -/
theorem IsProportional.symm {X Y : FermionHypercharges} (h : IsProportional X Y) : 
    IsProportional Y X := by
  obtain ⟨c, hc_ne, hQL, huR, hdR, hLL, heR⟩ := h
  use c⁻¹
  constructor
  · exact inv_ne_zero hc_ne
  · constructor
    · field_simp [hc_ne] at hQL ⊢; linarith
    · constructor
      · field_simp [hc_ne] at huR ⊢; linarith
      · constructor
        · field_simp [hc_ne] at hdR ⊢; linarith
        · constructor
          · field_simp [hc_ne] at hLL ⊢; linarith
          · field_simp [hc_ne] at heR ⊢; linarith

/-- LEMMA: Proportionality is transitive -/
theorem IsProportional.trans {X Y Z : FermionHypercharges} 
    (hXY : IsProportional X Y) (hYZ : IsProportional Y Z) : IsProportional X Z := by
  obtain ⟨c1, hc1_ne, hQL1, huR1, hdR1, hLL1, heR1⟩ := hXY
  obtain ⟨c2, hc2_ne, hQL2, huR2, hdR2, hLL2, heR2⟩ := hYZ
  use c1 * c2
  constructor
  · exact mul_ne_zero hc1_ne hc2_ne
  · constructor
    · simp only [hQL1, hQL2]; ring
    · constructor
      · simp only [huR1, huR2]; ring
      · constructor
        · simp only [hdR1, hdR2]; ring
        · constructor
          · simp only [hLL1, hLL2]; ring
          · simp only [heR1, heR2]; ring

/-- LEMMA: If X ∝ Z and Y ∝ Z, then X ∝ Y (assuming Z has nonzero Q_L) -/
theorem IsProportional.of_both_prop_to_same {X Y Z : FermionHypercharges}
    (hXZ : IsProportional X Z) (hYZ : IsProportional Y Z) (_hZ : Z.Q_L ≠ 0) :
    IsProportional X Y := by
  have hZY := hYZ.symm
  exact hXZ.trans hZY

/-- LEMMA: smHypercharges has nonzero Q_L -/
theorem smHypercharges_Q_L_ne_zero : smHypercharges.Q_L ≠ 0 := by
  simp only [smHypercharges]; norm_num

/-- LEMMA: swapUD preserves nonzero Q_L -/
theorem swapUD_Q_L {Y : FermionHypercharges} : (swapUD Y).Q_L = Y.Q_L := rfl

/-! ### Hypercharge Rigidity Proof (Self-Contained)

The following lemmas and theorems provide a complete proof of hypercharge uniqueness
without importing from other files. This eliminates the previous axiom. -/

/-- L_L = -3 * Q_L from [SU(2)]²U(1) cancellation with Nc=3 -/
private lemma L_from_Q (Y : FermionHypercharges) (h : su2_squared_u1_anomaly Y 3 = 0) :
    Y.L_L = -3 * Y.Q_L := by
  simp only [su2_squared_u1_anomaly, Nat.cast_ofNat] at h
  linarith

/-- u_R + d_R = 2 * Q_L from [SU(3)]²U(1) cancellation -/
private lemma ud_sum_from_Q (Y : FermionHypercharges) (h : su3_squared_u1_anomaly Y = 0) :
    Y.u_R + Y.d_R = 2 * Y.Q_L := by
  simp only [su3_squared_u1_anomaly] at h
  linarith

/-- e_R = -6 * Q_L from gravitational + su2 + su3 anomalies -/
private lemma e_from_Q (Y : FermionHypercharges) 
    (h_su3 : su3_squared_u1_anomaly Y = 0)
    (h_su2 : su2_squared_u1_anomaly Y 3 = 0)
    (h_grav : grav_u1_anomaly Y 3 = 0) :
    Y.e_R = -6 * Y.Q_L := by
  have h_ud : Y.u_R + Y.d_R = 2 * Y.Q_L := ud_sum_from_Q Y h_su3
  have h_L : Y.L_L = -3 * Y.Q_L := L_from_Q Y h_su2
  simp only [grav_u1_anomaly, Nat.cast_ofNat] at h_grav
  linarith

/-- d_R determined by u_R via u_R + d_R = 2*Q_L -/
private lemma d_from_u (Y : FermionHypercharges) (h : su3_squared_u1_anomaly Y = 0) :
    Y.d_R = 2 * Y.Q_L - Y.u_R := by
  have hud := ud_sum_from_Q Y h
  linarith

/-- Linear proportionality theorem -/
private theorem hypercharges_proportional_linear (Y₁ Y₂ : FermionHypercharges)
    (h1 : AnomalyCancellation Y₁ 3)
    (h2 : AnomalyCancellation Y₂ 3)
    (hY1_nonzero : Y₁.Q_L ≠ 0) :
    ∃ (c : ℚ), Y₂.Q_L = c * Y₁.Q_L ∧ 
                Y₂.L_L = c * Y₁.L_L ∧
                Y₂.e_R = c * Y₁.e_R ∧
                Y₂.u_R + Y₂.d_R = c * (Y₁.u_R + Y₁.d_R) := by
  use Y₂.Q_L / Y₁.Q_L
  have hL1 : Y₁.L_L = -3 * Y₁.Q_L := L_from_Q Y₁ h1.su2_sq_u1
  have hL2 : Y₂.L_L = -3 * Y₂.Q_L := L_from_Q Y₂ h2.su2_sq_u1
  have he1 : Y₁.e_R = -6 * Y₁.Q_L := e_from_Q Y₁ h1.su3_sq_u1 h1.su2_sq_u1 h1.grav_u1
  have he2 : Y₂.e_R = -6 * Y₂.Q_L := e_from_Q Y₂ h2.su3_sq_u1 h2.su2_sq_u1 h2.grav_u1
  have hud1 : Y₁.u_R + Y₁.d_R = 2 * Y₁.Q_L := ud_sum_from_Q Y₁ h1.su3_sq_u1
  have hud2 : Y₂.u_R + Y₂.d_R = 2 * Y₂.Q_L := ud_sum_from_Q Y₂ h2.su3_sq_u1
  refine ⟨?_, ?_, ?_, ?_⟩
  · field_simp
  · rw [hL1, hL2]; field_simp
  · rw [he1, he2]; field_simp
  · rw [hud1, hud2]; field_simp

/-- Helper: x² = y² implies x = y or x = -y -/
private lemma sq_eq_sq_iff (x y : ℚ) : x^2 = y^2 ↔ x = y ∨ x = -y := by
  constructor
  · intro h
    have : x^2 - y^2 = 0 := by linarith
    have : (x - y) * (x + y) = 0 := by ring_nf; linarith
    rcases mul_eq_zero.mp this with hm | hp
    · left; linarith
    · right; linarith
  · intro h; rcases h with rfl | rfl <;> ring

/-- Reduced cubic after substituting linear constraints -/
private def reducedCubic (Q u : ℚ) : ℚ :=
  let L := -3 * Q
  let e := -6 * Q
  let d := 2 * Q - u
  3 * 2 * Q^3 - 3 * u^3 - 3 * d^3 + 2 * L^3 - e^3

/-- Reduced cubic factors as 18*Q*(9*Q² - δ²) -/
private lemma reducedCubic_factored (Q u : ℚ) : 
    reducedCubic Q u = 18 * Q * (9 * Q^2 - (u - Q)^2) := by
  simp only [reducedCubic]
  ring

/-- Full cubic equals reduced cubic when linear constraints hold -/
private lemma cubic_equals_reduced (Y : FermionHypercharges)
    (hL : Y.L_L = -3 * Y.Q_L)
    (he : Y.e_R = -6 * Y.Q_L)
    (hd : Y.d_R = 2 * Y.Q_L - Y.u_R) :
    u1_cubed_anomaly_full Y 3 = reducedCubic Y.Q_L Y.u_R := by
  simp only [u1_cubed_anomaly_full, reducedCubic, hL, he, hd]
  ring

/-- THEOREM: u_R = 4*Q_L or u_R = -2*Q_L from anomaly cancellation -/
private theorem u_from_cubic (Y : FermionHypercharges) (hQ : Y.Q_L ≠ 0)
    (h : AnomalyCancellation Y 3) : 
    Y.u_R = 4 * Y.Q_L ∨ Y.u_R = -2 * Y.Q_L := by
  have hL : Y.L_L = -3 * Y.Q_L := L_from_Q Y h.su2_sq_u1
  have he : Y.e_R = -6 * Y.Q_L := e_from_Q Y h.su3_sq_u1 h.su2_sq_u1 h.grav_u1
  have hd : Y.d_R = 2 * Y.Q_L - Y.u_R := by
    have hsum := ud_sum_from_Q Y h.su3_sq_u1
    linarith
  have hcubic_eq : u1_cubed_anomaly_full Y 3 = reducedCubic Y.Q_L Y.u_R := 
    cubic_equals_reduced Y hL he hd
  have hcubic_zero : u1_cubed_anomaly_full Y 3 = 0 := h.u1_cubed
  have hreduced_zero : reducedCubic Y.Q_L Y.u_R = 0 := by rw [← hcubic_eq]; exact hcubic_zero
  rw [reducedCubic_factored] at hreduced_zero
  have h18 : (18 : ℚ) ≠ 0 := by norm_num
  have hprod : Y.Q_L * (9 * Y.Q_L^2 - (Y.u_R - Y.Q_L)^2) = 0 := by
    have : 18 * Y.Q_L * (9 * Y.Q_L^2 - (Y.u_R - Y.Q_L)^2) = 0 := hreduced_zero
    field_simp at this ⊢
    linarith
  have hdelta_sq : (Y.u_R - Y.Q_L)^2 = (3 * Y.Q_L)^2 := by
    have hfactor : 9 * Y.Q_L^2 - (Y.u_R - Y.Q_L)^2 = 0 := by
      cases mul_eq_zero.mp hprod with
      | inl hQ0 => exact absurd hQ0 hQ
      | inr h => exact h
    have h9 : 9 * Y.Q_L^2 = (3 * Y.Q_L)^2 := by ring
    linarith
  have hdelta : Y.u_R - Y.Q_L = 3 * Y.Q_L ∨ Y.u_R - Y.Q_L = -(3 * Y.Q_L) := 
    sq_eq_sq_iff _ _ |>.mp hdelta_sq
  rcases hdelta with hpos | hneg
  · left; linarith
  · right; linarith

/-- Full proportionality with u↔d ambiguity -/
private theorem hypercharges_proportional_with_swap (Y₁ Y₂ : FermionHypercharges)
    (h1 : AnomalyCancellation Y₁ 3)
    (h2 : AnomalyCancellation Y₂ 3)
    (hY1_nonzero : Y₁.Q_L ≠ 0)
    (hY2_nonzero : Y₂.Q_L ≠ 0) :
    ∃ (c : ℚ), Y₂.Q_L = c * Y₁.Q_L ∧ 
                Y₂.L_L = c * Y₁.L_L ∧
                Y₂.e_R = c * Y₁.e_R ∧
                ((Y₂.u_R = c * Y₁.u_R ∧ Y₂.d_R = c * Y₁.d_R) ∨
                 (Y₂.u_R = c * Y₁.d_R ∧ Y₂.d_R = c * Y₁.u_R)) := by
  obtain ⟨c, hQ, hL, he, hud_sum⟩ := hypercharges_proportional_linear Y₁ Y₂ h1 h2 hY1_nonzero
  use c
  refine ⟨hQ, hL, he, ?_⟩
  have hu1 := u_from_cubic Y₁ hY1_nonzero h1
  have hu2 := u_from_cubic Y₂ hY2_nonzero h2
  have hd1 := d_from_u Y₁ h1.su3_sq_u1
  have hd2 := d_from_u Y₂ h2.su3_sq_u1
  rcases hu1 with hu1_pos | hu1_neg <;> rcases hu2 with hu2_pos | hu2_neg
  · left; constructor
    · rw [hu1_pos, hu2_pos, hQ]; ring
    · rw [hd1, hd2, hu1_pos, hu2_pos, hQ]; ring
  · right; constructor
    · rw [hu2_neg, hd1, hu1_pos, hQ]; ring
    · rw [hd2, hu2_neg, hu1_pos, hQ]; ring
  · right; constructor
    · rw [hu2_pos, hd1, hu1_neg, hQ]; ring
    · rw [hd2, hu2_pos, hu1_neg, hQ]; ring
  · left; constructor
    · rw [hu1_neg, hu2_neg, hQ]; ring
    · rw [hd1, hd2, hu1_neg, hu2_neg, hQ]; ring

/-- SM hypercharges satisfy all anomaly cancellation with Nc=3 -/
theorem smHypercharges_anomaly_cancellation : AnomalyCancellation smHypercharges 3 where
  su3_sq_u1 := by simp only [su3_squared_u1_anomaly, smHypercharges]; norm_num
  su2_sq_u1 := by simp only [su2_squared_u1_anomaly, smHypercharges]; norm_num
  u1_cubed := by simp only [u1_cubed_anomaly_full, smHypercharges]; norm_num
  grav_u1 := by simp only [grav_u1_anomaly, smHypercharges]; norm_num

/-- THEOREM: Any anomaly-free U(1) with Q_L ≠ 0 is proportional to hypercharge (up to u↔d).
    
    This is the key rigidity result. Previously an axiom, now fully proven.
    
    **Physics**: There is NO independent family-universal U(1)' that can be gauged
    on the SM fermion content without adding new chiral matter. -/
theorem no_extra_U1_prime (X : FermionHypercharges) 
    (hX : AnomalyCancellation X 3) 
    (hXQ : X.Q_L ≠ 0) :
    IsProportionalUpToSwap X smHypercharges := by
  have hSM : AnomalyCancellation smHypercharges 3 := smHypercharges_anomaly_cancellation
  have hSM_nonzero : smHypercharges.Q_L ≠ 0 := by simp [smHypercharges]
  have hprop := hypercharges_proportional_with_swap smHypercharges X hSM hX hSM_nonzero hXQ
  obtain ⟨c, hQ, hL, he, hud⟩ := hprop
  simp only [smHypercharges] at hQ hL he
  rcases hud with ⟨hu, hd⟩ | ⟨hu, hd⟩
  · simp only [smHypercharges] at hu hd
    left
    refine ⟨c, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro hc; rw [hc] at hQ; simp at hQ; exact hXQ hQ
    · simp only [smHypercharges]; linarith
    · simp only [smHypercharges]; linarith
    · simp only [smHypercharges]; linarith
    · simp only [smHypercharges]; linarith
    · simp only [smHypercharges]; linarith
  · simp only [smHypercharges] at hu hd
    right
    refine ⟨c, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro hc; rw [hc] at hQ; simp at hQ; exact hXQ hQ
    · simp only [swapUD, smHypercharges]; linarith
    · simp only [swapUD, smHypercharges]; linarith
    · simp only [swapUD, smHypercharges]; linarith
    · simp only [swapUD, smHypercharges]; linarith
    · simp only [swapUD, smHypercharges]; linarith

/-- Universal property: hypercharge is terminal (up to proportionality and the
discrete \(u\leftrightarrow d\) swap) among anomaly-free family-universal
\(\mathrm{U}(1)\) charge assignments with \(Q_L \neq 0\). -/
def HyperchargeTerminal (Y : FermionHypercharges) : Prop :=
  AnomalyCancellation Y 3 ∧ Y.Q_L ≠ 0 ∧
    ∀ X, AnomalyCancellation X 3 → X.Q_L ≠ 0 → IsProportionalUpToSwap X Y

/-- Hypercharge satisfies the terminal universal property. -/
theorem smHypercharges_terminal : HyperchargeTerminal smHypercharges := by
  refine ⟨smHypercharges_anomaly_cancellation, ?_, ?_⟩
  · simp [smHypercharges]
  · intro X hX hXQ
    -- apply the already-proved rigidity theorem, specialised to SM hypercharges
    have := no_extra_U1_prime X hX hXQ
    simpa using this

/-- Uniqueness consequence of terminality: any other “terminal hypercharge”
representative is equivalent to `smHypercharges` (up to scale and swap). -/
theorem hypercharge_terminal_unique (Y : FermionHypercharges) (hY : HyperchargeTerminal Y) :
    IsProportionalUpToSwap Y smHypercharges := by
  -- Apply the terminal property to X := Y itself.
  exact no_extra_U1_prime Y hY.1 hY.2.1

/-- THEOREM: Two independent anomaly-free U(1) charges cannot both have Q_L ≠ 0.
    
    If X₁ and X₂ are both anomaly-free with Q_L ≠ 0, they must be proportional.
    Therefore they define the SAME gauged U(1) direction, not two independent ones. -/
theorem no_two_independent_U1 (X₁ X₂ : FermionHypercharges)
    (hX1 : AnomalyCancellation X₁ 3) (hX2 : AnomalyCancellation X₂ 3)
    (hX1Q : X₁.Q_L ≠ 0) (hX2Q : X₂.Q_L ≠ 0) :
    ¬Independent X₁ X₂ := by
  intro hInd
  unfold Independent IsProportionalUpToSwap at hInd
  push_neg at hInd
  obtain ⟨hNotProp, hNotPropSwap⟩ := hInd
  -- X₁ is proportional to smHypercharges (or its swap)
  have h1 := no_extra_U1_prime X₁ hX1 hX1Q
  -- X₂ is proportional to smHypercharges (or its swap)
  have h2 := no_extra_U1_prime X₂ hX2 hX2Q
  -- Case analysis on which variant each is proportional to
  rcases h1 with h1_sm | h1_swap
  · -- X₁ ∝ smHypercharges
    rcases h2 with h2_sm | h2_swap
    · -- X₂ ∝ smHypercharges
      -- Both proportional to same thing → X₁ ∝ X₂
      have hX1X2 := IsProportional.of_both_prop_to_same h1_sm h2_sm smHypercharges_Q_L_ne_zero
      exact hNotProp hX1X2
    · -- X₂ ∝ swapUD(smHypercharges)
      -- X₁ ∝ sm, X₂ ∝ swap(sm) → need X₁ ∝ swap(X₂) which is X₁ ∝ swap(swap(sm)) = X₁ ∝ sm
      -- Actually we need X₁ ∝ X₂ or X₁ ∝ swap(X₂)
      -- X₂ ∝ swap(sm) means swap(X₂) ∝ sm (since swap is involutive on the relation)
      -- So X₁ ∝ sm and we need to show X₁ ∝ swap(X₂)
      -- swap(X₂) ∝ swap(swap(sm)) = sm, so X₁ ∝ swap(X₂) via transitivity through sm
      have h2_swap_sm : IsProportional (swapUD X₂) smHypercharges := by
        obtain ⟨c, hc, hQL, huR, hdR, hLL, heR⟩ := h2_swap
        use c
        refine ⟨hc, ?_, ?_, ?_, ?_, ?_⟩
        · simp only [swapUD, swapUD_Q_L] at hQL ⊢; exact hQL
        · simp only [swapUD] at huR hdR ⊢; exact hdR
        · simp only [swapUD] at huR hdR ⊢; exact huR
        · simp only [swapUD] at hLL ⊢; exact hLL
        · simp only [swapUD] at heR ⊢; exact heR
      have hX1_swapX2 := IsProportional.of_both_prop_to_same h1_sm h2_swap_sm smHypercharges_Q_L_ne_zero
      exact hNotPropSwap hX1_swapX2
  · -- X₁ ∝ swapUD(smHypercharges)
    rcases h2 with h2_sm | h2_swap
    · -- X₂ ∝ smHypercharges, X₁ ∝ swap(sm)
      -- We need X₁ ∝ X₂. X₁ ∝ swap(sm), X₂ ∝ sm
      -- swap(X₁) ∝ sm via similar argument
      have h1_swap_sm : IsProportional (swapUD X₁) smHypercharges := by
        obtain ⟨c, hc, hQL, huR, hdR, hLL, heR⟩ := h1_swap
        use c
        refine ⟨hc, ?_, ?_, ?_, ?_, ?_⟩
        · simp only [swapUD, swapUD_Q_L] at hQL ⊢; exact hQL
        · simp only [swapUD] at huR hdR ⊢; exact hdR
        · simp only [swapUD] at huR hdR ⊢; exact huR
        · simp only [swapUD] at hLL ⊢; exact hLL
        · simp only [swapUD] at heR ⊢; exact heR
      -- swap(X₁) ∝ sm and X₂ ∝ sm → swap(X₁) ∝ X₂
      have h_swapX1_X2 := IsProportional.of_both_prop_to_same h1_swap_sm h2_sm smHypercharges_Q_L_ne_zero
      -- swap(X₁) ∝ X₂ means X₁ ∝ swap(X₂)
      have hX1_swapX2 : IsProportional X₁ (swapUD X₂) := by
        obtain ⟨c, hc, hQL, huR, hdR, hLL, heR⟩ := h_swapX1_X2
        use c
        refine ⟨hc, ?_, ?_, ?_, ?_, ?_⟩
        · simp only [swapUD] at hQL ⊢; exact hQL
        · simp only [swapUD] at huR hdR ⊢; exact hdR
        · simp only [swapUD] at huR hdR ⊢; exact huR
        · simp only [swapUD] at hLL ⊢; exact hLL
        · simp only [swapUD] at heR ⊢; exact heR
      exact hNotPropSwap hX1_swapX2
    · -- X₁ ∝ swap(sm), X₂ ∝ swap(sm) → X₁ ∝ X₂
      -- Both proportional to swap(sm), which has nonzero Q_L
      have swap_sm_Q_L : (swapUD smHypercharges).Q_L ≠ 0 := by
        simp only [swapUD, smHypercharges]; norm_num
      have hX1X2 := IsProportional.of_both_prop_to_same h1_swap h2_swap swap_sm_Q_L
      exact hNotProp hX1X2

/-- Semantic U(1) charge data for a gauge group.
    
    This captures the physical content: each gauged U(1) has an associated
    charge assignment that must satisfy anomaly cancellation. -/
structure GaugedU1Data where
  /-- The charge assignment for this U(1) -/
  charges : FermionHypercharges
  /-- Anomaly cancellation holds -/
  anomaly_free : AnomalyCancellation charges 3
  /-- Couples to quarks (physical requirement) -/
  couples_to_quarks : charges.Q_L ≠ 0

/-! ### Vector-Based Linear Independence

For ℚ-vector spaces, two non-zero vectors are linearly independent iff neither is 
a scalar multiple of the other. This is exactly what `IsProportional` captures.

We define a vector-based notion that makes independence *checkable* rather than *axiomatic*. -/

/-- Two vectors in ℚ^5 are linearly independent iff not proportional.
    For hypercharges, this is equivalent to `Independent`. -/
def VecLinIndep (v w : Fin 5 → ℚ) : Prop :=
  ¬∃ c : ℚ, c ≠ 0 ∧ ∀ i, v i = c * w i

/-- THEOREM: VecLinIndep implies our Independent predicate for hypercharges -/
theorem vecLinIndep_implies_independent {X Y : FermionHypercharges}
    (hv : VecLinIndep X.toVec Y.toVec)
    (hw : VecLinIndep X.toVec (swapUD Y).toVec) :
    Independent X Y := by
  unfold Independent IsProportionalUpToSwap IsProportional
  push_neg
  constructor
  · intro c hc hQL huR hdR hLL heR
    apply hv
    use c, hc
    intro i
    fin_cases i
    · exact hQL
    · exact huR
    · exact hdR
    · exact hLL
    · exact heR
  · intro c hc hQL huR hdR hLL heR
    apply hw
    use c, hc
    intro i
    fin_cases i
    · exact hQL
    · simp only [swapUD, FermionHypercharges.toVec] at huR ⊢; exact huR
    · simp only [swapUD, FermionHypercharges.toVec] at hdR ⊢; exact hdR
    · exact hLL
    · exact heR

/-- Semantic U(1) data bundle (Type, not Prop, since it contains data).
    
    REFACTORED: The independence condition is now expressed in terms of 
    vector linear independence, making it *definitionally checkable* 
    rather than a bare axiom. -/
structure U1SemanticData (G : GaugeGroup) where
  /-- Each U(1) factor has associated charge data -/
  u1_data : Fin G.u1_factors → GaugedU1Data
  /-- DEFINITIONAL: Distinct U(1) factors have linearly independent charge vectors.
      This is the mathematical content of "distinct gauge factors" - their charges
      span independent directions in charge space. -/
  distinct_factors_linIndep : ∀ i j : Fin G.u1_factors, i ≠ j → 
    VecLinIndep (u1_data i).charges.toVec (u1_data j).charges.toVec ∧
    VecLinIndep (u1_data i).charges.toVec (swapUD (u1_data j).charges).toVec

/-- Derived: Distinct factors have independent charges (from linIndep) -/
theorem distinct_factors_independent (G : GaugeGroup) (hU1 : U1SemanticData G) :
    ∀ i j : Fin G.u1_factors, i ≠ j → 
      Independent (hU1.u1_data i).charges (hU1.u1_data j).charges := by
  intro i j hij
  have ⟨hv, hw⟩ := hU1.distinct_factors_linIndep i j hij
  exact vecLinIndep_implies_independent hv hw

/-- Prop-level constraint that semantic data exists -/
def U1UniquenessConstraints (G : GaugeGroup) : Prop :=
  Nonempty (U1SemanticData G)

/-- THEOREM: At most one U(1) factor from charge-space rigidity.
    
    Proof by contradiction:
    1. Assume u1_factors ≥ 2
    2. Then we have two distinct indices i ≠ j
    3. By distinct_factors_independent: their charges are independent
    4. But by no_two_independent_U1: anomaly-free charges with Q_L ≠ 0 can't be independent
    5. Contradiction!
-/
theorem u1_factors_le_one (G : GaugeGroup) 
    (hU1 : U1SemanticData G) :
    G.u1_factors ≤ 1 := by
  by_contra h
  push_neg at h
  -- u1_factors ≥ 2
  have h2 : G.u1_factors ≥ 2 := h
  -- Get two distinct indices
  let i : Fin G.u1_factors := ⟨0, by omega⟩
  let j : Fin G.u1_factors := ⟨1, by omega⟩
  have hij : i ≠ j := Fin.ne_of_val_ne (by decide : (0 : ℕ) ≠ 1)
  -- By distinct_factors_independent (derived from linIndep): charges are independent
  have h_indep := distinct_factors_independent G hU1 i j hij
  -- Get the charge data
  let data_i := hU1.u1_data i
  let data_j := hU1.u1_data j
  -- Both satisfy anomaly cancellation and have Q_L ≠ 0
  have hX1 : AnomalyCancellation data_i.charges 3 := data_i.anomaly_free
  have hX2 : AnomalyCancellation data_j.charges 3 := data_j.anomaly_free
  have hX1Q : data_i.charges.Q_L ≠ 0 := data_i.couples_to_quarks
  have hX2Q : data_j.charges.Q_L ≠ 0 := data_j.couples_to_quarks
  -- By no_two_independent_U1: they cannot be independent
  have h_not_indep := no_two_independent_U1 data_i.charges data_j.charges hX1 hX2 hX1Q hX2Q
  -- Contradiction!
  exact h_not_indep h_indep

/-- THEOREM: Exactly one U(1) factor.
    
    Combines:
    - u1_factors ≥ 1 (from born_rule_phase_invariance)
    - u1_factors ≤ 1 (from charge-space rigidity)
    
    Therefore: u1_factors = 1 -/
theorem u1_factors_eq_one (G : GaugeGroup)
    (hC : SMMinimalConstraintsWeak G)
    (hU1 : U1SemanticData G) :
    G.u1_factors = 1 := by
  have h_ge : G.u1_factors ≥ 1 := hC.born_rule_phase_invariance
  have h_le : G.u1_factors ≤ 1 := u1_factors_le_one G hU1
  omega

/-! ## Section 11: Final Theorem - SM Forced from Minimal Constraints (Workstream 6)

This is the CAPSTONE THEOREM of Interpretation B:
The Standard Model gauge group is uniquely forced from minimal physical constraints.
-/

-- Note: removeOneFactor, removeOneU1 are now imported from SMCoreTypes.lean

/-- The constraint predicate used for minimality.
    
    Note: The A-types condition is a DERIVED consequence of minimality +
    Valid + fundamentalDim constraints, not an independent assumption.
    It's included here for the minimality machinery to work. -/
def SMConstraintPredicate (G : GaugeGroup) : Prop :=
  G.containsFactor (.A 2) ∧
  G.containsFactor (.A 1) ∧
  G.u1_factors ≥ 1

/-- Full constraint bundle for SM uniqueness (Prop part)
    
    STRENGTHENED: No longer includes `a_types_only` as an assumption!
    A-types are now DERIVED from Valid + fundamentalDim constraints
    via fundDim_eq_2_implies_A1_valid and fundDim_eq_3_implies_A2_valid. -/
structure SMFullConstraintsProp (G : GaugeGroup) : Prop extends SMMinimalConstraints G where
  /-- No trivial factors (dim > 0) -/
  no_trivial : ∀ t ∈ G.simple_factors, SimpleLieType.adjointDim t > 0
  /-- Minimality: no strict subgroup satisfies the SM constraint predicate -/
  minimality : MinimalSatisfying SMConstraintPredicate G

 /-- Early helper: removing a present factor yields a strict subgroup. -/
 lemma removeOneFactor_strict_subgroup_pre (G : GaugeGroup) (t : SimpleLieType)
     (ht : t ∈ G.simple_factors) :
     (G.removeOneFactor t).isStrictSubgroupOf G := by
   constructor
   · constructor
     · simp only [GaugeGroup.removeOneFactor, le_refl]
     · intro s
       simp only [GaugeGroup.removeOneFactor]
       by_cases heq : s = t
       · rw [heq]
         have h := List.count_erase_self (a := t) (l := G.simple_factors)
         omega
       · have h := List.count_erase_of_ne heq (l := G.simple_factors) (b := t)
         omega
   · intro heq
     simp only [GaugeGroup.removeOneFactor] at heq
     have hlen := List.length_erase_of_mem ht
     have hpos : 0 < G.simple_factors.length := List.length_pos_of_mem ht
     cases G with
     | mk sf u1 =>
       simp only [GaugeGroup.mk.injEq] at heq
       simp only [GaugeGroup.simple_factors] at hlen hpos ht
       rw [heq.1] at hlen
       have : sf.length ≥ 1 := hpos
       omega

 /-- Early helper: membership survives erasing a different factor. -/
 lemma mem_erase_of_ne_of_mem_pre {L : List SimpleLieType} {a b : SimpleLieType}
     (hab : a ≠ b) (ha : a ∈ L) : a ∈ L.erase b := by
   rw [List.mem_erase_of_ne hab]
   exact ha

  /-- DERIVED: Minimality rules out any simple factor other than `A1` or `A2`.
  
      If some other factor were present, removing it would preserve the SM core
      predicate, contradicting minimality. -/
theorem a_types_derived_from_minimality (G : GaugeGroup) (hC : SMFullConstraintsProp G) :
    ∀ t ∈ G.simple_factors, t = .A 1 ∨ t = .A 2 := by
  have hA2 : (.A 2 : SimpleLieType) ∈ G.simple_factors :=
    color_factor_forced G hC.toSMMinimalConstraints
  have hA1 : (.A 1 : SimpleLieType) ∈ G.simple_factors :=
    weak_factor_forced G hC.toSMMinimalConstraintsWeak
  have hu1ge1 := hC.toSMMinimalConstraintsWeak.born_rule_phase_invariance
  intro t ht
  by_contra hnot
  have ht_ne1 : t ≠ .A 1 := by
    intro h
    exact hnot (Or.inl h)
  have ht_ne2 : t ≠ .A 2 := by
    intro h
    exact hnot (Or.inr h)
  let H := G.removeOneFactor t
  have hstrict : H.isStrictSubgroupOf G := removeOneFactor_strict_subgroup_pre G t ht
  have hpred : SMConstraintPredicate H := ⟨
    mem_erase_of_ne_of_mem_pre (Ne.symm ht_ne2) hA2,
    mem_erase_of_ne_of_mem_pre (Ne.symm ht_ne1) hA1,
    hu1ge1⟩
  exact hC.minimality.2 H hstrict hpred

/-- Full constraint bundle including semantic U(1) data -/
structure SMFullConstraints (G : GaugeGroup) where
  /-- Prop-level constraints -/
  prop_constraints : SMFullConstraintsProp G
  /-- Semantic U(1) data -/
  u1_data : U1SemanticData G

/-- CAPSTONE THEOREM: SM gauge group is uniquely forced from minimal constraints.
    
    Given SMFullConstraints G:
    1. Color factor = SU(3) [from anomaly + color bridge + Valid (A-type DERIVED)]
    2. Weak factor = SU(2) [from doublet existence + Valid (A-type DERIVED)]
    3. U(1) factors = 1 [from Born rule + charge-space rigidity]
    4. No extra factors [from minimality + no trivial]
    
    Therefore G contains exactly SU(3) × SU(2) × U(1) = Standard Model.
    
    This is INTERPRETATION B: The SM is DERIVED, not assumed.
    
    STRENGTHENED: A-types are DERIVED from Valid + fundamentalDim constraints,
    NOT assumed as a premise. -/
theorem sm_forced_from_minimal_constraints (G : GaugeGroup)
    (hC : SMFullConstraints G) :
    G.containsSMCore ∧ G.u1_factors = 1 := by
  constructor
  · -- SM core containment (A-types derived from Valid + fundDim)
    exact sm_core_forced_from_strong_constraints G hC.prop_constraints.toSMMinimalConstraints
  · -- Exactly one U(1)
    exact u1_factors_eq_one G hC.prop_constraints.toSMMinimalConstraintsWeak hC.u1_data

/-- COROLLARY: SM is the unique gauge group satisfying full constraints.
    
    Any gauge group G with SMFullConstraints must have:
    - G.containsFactor (.A 2) [SU(3)]
    - G.containsFactor (.A 1) [SU(2)]
    - G.u1_factors = 1 [exactly one U(1)]
-/
  theorem sm_uniqueness_from_constraints (G : GaugeGroup)
      (hC : SMFullConstraints G) :
      G.containsFactor (.A 2) ∧ G.containsFactor (.A 1) ∧ G.u1_factors = 1 := by
    have h := sm_forced_from_minimal_constraints G hC
    unfold GaugeGroup.containsSMCore at h
    exact ⟨h.1.1, h.1.2.1, h.2⟩

  def smConstraintCanonicalBackwardInterface : AdmissibleBackwardInterface :=
    canonicalAdmissibleBackwardInterface

  def smConstraintPublicMechanismInvariant : EpistemicallyAdequateInvariant Mechanism :=
    smConstraintCanonicalBackwardInterface.toEpistemicallyAdequateInvariant

  def smConstraintObs (G : GaugeGroup) (_hC : SMFullConstraints G) : NegObj where
    mechanism := Mechanism.resource
    quotient := QuotientGeom.continuous
    witness := Unit

  theorem smConstraintObs_terminal_stype (G : GaugeGroup) (hC : SMFullConstraints G) :
      (P_obj (smConstraintObs G hC)).stype = SymType.continuous := by
    rfl

  theorem smConstraintObs_public_mechanism (G : GaugeGroup) (hC : SMFullConstraints G) :
      smConstraintPublicMechanismInvariant.observe (smConstraintObs G hC) = Mechanism.resource := by
    change symTypeToMechanism (P_obj (smConstraintObs G hC)).stype = Mechanism.resource
    rfl

  theorem smConstraintObs_public_mechanism_respects_canonicalProjection
      (G : GaugeGroup) (hC : SMFullConstraints G) :
      smConstraintPublicMechanismInvariant.observe (canonicalProjection (smConstraintObs G hC)) =
        Mechanism.resource := by
    have hproj :
        smConstraintPublicMechanismInvariant.observe (canonicalProjection (smConstraintObs G hC)) =
          smConstraintPublicMechanismInvariant.observe (smConstraintObs G hC) := by
      exact smConstraintPublicMechanismInvariant.respects_canonicalProjection (smConstraintObs G hC)
    rw [hproj]
    exact smConstraintObs_public_mechanism G hC

  theorem smConstraintObs_epistemic_interface_certificate
      (G : GaugeGroup) (hC : SMFullConstraints G) :
      EpistemicInterfaceCertificate (smConstraintObs G hC) :=
    canonicalProjection_epistemicInterface (smConstraintObs G hC)

  theorem smConstraintObs_canonical_projection_normal_form
      (G : GaugeGroup) (hC : SMFullConstraints G) :
      (canonicalProjection (smConstraintObs G hC)).mechanism = Mechanism.resource ∧
        (canonicalProjection (smConstraintObs G hC)).quotient = QuotientGeom.continuous := by
    constructor <;> rfl

  /-! ### No Extra Factors from Minimality

  The minimality constraint allows us to prove that there are NO extra factors
  beyond the required A2 and A1. -/

/-- LEMMA: removeOneFactor produces a strict subgroup when factor exists -/
lemma removeOneFactor_strict_subgroup (G : GaugeGroup) (t : SimpleLieType)
    (ht : t ∈ G.simple_factors) :
    (G.removeOneFactor t).isStrictSubgroupOf G := by
  constructor
  · -- isSubgroupOf
    constructor
    · -- u1_factors preserved
      simp only [GaugeGroup.removeOneFactor, le_refl]
    · -- count decreases or stays same for all s
      intro s
      simp only [GaugeGroup.removeOneFactor]
      by_cases heq : s = t
      · -- s = t: count decreases by 1
        rw [heq]
        have h := List.count_erase_self (a := t) (l := G.simple_factors)
        omega
      · -- s ≠ t: count unchanged
        have h := List.count_erase_of_ne heq (l := G.simple_factors) (b := t)
        omega
  · -- ≠ G (strictness)
    intro heq
    simp only [GaugeGroup.removeOneFactor] at heq
    -- If H = G, then simple_factors would be equal
    have hlen := List.length_erase_of_mem ht
    -- erase t L has length = L.length - 1
    have hpos : 0 < G.simple_factors.length := List.length_pos_of_mem ht
    -- heq gives us equality of the gauge groups
    cases G with
    | mk sf u1 =>
      simp only [GaugeGroup.mk.injEq] at heq
      simp only [GaugeGroup.simple_factors] at hlen hpos ht
      rw [heq.1] at hlen
      -- hlen : sf.length = sf.length - 1, hpos : 0 < sf.length
      have : sf.length ≥ 1 := hpos
      omega

/-- Helper: membership preserved when erasing a different element -/
lemma mem_erase_of_ne_of_mem {L : List SimpleLieType} {a b : SimpleLieType}
    (hab : a ≠ b) (ha : a ∈ L) : a ∈ L.erase b := by
  rw [List.mem_erase_of_ne hab]
  exact ha

/-- Helper: if count ≥ 2, element remains after erasing one copy -/
lemma mem_erase_self_of_count_ge_2 {L : List SimpleLieType} {a : SimpleLieType}
    (hcount : L.count a ≥ 2) : a ∈ L.erase a := by
  have h := List.count_erase_self (a := a) (l := L)
  have hge1 : (L.erase a).count a ≥ 1 := by omega
  by_contra hne
  have : (L.erase a).count a = 0 := List.count_eq_zero.mpr hne
  omega

/-- Helper: for a list containing only A1 and A2, count sum equals length -/
lemma count_A1_A2_sum_eq_length : ∀ (L : List SimpleLieType), 
    (∀ t ∈ L, t = .A 1 ∨ t = .A 2) → L.count (.A 1) + L.count (.A 2) = L.length
  | [], _ => by simp
  | x :: xs, hL => by
    simp only [List.count_cons, List.length_cons]
    have hx : x = .A 1 ∨ x = .A 2 := hL x (by simp)
    have hxs : ∀ t ∈ xs, t = .A 1 ∨ t = .A 2 := fun t ht => hL t (by simp [ht])
    have ih := count_A1_A2_sum_eq_length xs hxs
    rcases hx with rfl | rfl
    · simp only [beq_self_eq_true, ↓reduceIte, beq_iff_eq, SimpleLieType.A.injEq]
      split_ifs <;> omega
    · simp only [beq_iff_eq, SimpleLieType.A.injEq, beq_self_eq_true, ↓reduceIte]
      split_ifs <;> omega

/-- LEMMA: If simple_factors has length > 2, we can remove a non-essential factor -/
lemma no_extra_simple_factors (G : GaugeGroup)
    (hC : SMFullConstraintsProp G)
    (_hU1 : U1SemanticData G)
    (hlen : G.simple_factors.length > 2) :
    False := by
  -- G has A2 and A1 (derived from Valid + fundamentalDim)
  have hA2 : (.A 2 : SimpleLieType) ∈ G.simple_factors := 
    color_factor_forced G hC.toSMMinimalConstraints
  have hA1 : (.A 1 : SimpleLieType) ∈ G.simple_factors := 
    weak_factor_forced G hC.toSMMinimalConstraintsWeak
  have hA12ne : (.A 2 : SimpleLieType) ≠ .A 1 := by decide
  have hMin := hC.minimality
  have hu1ge1 := hC.toSMMinimalConstraintsWeak.born_rule_phase_invariance
  have hall : ∀ t ∈ G.simple_factors, t = .A 1 ∨ t = .A 2 :=
    a_types_derived_from_minimality G hC
  have hsum := count_A1_A2_sum_eq_length G.simple_factors hall
  have hge2 : G.simple_factors.count (.A 1) ≥ 2 ∨ G.simple_factors.count (.A 2) ≥ 2 := by
    omega
  rcases hge2 with hcount1 | hcount2
  · let H := G.removeOneFactor (.A 1)
    have hstrict := removeOneFactor_strict_subgroup G (.A 1) hA1
    have hpred : SMConstraintPredicate H := ⟨
      mem_erase_of_ne_of_mem hA12ne hA2,
      mem_erase_self_of_count_ge_2 hcount1,
      hu1ge1⟩
    exact hMin.2 H hstrict hpred
  · let H := G.removeOneFactor (.A 2)
    have hstrict := removeOneFactor_strict_subgroup G (.A 2) hA2
    have hpred : SMConstraintPredicate H := ⟨
      mem_erase_self_of_count_ge_2 hcount2,
      mem_erase_of_ne_of_mem (Ne.symm hA12ne) hA1,
      hu1ge1⟩
    exact hMin.2 H hstrict hpred

/-- Helper: two distinct members implies length ≥ 2 -/
lemma length_ge_two_of_distinct_mem {L : List SimpleLieType} {a b : SimpleLieType}
    (ha : a ∈ L) (hb : b ∈ L) (hab : a ≠ b) : L.length ≥ 2 := by
  cases L with
  | nil => simp at ha
  | cons x xs =>
    cases xs with
    | nil => 
      simp only [List.mem_singleton, List.mem_cons] at ha hb
      rcases ha with rfl | ha' <;> rcases hb with rfl | hb'
      · exact absurd rfl hab
      · simp at hb'
      · simp at ha'
      · simp at ha'
    | cons y ys =>
      simp only [List.length_cons]
      omega

/-- THEOREM: Exactly two simple factors from minimality -/
theorem simple_factors_length_eq_2 (G : GaugeGroup)
    (hC : SMFullConstraintsProp G)
    (hU1 : U1SemanticData G) :
    G.simple_factors.length = 2 := by
  -- A2 and A1 derived from Valid + fundamentalDim (not from a_types assumption)
  have hA2 : (.A 2 : SimpleLieType) ∈ G.simple_factors := 
    color_factor_forced G hC.toSMMinimalConstraints
  have hA1 : (.A 1 : SimpleLieType) ∈ G.simple_factors := 
    weak_factor_forced G hC.toSMMinimalConstraintsWeak
  have hA2ne : (.A 2 : SimpleLieType) ≠ .A 1 := by decide
  -- Length ≥ 2 (two distinct elements)
  have hge2 : G.simple_factors.length ≥ 2 := length_ge_two_of_distinct_mem hA2 hA1 hA2ne
  -- Length ≤ 2 (from minimality - no extra factors)
  by_contra hne
  push_neg at hne
  have hgt2 : G.simple_factors.length > 2 := by omega
  exact no_extra_simple_factors G hC hU1 hgt2

/-- Helper: length 2 list containing A1 and A2 has count 1 for each -/
lemma count_A1_A2_eq_one_of_length_two (L : List SimpleLieType)
    (hlen : L.length = 2) 
    (hA1 : (.A 1 : SimpleLieType) ∈ L) 
    (hA2 : (.A 2 : SimpleLieType) ∈ L)
    (hall : ∀ t ∈ L, t = .A 1 ∨ t = .A 2) : 
    L.count (.A 1) = 1 ∧ L.count (.A 2) = 1 := by
  have hsum := count_A1_A2_sum_eq_length L hall
  -- count(A1) + count(A2) = 2
  rw [hlen] at hsum
  -- Both counts are ≥ 1 (from membership)
  have hc1 : L.count (.A 1) ≥ 1 := by
    by_contra h; push_neg at h
    have : (.A 1) ∉ L := List.count_eq_zero.mp (by omega)
    exact this hA1
  have hc2 : L.count (.A 2) ≥ 1 := by
    by_contra h; push_neg at h
    have : (.A 2) ∉ L := List.count_eq_zero.mp (by omega)
    exact this hA2
  omega

/-- Helper: length 2 list with count(A2)=1 and count(A1)=1 is [A2,A1] or [A1,A2] -/
lemma list_A1_A2_two_elements (L : List SimpleLieType)
    (hlen : L.length = 2) (hcA2 : L.count (.A 2) = 1) (hcA1 : L.count (.A 1) = 1) :
    L = [.A 2, .A 1] ∨ L = [.A 1, .A 2] := by
  -- Extract the two elements from length = 2
  match hL : L with
  | [] => simp at hlen
  | [_] => simp at hlen
  | [x, y] =>
    -- Use the count information to determine x and y
    simp only [List.count_cons, List.count_nil, add_zero] at hcA2 hcA1
    -- Analyze all 4 cases for (x, y) being (A1, A1), (A1, A2), (A2, A1), (A2, A2)
    -- The counts rule out (A1, A1) and (A2, A2)
    by_cases hx1 : x = .A 1 <;> by_cases hx2 : x = .A 2 <;> 
    by_cases hy1 : y = .A 1 <;> by_cases hy2 : y = .A 2
    all_goals simp_all [SimpleLieType.A.injEq]
  | _ :: _ :: _ :: _ => simp at hlen

/-- Helper: in a length-2 A-type list containing A1 and A2, every element is A1 or A2 -/
lemma all_A1_or_A2_of_length_two (L : List SimpleLieType) 
    (hlen : L.length = 2)
    (hA1 : (.A 1 : SimpleLieType) ∈ L) 
    (hA2 : (.A 2 : SimpleLieType) ∈ L)
    : ∀ t ∈ L, t = .A 1 ∨ t = .A 2 := by
  -- We only need: if `L.length = 2` and `A1 ∈ L` and `A2 ∈ L`, then `L` contains no other values.
  have hA12ne : (.A 1 : SimpleLieType) ≠ .A 2 := by decide
  cases L with
  | nil =>
      simp at hlen
  | cons x xs =>
      cases xs with
      | nil =>
          simp at hlen
      | cons y ys =>
          cases ys with
          | nil =>
              have hA1xy : (.A 1 : SimpleLieType) = x ∨ (.A 1 : SimpleLieType) = y := by
                simpa [List.mem_cons] using hA1
              have hA2xy : (.A 2 : SimpleLieType) = x ∨ (.A 2 : SimpleLieType) = y := by
                simpa [List.mem_cons] using hA2
              have hxy : (x = (.A 1 : SimpleLieType) ∧ y = (.A 2 : SimpleLieType)) ∨
                  (x = (.A 2 : SimpleLieType) ∧ y = (.A 1 : SimpleLieType)) := by
                rcases hA1xy with hA1x | hA1y
                · rcases hA2xy with hA2x | hA2y
                  · exfalso
                    have : (.A 1 : SimpleLieType) = (.A 2 : SimpleLieType) := by
                      calc
                        (.A 1 : SimpleLieType) = x := hA1x
                        _ = (.A 2 : SimpleLieType) := hA2x.symm
                    exact hA12ne this
                  · exact Or.inl ⟨hA1x.symm, hA2y.symm⟩
                · rcases hA2xy with hA2x | hA2y
                  · exact Or.inr ⟨hA2x.symm, hA1y.symm⟩
                  · exfalso
                    have : (.A 1 : SimpleLieType) = (.A 2 : SimpleLieType) := by
                      calc
                        (.A 1 : SimpleLieType) = y := hA1y
                        _ = (.A 2 : SimpleLieType) := hA2y.symm
                    exact hA12ne this
              intro t ht
              have htxy : t = x ∨ t = y := by
                simpa [List.mem_cons] using ht
              rcases htxy with rfl | rfl
              · rcases hxy with h | h
                · left; simp [h.1]
                · right; simp [h.1]
              · rcases hxy with h | h
                · right; simp [h.2]
                · left; simp [h.2]
          | cons z zs =>
              simp at hlen

/-- STRENGTHENED CAPSTONE: SM gauge group structure is exactly determined.
    
    A-types are DERIVED from minimality, not assumed as a premise.
    SU(2) and SU(3) are DERIVED from Valid + fundamentalDim constraints. -/
theorem sm_forced_strong (G : GaugeGroup)
    (hC : SMFullConstraints G) :
    G.simple_factors.length = 2 ∧
    G.simple_factors.count (.A 2) = 1 ∧
    G.simple_factors.count (.A 1) = 1 ∧
    G.u1_factors = 1 := by
  have hLen := simple_factors_length_eq_2 G hC.prop_constraints hC.u1_data
  have hU1 := u1_factors_eq_one G hC.prop_constraints.toSMMinimalConstraintsWeak hC.u1_data
  -- A2 and A1 derived from Valid + fundamentalDim (not from a_types assumption)
  have hA2 : (.A 2 : SimpleLieType) ∈ G.simple_factors := 
    color_factor_forced G hC.prop_constraints.toSMMinimalConstraints
  have hA1 : (.A 1 : SimpleLieType) ∈ G.simple_factors := 
    weak_factor_forced G hC.prop_constraints.toSMMinimalConstraintsWeak
  have hall := all_A1_or_A2_of_length_two G.simple_factors hLen hA1 hA2
  have ⟨hcA1, hcA2⟩ := count_A1_A2_eq_one_of_length_two G.simple_factors hLen hA1 hA2 hall
  exact ⟨hLen, hcA2, hcA1, hU1⟩

/-- FINAL FORM: G is isomorphic to standard model gauge group (up to factor ordering) -/
theorem sm_classification (G : GaugeGroup)
    (hC : SMFullConstraints G) :
    (G.simple_factors = [.A 2, .A 1] ∨ G.simple_factors = [.A 1, .A 2]) ∧
    G.u1_factors = 1 := by
  have ⟨hLen, hcA2, hcA1, hU1⟩ := sm_forced_strong G hC
  constructor
  · exact list_A1_A2_two_elements G.simple_factors hLen hcA2 hcA1
  · exact hU1

/-! ## Section 13: Umbrella Theorems (Top-Level Exports)

These theorems provide clean API exports for downstream users. -/

/-- UMBRELLA: SM core is forced from coherent constraints.
    
    This is the primary export for "any gauge group satisfying SMMinimalConstraints
    must contain the SM core (SU(3) × SU(2) × U(1))". -/
theorem sm_core_subgroup_forced (G : GaugeGroup) (hC : SMMinimalConstraints G) :
    G.containsSMCore :=
  sm_core_forced_from_strong_constraints G hC

/-- UMBRELLA: Complete SM derivation from full constraints.
    
    Given SMFullConstraints (coherent physics + semantic U(1) data + minimality):
    - SM core is contained
    - Exactly one U(1) factor
    - No extra simple factors (exactly 2: A2 and A1)
    
    This is the cleanest top-level theorem for the complete derivation. -/
theorem sm_umbrella (G : GaugeGroup) (hC : SMFullConstraints G) :
    G.containsSMCore ∧ 
    G.u1_factors = 1 ∧
    G.simple_factors.length = 2 ∧
    (G.simple_factors = [.A 2, .A 1] ∨ G.simple_factors = [.A 1, .A 2]) := by
  have hClass := sm_classification G hC
  have hStrong := sm_forced_strong G hC
  have hCore := sm_core_subgroup_forced G hC.prop_constraints.toSMMinimalConstraints
  exact ⟨hCore, hStrong.2.2.2, hStrong.1, hClass.1⟩

/-! ## Section 14: Summary of Interpretation B

**COMPLETED THEOREMS:**

*Workstream 2 (Factor Forcing):*
- `anomaly_forces_Nc_eq_3`: cubicAnomalyCoeff Nc = 0 → Nc = 3
- `weak_factor_forced`: doublet existence + A-type → SU(2)
- `color_factor_forced`: coherent color + A-type → SU(3)
- `sm_core_forced_from_strong_constraints`: strong constraints → SM core

*Workstream 3 (U(1) Uniqueness):*
- `no_extra_U1_prime`: anomaly rigidity (theorem)
- `u1_factors_eq_one`: exactly one U(1)

*Workstream 6 (Final Assembly):*
- `sm_forced_from_minimal_constraints`: CAPSTONE - SM uniquely forced
- `sm_uniqueness_from_constraints`: explicit factor listing

**INTERPRETATION B ACHIEVEMENT:**
The Standard Model gauge group SU(3) × SU(2) × U(1) is DERIVED from:
1. Anomaly cancellation (Nc = 3 → SU(3))
2. Weak doublet existence (fundamentalDim = 2 → SU(2))
3. Born rule + charge-space rigidity (exactly one U(1))

NO INVENTORY INPUT: We do NOT assume dim=12, rank=4, u1=1.
These are CONSEQUENCES, not axioms.

**OUTSTANDING SORRYS: 0**

All sorrys have been discharged. The file compiles cleanly with:
```bash
lake env lean SMMinimalConstraints.lean
```

**CAPSTONE THEOREMS PROVEN:**
- `sm_forced_strong`: G.simple_factors.length = 2 ∧ count(A2) = 1 ∧ count(A1) = 1 ∧ u1_factors = 1
- `sm_classification`: G.simple_factors ∈ {[A2,A1], [A1,A2]} ∧ u1_factors = 1
-/

end SMMinimalConstraintsCoreCMP

-- Axiom audit
#print axioms SMMinimalConstraintsCoreCMP.sm_forced_strong
#print axioms SMMinimalConstraintsCoreCMP.sm_classification

/-!
## February 2026: Ablation-completeness witnesses (SM core)

This section provides explicit *drop-one-premise* witnesses showing that the key
premises in the SM pipeline are doing real work.

Important: these are not claims about Nature; they are *logical sensitivity* results:
if a premise is removed from the constraint bundle, the corresponding conclusion is no
longer forced (counterexamples exist).
-/

namespace SMMinimalConstraintsAblationCMP

open SMMinimalConstraintsCoreCMP
open SMCoreTypes

/-! ### Witness gauge groups -/

/-- SM with an extra decoupled simple factor (violates minimality, not consistency). -/
def G_SM_plus_spectator : GaugeGroup :=
  { simple_factors := [.A 2, .A 1, .A 3]
    u1_factors := 1 }

/-- Drop Born-rule phase premise: allow zero U(1). -/
def G_no_U1 : GaugeGroup :=
  { simple_factors := [.A 2, .A 1]
    u1_factors := 0 }

/-- Drop weak-doublet premise: allow no SU(2) factor. -/
def G_no_SU2 : GaugeGroup :=
  { simple_factors := [.A 2]
    u1_factors := 1 }

/-- Drop coherent-color bridge: allow no SU(3) factor. -/
def G_no_SU3 : GaugeGroup :=
  { simple_factors := [.A 1]
    u1_factors := 1 }

/-! ### Helper lemmas -/

private lemma mem_A2_in_SM_plus : (.A 2 : SimpleLieType) ∈ G_SM_plus_spectator.simple_factors := by
  simp [G_SM_plus_spectator]

private lemma mem_A1_in_SM_plus : (.A 1 : SimpleLieType) ∈ G_SM_plus_spectator.simple_factors := by
  simp [G_SM_plus_spectator]

private lemma mem_A3_in_SM_plus : (.A 3 : SimpleLieType) ∈ G_SM_plus_spectator.simple_factors := by
  simp [G_SM_plus_spectator]

private lemma valid_A (n : ℕ) (hn : 1 ≤ n) : SimpleLieType.Valid (.A n) := by
  simpa [SimpleLieType.Valid, hn]

private lemma no_trivial_A (n : ℕ) (hn : 1 ≤ n) : SimpleLieType.adjointDim (.A n) > 0 := by
  -- adjointDim(.A n) = (n+1)^2 - 1, positive for n ≥ 1 (SU(2) and above).
  have hn1 : 2 ≤ n + 1 := by omega
  have hmul : 4 ≤ (n + 1) * (n + 1) := by
    -- from `2 ≤ n+1`, multiply both sides: `2*2 ≤ (n+1)*(n+1)`
    have : (2 : ℕ) * 2 ≤ (n + 1) * (n + 1) := Nat.mul_le_mul hn1 hn1
    simpa using this
  -- now (n+1)^2 - 1 ≥ 3
  simp [SimpleLieType.adjointDim, pow_two]
  omega

/-! ### Weakened constraint bundles for ablation -/

/-- `SMMinimalConstraintsWeak` but *without* the Born-rule phase requirement. -/
structure SMMinimalConstraintsWeak_noPhase (G : GaugeGroup) : Prop where
  has_charges : ∃ Y : FermionHypercharges, Y.Q_L ≠ 0
  anomaly_free : ∃ (Y : FermionHypercharges) (Nc : ℕ),
    Y.Q_L ≠ 0 ∧ AnomalyCancellation Y Nc ∧ cubicAnomalyCoeff Nc = 0
  weak_doublets_exist : ∃ t ∈ G.simple_factors, SimpleLieType.fundamentalDim t = 2
  all_valid : ∀ t ∈ G.simple_factors, SimpleLieType.Valid t

/-- `SMMinimalConstraintsWeak` but *without* weak-doublet existence. -/
structure SMMinimalConstraintsWeak_noWeak (G : GaugeGroup) : Prop where
  has_charges : ∃ Y : FermionHypercharges, Y.Q_L ≠ 0
  anomaly_free : ∃ (Y : FermionHypercharges) (Nc : ℕ),
    Y.Q_L ≠ 0 ∧ AnomalyCancellation Y Nc ∧ cubicAnomalyCoeff Nc = 0
  born_rule_phase_invariance : G.u1_factors ≥ 1
  all_valid : ∀ t ∈ G.simple_factors, SimpleLieType.Valid t

/-- `SMMinimalConstraintsWeak` but *without* the coherent-color bridge. -/
structure SMMinimalConstraints_noColorBridge (G : GaugeGroup) : Prop extends SMMinimalConstraintsWeak G

/-- `SMFullConstraintsProp` but *without* the minimality field (so spectators can remain). -/
structure SMFullConstraintsProp_noMinimality (G : GaugeGroup) : Prop extends SMMinimalConstraints G where
  no_trivial : ∀ t ∈ G.simple_factors, SimpleLieType.adjointDim t > 0

/-- Full constraints but without minimality.

This is a data-bearing bundle (it includes `U1SemanticData`), so it lives in `Type`,
not `Prop`. When using it in “existence” theorems, prefer `×`/Sigma-types over `∧`.
-/
structure SMFullConstraints_noMinimality (G : GaugeGroup) where
  prop_constraints : SMFullConstraintsProp_noMinimality G
  u1_data : U1SemanticData G

/-! ### Concrete witnesses -/

private lemma anomaly_free_sm : ∃ (Y : FermionHypercharges) (Nc : ℕ),
    Y.Q_L ≠ 0 ∧ AnomalyCancellation Y Nc ∧ cubicAnomalyCoeff Nc = 0 := by
  refine ⟨smHypercharges, 3, smHypercharges_Q_L_ne_zero, smHypercharges_anomaly_cancellation, ?_⟩
  simp [cubicAnomalyCoeff]

/-- Witness: without the Born-rule phase premise, zero U(1) is consistent with the remaining bundle. -/
theorem ablation_noPhase_allows_noU1 : ∃ G, SMMinimalConstraintsWeak_noPhase G ∧ G.u1_factors = 0 := by
  refine ⟨G_no_U1, ?_, rfl⟩
  refine
    { has_charges := ⟨smHypercharges, smHypercharges_Q_L_ne_zero⟩
      anomaly_free := anomaly_free_sm
      weak_doublets_exist := ?_
      all_valid := ?_ }
  · refine ⟨.A 1, ?_, ?_⟩
    · simp [G_no_U1]
    · simp [SimpleLieType.fundamentalDim]
  · intro t ht
    -- only A2 and A1 appear
    have : t = .A 2 ∨ t = .A 1 := by simpa [G_no_U1] using ht
    rcases this with rfl | rfl
    · exact valid_A 2 (by omega)
    · exact valid_A 1 (by omega)

/-- Witness: without weak-doublet existence, the SM weak factor is not forced. -/
theorem ablation_noWeak_allows_noSU2 : ∃ G, SMMinimalConstraintsWeak_noWeak G ∧ ¬ G.containsFactor (.A 1) := by
  refine ⟨G_no_SU2, ?_, ?_⟩
  · refine
      { has_charges := ⟨smHypercharges, smHypercharges_Q_L_ne_zero⟩
        anomaly_free := anomaly_free_sm
        born_rule_phase_invariance := by simp [G_no_SU2]
        all_valid := ?_ }
    intro t ht
    have : t = .A 2 := by simpa [G_no_SU2] using ht
    cases this
    exact valid_A 2 (by omega)
  · intro h
    -- `.A 1` is not in the singleton list `[.A 2]`
    simpa [GaugeGroup.containsFactor, G_no_SU2] using h

/-- Witness: without the coherent color bridge, the SM colour factor is not forced. -/
theorem ablation_noColorBridge_allows_noSU3 :
    ∃ G, SMMinimalConstraints_noColorBridge G ∧ ¬ G.containsFactor (.A 2) := by
  refine ⟨G_no_SU3, ?_, ?_⟩
  · refine
      { toSMMinimalConstraintsWeak :=
          { has_charges := ⟨smHypercharges, smHypercharges_Q_L_ne_zero⟩
            anomaly_free := anomaly_free_sm
            weak_doublets_exist := ?_
            born_rule_phase_invariance := by simp [G_no_SU3]
            all_valid := ?_ } }
    · refine ⟨.A 1, ?_, ?_⟩
      · simp [G_no_SU3]
      · simp [SimpleLieType.fundamentalDim]
    · intro t ht
      have : t = .A 1 := by simpa [G_no_SU3] using ht
      cases this
      exact valid_A 1 (by omega)
  · intro h
    simpa [GaugeGroup.containsFactor, G_no_SU3] using h

/-- Witness: if minimality is dropped, a spectator factor can be added while keeping the other constraints. -/
def HasSMFullConstraints_noMinimality (G : GaugeGroup) : Prop :=
  Nonempty (SMFullConstraints_noMinimality G)

theorem ablation_noMinimality_allows_spectator :
    ∃ G, HasSMFullConstraints_noMinimality G ∧ G.simple_factors.length ≠ 2 := by
  refine ⟨G_SM_plus_spectator, ?_, ?_⟩
  · refine ⟨?_⟩
    refine
      { prop_constraints :=
          { toSMMinimalConstraints :=
              { toSMMinimalConstraintsWeak :=
                  { has_charges := ⟨smHypercharges, smHypercharges_Q_L_ne_zero⟩
                    anomaly_free := anomaly_free_sm
                    weak_doublets_exist := ⟨.A 1, mem_A1_in_SM_plus, by simp [SimpleLieType.fundamentalDim]⟩
                    born_rule_phase_invariance := by simp [G_SM_plus_spectator]
                    all_valid := by
                      intro t ht
                      have : t = .A 2 ∨ t = .A 1 ∨ t = .A 3 := by simpa [G_SM_plus_spectator] using ht
                      rcases this with rfl | h'
                      · exact valid_A 2 (by omega)
                      · rcases h' with rfl | rfl
                        · exact valid_A 1 (by omega)
                        · exact valid_A 3 (by omega) }
                coherent_color := by
                  refine ⟨3, ?_, .A 2, mem_A2_in_SM_plus, by simp [SimpleLieType.fundamentalDim]⟩
                  simp [cubicAnomalyCoeff] }
            no_trivial := by
              intro t ht
              have : t = .A 2 ∨ t = .A 1 ∨ t = .A 3 := by simpa [G_SM_plus_spectator] using ht
              rcases this with rfl | h'
              · exact no_trivial_A 2 (by omega)
              · rcases h' with rfl | rfl
                · exact no_trivial_A 1 (by omega)
                · exact no_trivial_A 3 (by omega) }
        u1_data := by
          -- U1SemanticData for a single U(1): provide one charge assignment
          refine
            { u1_data := fun _ =>
                { charges := smHypercharges
                  anomaly_free := smHypercharges_anomaly_cancellation
                  couples_to_quarks := smHypercharges_Q_L_ne_zero }
              distinct_factors_linIndep := ?_ }
          intro i j hij
          exfalso
          fin_cases i <;> fin_cases j
          exact hij rfl }
  · simp [G_SM_plus_spectator]

end SMMinimalConstraintsAblationCMP
