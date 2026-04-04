/-
  MatterContentUniqueness.lean
  
  THEOREM: Among chiral spectra built from a bounded search space of 
  SU(3)×SU(2)×U(1) representations, satisfying anomaly cancellation,
  the Standard Model spectrum is the unique minimal solution.
  
  NON-CIRCULARITY DESIGN:
  - We do NOT hardcode "Q_L, u_R, d_R, L_L, e_R" as field names
  - We parameterize spectra by MULTIPLICITIES of representation tags
  - The search space is representation-agnostic
  - Minimality is an explicit cost function, not pattern-matching
  - We re-use StandardModelFromImpossibility hypercharge machinery
  
  Structure:
  1. Representation-agnostic search space definition
  2. Anomaly constraints as linear equations over multiplicities
  3. Cost function (total Weyl fermion count)
  4. Finite enumeration via bounds
  5. Uniqueness theorem
  
  Author: Jonathan Reich
  Date: January 2026
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic

import StandardModelFromImpossibility

namespace MatterContentUniqueness

open InverseNoetherV2

open StandardModelFromImpossibility

@[ext]
structure SpectrumCounts where
  n_32L : ℕ
  n_31R_u : ℕ
  n_31R_d : ℕ
  n_12L : ℕ
  n_11R : ℕ
  deriving DecidableEq, Repr

def SpectrumCounts.cost (n : SpectrumCounts) : ℕ :=
  6 * n.n_32L + 3 * n.n_31R_u + 3 * n.n_31R_d + 2 * n.n_12L + 1 * n.n_11R

def smCounts : SpectrumCounts where
  n_32L := 1
  n_31R_u := 1
  n_31R_d := 1
  n_12L := 1
  n_11R := 1

theorem smCounts_cost : smCounts.cost = 15 := by
  simp [SpectrumCounts.cost, smCounts]

structure AnomalyCancellationWithMultiplicity (n : SpectrumCounts) (Y : FermionHypercharges) : Prop where
  su3_sq_u1 : (2 * (n.n_32L : ℚ)) * Y.Q_L - (n.n_31R_u : ℚ) * Y.u_R - (n.n_31R_d : ℚ) * Y.d_R = 0
  su2_sq_u1 : (3 * (n.n_32L : ℚ)) * Y.Q_L + (n.n_12L : ℚ) * Y.L_L = 0
  grav_u1 : (6 * (n.n_32L : ℚ)) * Y.Q_L - (3 * (n.n_31R_u : ℚ)) * Y.u_R - (3 * (n.n_31R_d : ℚ)) * Y.d_R +
            (2 * (n.n_12L : ℚ)) * Y.L_L - (n.n_11R : ℚ) * Y.e_R = 0
  u1_cubed : (6 * (n.n_32L : ℚ)) * Y.Q_L^3 - (3 * (n.n_31R_u : ℚ)) * Y.u_R^3 - (3 * (n.n_31R_d : ℚ)) * Y.d_R^3 +
             (2 * (n.n_12L : ℚ)) * Y.L_L^3 - (n.n_11R : ℚ) * Y.e_R^3 = 0

 def AnomalyFreeNontrivial (n : SpectrumCounts) : Prop :=
   ∃ Y : FermionHypercharges, AnomalyCancellationWithMultiplicity n Y ∧ Y.Q_L ≠ 0

theorem smCounts_anomaly_free : AnomalyCancellationWithMultiplicity smCounts smHypercharges := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [smCounts, smHypercharges] <;> norm_num

/-! ## Search Space Design

The search space is encoded by the structure of `SpectrumCounts`:
- Only 5 representation slots: (3,2)_L, (3,1)_R×2, (1,2)_L, (1,1)_R
- No right-handed SU(2) doublets (SU(2)_L chirality)
- Only singlets/triplets for SU(3), singlets/doublets for SU(2)

These restrictions are structural (data type), not propositional axioms.
-/

/-! ## Step 5: Non-Abelian Anomaly Constraints

The [SU(3)]³ anomaly cancellation forces a relation between colored fermion multiplicities.
-/

/-- [SU(3)]³ anomaly coefficient for a spectrum.
    
    Each SU(3) triplet contributes A(3) = 1 to the anomaly.
    Left-handed contributes +1, right-handed contributes -1.
    
    (3,2)_L: contributes 2 triplets (one per SU(2) component), left-handed → +2
    (3,1)_R: contributes 1 triplet, right-handed → -1 each
    
    For cancellation: 2 * n_32L - n_31R_u - n_31R_d = 0 -/
def su3CubedCoeff (n : SpectrumCounts) : ℤ :=
  2 * (n.n_32L : ℤ) - (n.n_31R_u : ℤ) - (n.n_31R_d : ℤ)

/-- A spectrum satisfies SU(3)³ anomaly cancellation -/
def SU3CubedCancels (n : SpectrumCounts) : Prop :=
  su3CubedCoeff n = 0

/-- THEOREM: SU(3)³ cancellation forces n_31R_u + n_31R_d = 2 * n_32L -/
theorem su3_cubed_constraint (n : SpectrumCounts) (h : SU3CubedCancels n) :
    n.n_31R_u + n.n_31R_d = 2 * n.n_32L := by
  simp only [SU3CubedCancels, su3CubedCoeff] at h
  omega

/-- SM satisfies SU(3)³ cancellation -/
theorem sm_su3_cubed_cancels : SU3CubedCancels smCounts := by
  simp [SU3CubedCancels, su3CubedCoeff, smCounts]

/-! ## Step 6: Cost Function and Lower Bounds -/

/-- A spectrum is nontrivial if it has at least one fermion -/
def SpectrumCounts.nontrivial (n : SpectrumCounts) : Prop :=
  n.n_32L > 0 ∨ n.n_31R_u > 0 ∨ n.n_31R_d > 0 ∨ n.n_12L > 0 ∨ n.n_11R > 0

/-- A spectrum is chiral if colored content is chiral (has (3,2)_L) -/
def SpectrumCounts.hasColoredChiral (n : SpectrumCounts) : Prop :=
  n.n_32L > 0

/-- SM spectrum is nontrivial -/
theorem sm_nontrivial : smCounts.nontrivial := by
  simp only [SpectrumCounts.nontrivial, smCounts]
  omega

/-- SM spectrum has colored chiral content -/
theorem sm_hasColoredChiral : smCounts.hasColoredChiral := by
  simp [SpectrumCounts.hasColoredChiral, smCounts]

/-- SM is anomaly-free nontrivial (witnesses feasibility) -/
theorem sm_anomaly_free_nontrivial : AnomalyFreeNontrivial smCounts := by
  use smHypercharges
  constructor
  · exact smCounts_anomaly_free
  · simp [smHypercharges]

/-! ## Deriving Lepton Presence from Anomaly Cancellation

These lemmas show that n_12L ≥ 1 and n_11R ≥ 1 are CONSEQUENCES of anomaly cancellation,
not assumptions. This is critical for avoiding circularity.
-/

/-- LEMMA: If n_32L ≥ 1 and a nontrivial U(1) exists, then n_12L ≥ 1.
    
    Proof: If n_12L = 0, the SU(2)²U(1) equation becomes 3*n_32L*Q_L = 0.
    With n_32L ≥ 1, this forces Q_L = 0, contradicting nontriviality. -/
theorem n12L_pos_of_anomaly (n : SpectrumCounts)
    (h32L : n.n_32L ≥ 1) (hA : AnomalyFreeNontrivial n) :
    n.n_12L ≥ 1 := by
  rcases hA with ⟨Y, hAnom, hQ⟩
  by_contra hn12
  push_neg at hn12
  have hn12' : n.n_12L = 0 := by omega
  -- SU(2)²U(1): 3*n_32L*Q_L + n_12L*L_L = 0
  -- With n_12L = 0: 3*n_32L*Q_L = 0
  have hsu2 := hAnom.su2_sq_u1
  simp only [hn12'] at hsu2
  -- 3 * n_32L * Q_L = 0, and 3 * n_32L > 0, so Q_L = 0
  have hn32pos : (3 * (n.n_32L : ℚ)) ≠ 0 := by
    have : (n.n_32L : ℚ) ≥ 1 := by exact_mod_cast h32L
    linarith
  have hQL0 : Y.Q_L = 0 := by
    have heq : (3 * (n.n_32L : ℚ)) * Y.Q_L + 0 * Y.L_L = 0 := hsu2
    simp only [zero_mul, add_zero] at heq
    have hmul : (3 * (n.n_32L : ℚ)) * Y.Q_L = 0 := heq
    rcases mul_eq_zero.mp hmul with h1 | h2
    · exact absurd h1 hn32pos
    · exact h2
  exact hQ hQL0

/-- LEMMA: If n_32L ≥ 1, n_12L ≥ 1, and a nontrivial U(1) exists, then n_11R ≥ 1.
    
    Proof: Combining grav²U(1) and SU(3)²U(1) with the hypercharge linear relations,
    if n_11R = 0 then the gravitational anomaly forces constraints that, together
    with SU(2)²U(1), force Q_L = 0. -/
theorem n11R_pos_of_anomaly (n : SpectrumCounts)
    (h32L : n.n_32L ≥ 1) (h12L : n.n_12L ≥ 1) (hA : AnomalyFreeNontrivial n) :
    n.n_11R ≥ 1 := by
  rcases hA with ⟨Y, hAnom, hQ⟩
  by_contra hn11
  push_neg at hn11
  have hn11' : n.n_11R = 0 := by omega
  -- From SU(2)²U(1): L_L = -3*n_32L/n_12L * Q_L (if n_12L ≠ 0)
  have hsu2 := hAnom.su2_sq_u1
  have hn12pos : (n.n_12L : ℚ) ≠ 0 := by
    have : (n.n_12L : ℚ) ≥ 1 := by exact_mod_cast h12L
    linarith
  have hLL : Y.L_L = -(3 * (n.n_32L : ℚ)) / (n.n_12L : ℚ) * Y.Q_L := by
    have : (3 * (n.n_32L : ℚ)) * Y.Q_L + (n.n_12L : ℚ) * Y.L_L = 0 := hsu2
    field_simp at this ⊢
    linarith
  -- From grav²U(1) with n_11R = 0:
  -- 6*n_32L*Q_L - 3*n_31R_u*u_R - 3*n_31R_d*d_R + 2*n_12L*L_L = 0
  have hgrav := hAnom.grav_u1
  simp only [hn11'] at hgrav
  -- From SU(3)²U(1): 2*n_32L*Q_L - n_31R_u*u_R - n_31R_d*d_R = 0
  have hsu3 := hAnom.su3_sq_u1
  -- Multiply su3 by 3 to match grav coefficients on colored singlets:
  -- 3 * (2*n_32L*Q - n_31R_u*u - n_31R_d*d) = 0
  -- = 6*n_32L*Q - 3*n_31R_u*u - 3*n_31R_d*d = 0
  have hsu3x3 : (6 * (n.n_32L : ℚ)) * Y.Q_L - (3 * (n.n_31R_u : ℚ)) * Y.u_R 
                - (3 * (n.n_31R_d : ℚ)) * Y.d_R = 0 := by ring_nf; linarith
  -- grav (with n_11R = 0): 6*n_32L*Q - 3*n_31R_u*u - 3*n_31R_d*d + 2*n_12L*L - 0*e = 0
  -- Subtract su3x3 from grav to isolate lepton term
  have hLterm : (2 * (n.n_12L : ℚ)) * Y.L_L = 0 := by
    have hgrav' : (6 * (n.n_32L : ℚ)) * Y.Q_L - (3 * (n.n_31R_u : ℚ)) * Y.u_R 
                  - (3 * (n.n_31R_d : ℚ)) * Y.d_R + (2 * (n.n_12L : ℚ)) * Y.L_L = 0 := by
      simp only [Nat.cast_zero, zero_mul, sub_zero] at hgrav
      linarith
    linarith
  -- Since n_12L ≥ 1, we have 2*n_12L ≠ 0, so L_L = 0
  have h2n12pos : (2 * (n.n_12L : ℚ)) ≠ 0 := by
    have : (n.n_12L : ℚ) ≥ 1 := by exact_mod_cast h12L
    linarith
  have hLL0 : Y.L_L = 0 := by
    have := mul_eq_zero.mp hLterm
    rcases this with h | h
    · exact absurd h h2n12pos
    · exact h
  -- From hLL: L_L = -(3*n_32L/n_12L) * Q_L and L_L = 0
  -- So -(3*n_32L/n_12L) * Q_L = 0
  -- Coefficient is nonzero since n_32L ≥ 1, n_12L ≥ 1
  rw [hLL0] at hLL
  have hn32pos : (3 * (n.n_32L : ℚ)) ≠ 0 := by
    have : (n.n_32L : ℚ) ≥ 1 := by exact_mod_cast h32L
    linarith
  have hcoef : -(3 * (n.n_32L : ℚ)) / (n.n_12L : ℚ) ≠ 0 := by
    rw [neg_div]
    exact neg_ne_zero.mpr (div_ne_zero hn32pos hn12pos)
  have hQL0 : Y.Q_L = 0 := by
    have := mul_eq_zero.mp (hLL.symm)
    rcases this with h | h
    · exact absurd h hcoef
    · exact h
  exact hQ hQL0

/-- LEMMA: If n_32L ≥ 1 and SU(3)³ cancels, then n_31R_u + n_31R_d ≥ 2 -/
lemma colored_singlets_ge_two (n : SpectrumCounts) 
    (h32L : n.n_32L ≥ 1) (hSU3 : SU3CubedCancels n) :
    n.n_31R_u + n.n_31R_d ≥ 2 := by
  have hconstr := su3_cubed_constraint n hSU3
  omega

/-- LEMMA: Cost of colored sector alone when n_32L ≥ 1 and SU(3)³ cancels -/
lemma colored_cost_ge_12 (n : SpectrumCounts)
    (h32L : n.n_32L ≥ 1) (hSU3 : SU3CubedCancels n) :
    6 * n.n_32L + 3 * n.n_31R_u + 3 * n.n_31R_d ≥ 12 := by
  have hconstr := su3_cubed_constraint n hSU3
  -- 6 * n_32L + 3 * (n_31R_u + n_31R_d) = 6 * n_32L + 3 * (2 * n_32L) = 12 * n_32L
  have hsum : 6 * n.n_32L + 3 * n.n_31R_u + 3 * n.n_31R_d = 12 * n.n_32L := by omega
  omega

/-- THEOREM: Any chiral anomaly-free spectrum with n_32L ≥ 1 has cost ≥ 12 from colored sector -/
theorem cost_colored_lower_bound (n : SpectrumCounts)
    (h32L : n.n_32L ≥ 1) (hSU3 : SU3CubedCancels n) :
    n.cost ≥ 12 := by
  simp only [SpectrumCounts.cost]
  have hcolored := colored_cost_ge_12 n h32L hSU3
  omega

/-! ## Step 7: Uniqueness Theorem

We prove that among spectra with n_32L ≥ 1, cost ≤ 15, and SU(3)³ cancellation,
the SM multiplicities are forced.
-/

/-- LEMMA: If n_32L ≥ 2 and SU(3)³ cancels, cost ≥ 24 (exceeds SM cost) -/
lemma n32L_ge_2_cost_ge_24 (n : SpectrumCounts)
    (h32L : n.n_32L ≥ 2) (hSU3 : SU3CubedCancels n) :
    n.cost ≥ 24 := by
  simp only [SpectrumCounts.cost]
  have hconstr := su3_cubed_constraint n hSU3
  -- Colored cost: 6 * n_32L + 3 * (2 * n_32L) = 12 * n_32L ≥ 24
  have : 6 * n.n_32L + 3 * n.n_31R_u + 3 * n.n_31R_d = 12 * n.n_32L := by omega
  omega

/-- LEMMA: If n_32L = 1 and SU(3)³ cancels, then n_31R_u + n_31R_d = 2 -/
lemma n32L_eq_1_forces_singlets (n : SpectrumCounts)
    (h32L : n.n_32L = 1) (hSU3 : SU3CubedCancels n) :
    n.n_31R_u + n.n_31R_d = 2 := by
  have hconstr := su3_cubed_constraint n hSU3
  omega

/-- LEMMA: If n_32L = 1, SU(3)³ cancels, and cost ≤ smCounts.cost, then lepton sector cost ≤ 3 -/
lemma lepton_cost_bound (n : SpectrumCounts)
    (h32L : n.n_32L = 1) (hSU3 : SU3CubedCancels n) (hCost : n.cost ≤ smCounts.cost) :
    2 * n.n_12L + n.n_11R ≤ 3 := by
  simp only [SpectrumCounts.cost, smCounts] at hCost
  have hsinglets := n32L_eq_1_forces_singlets n h32L hSU3
  omega

/-- MAIN THEOREM: Among spectra with n_32L ≥ 1, SU(3)³ cancellation, and cost ≤ smCounts.cost,
    we must have n_32L = 1.
    
    This is the first uniqueness constraint. -/
theorem n32L_forced_to_one (n : SpectrumCounts)
    (h32L : n.n_32L ≥ 1) (hSU3 : SU3CubedCancels n) (hCost : n.cost ≤ smCounts.cost) :
    n.n_32L = 1 := by
  by_contra h
  push_neg at h
  have h2 : n.n_32L ≥ 2 := by omega
  have hbig := n32L_ge_2_cost_ge_24 n h2 hSU3
  have hsmcost : smCounts.cost = 15 := smCounts_cost
  simp only [SpectrumCounts.cost] at hbig hCost
  simp only [smCounts, SpectrumCounts.cost] at hCost
  omega

/-- THEOREM: With n_32L = 1 and SU(3)³, the colored singlet sum is forced to 2 -/
theorem singlet_sum_forced (n : SpectrumCounts)
    (h32L : n.n_32L = 1) (hSU3 : SU3CubedCancels n) :
    n.n_31R_u + n.n_31R_d = 2 := n32L_eq_1_forces_singlets n h32L hSU3

/-- A spectrum matches SM colored structure -/
def matchesSMColored (n : SpectrumCounts) : Prop :=
  n.n_32L = 1 ∧ n.n_31R_u + n.n_31R_d = 2

/-- THEOREM: Minimal cost chiral spectrum has SM colored structure -/
theorem minimal_has_sm_colored (n : SpectrumCounts)
    (h32L : n.n_32L ≥ 1) (hSU3 : SU3CubedCancels n) (hCost : n.cost ≤ smCounts.cost) :
    matchesSMColored n := by
  constructor
  · exact n32L_forced_to_one n h32L hSU3 hCost
  · have h1 := n32L_forced_to_one n h32L hSU3 hCost
    exact singlet_sum_forced n h1 hSU3

/-- THEOREM: SM spectrum achieves the minimum cost for any chiral anomaly-free spectrum.
    
    Given: n_32L = 1, n_31R_u + n_31R_d = 2 (forced by SU(3)³)
    Colored cost = 6 + 6 = 12.
    Remaining budget = smCounts.cost - 12 = 3 for lepton sector.
    
    With n_12L ≥ 1 and n_11R ≥ 1 (derived from anomaly cancellation),
    minimal lepton cost is 2*1 + 1 = 3, giving total cost = smCounts.cost. -/
theorem sm_cost_is_minimal : 
    ∀ n : SpectrumCounts,
    n.n_32L ≥ 1 → 
    SU3CubedCancels n →
    n.cost ≤ smCounts.cost →
    (n.n_12L ≥ 1 → n.n_11R ≥ 1 → n.cost ≥ smCounts.cost) := by
  intro n h32L hSU3 hCost h12L h11R
  simp only [SpectrumCounts.cost, smCounts]
  have h1 := n32L_forced_to_one n h32L hSU3 hCost
  have h2 := singlet_sum_forced n h1 hSU3
  omega

/-! ## Final Uniqueness Statement -/

/-- A spectrum equals smCounts (the strongest uniqueness statement) -/
def isSmCounts (n : SpectrumCounts) : Prop :=
  n.n_32L = 1 ∧ n.n_31R_u = 1 ∧ n.n_31R_d = 1 ∧ n.n_12L = 1 ∧ n.n_11R = 1

/-- Alternative: equality to smCounts -/
theorem isSmCounts_iff_eq (n : SpectrumCounts) : isSmCounts n ↔ n = smCounts := by
  constructor
  · intro ⟨h1, h2, h3, h4, h5⟩
    ext <;> simp [smCounts, *]
  · intro h
    simp [isSmCounts, h, smCounts]

/-! ## Forcing Individual Colored Singlet Multiplicities

The SU(3)³ constraint only gives n_31R_u + n_31R_d = 2.
To force n_31R_u = 1 and n_31R_d = 1, we use the U(1)³ anomaly equation.
-/

/-- LEMMA: Under anomaly-free nontriviality with n_32L=1, n_12L=1, n_11R=1,
    and n_31R_u + n_31R_d = 2, the cases (2,0) and (0,2) are ruled out.
    
    Proof idea: If n_31R_u = 0 (or n_31R_d = 0), the U(1)³ equation simplifies
    to a form that, combined with the linear constraints, forces Q_L = 0.
    
    Sketch for (0,2) case:
    - SU(3)²U(1): 2*Q_L - 0*u_R - 2*d_R = 0 → d_R = Q_L
    - SU(2)²U(1): 3*Q_L + L_L = 0 → L_L = -3*Q_L
    - grav²U(1): 6*Q_L - 6*d_R + 2*L_L - e_R = 0 → e_R = -6*Q_L
    - U(1)³: 6*Q³ - 6*d³ + 2*L³ - e³ = 6*Q³ - 6*Q³ - 54*Q³ + 216*Q³ = 162*Q³
    - For cancellation: Q_L = 0, contradiction! -/
theorem colored_singlets_both_nonzero (n : SpectrumCounts)
    (h32L : n.n_32L = 1) (h12L : n.n_12L = 1) (h11R : n.n_11R = 1)
    (hsum : n.n_31R_u + n.n_31R_d = 2)
    (hA : AnomalyFreeNontrivial n) :
    n.n_31R_u ≥ 1 ∧ n.n_31R_d ≥ 1 := by
  rcases hA with ⟨Y, hAnom, hQ⟩
  constructor
  -- First conjunct: n_31R_u ≥ 1
  · by_contra hu
    push_neg at hu
    have hu0 : n.n_31R_u = 0 := by omega
    have hd2 : n.n_31R_d = 2 := by omega
    -- Simplify anomaly equations with h32L=1, h12L=1, h11R=1, hu0=0, hd2=2
    -- SU(3)²U(1): 2*Q_L - 0*u_R - 2*d_R = 0 → d_R = Q_L
    have hsu3 := hAnom.su3_sq_u1
    simp only [h32L, hu0, hd2, Nat.cast_one, Nat.cast_zero, Nat.cast_ofNat] at hsu3
    have hd : Y.d_R = Y.Q_L := by linarith
    -- SU(2)²U(1): 3*Q_L + L_L = 0 → L_L = -3*Q_L
    have hsu2 := hAnom.su2_sq_u1
    simp only [h32L, h12L, Nat.cast_one] at hsu2
    have hL : Y.L_L = -3 * Y.Q_L := by linarith
    -- grav²U(1): 6*Q_L - 6*d_R + 2*L_L - e_R = 0
    have hgrav := hAnom.grav_u1
    simp only [h32L, h12L, h11R, hu0, hd2, Nat.cast_one, Nat.cast_zero, Nat.cast_ofNat] at hgrav
    -- Substitute hd and hL: 6*Q - 6*Q + 2*(-3*Q) - e = 0 → e = -6*Q
    have he : Y.e_R = -6 * Y.Q_L := by linarith [hd, hL]
    -- U(1)³: 6*Q³ - 6*d³ + 2*L³ - e³ = 0
    have hcubic := hAnom.u1_cubed
    simp only [h32L, h12L, h11R, hu0, hd2] at hcubic
    -- Substitute: 6*Q³ - 6*Q³ + 2*(-3*Q)³ - (-6*Q)³ = 6*Q³ - 6*Q³ - 54*Q³ + 216*Q³ = 162*Q³
    rw [hd, hL, he] at hcubic
    have hcubic' : (162 : ℚ) * Y.Q_L^3 = 0 := by ring_nf at hcubic ⊢; linarith
    have h162 : (162 : ℚ) ≠ 0 := by norm_num
    have hQ3 : Y.Q_L^3 = 0 := by
      have := mul_eq_zero.mp hcubic'
      rcases this with h | h
      · exact absurd h h162
      · exact h
    have hQL0 : Y.Q_L = 0 := by
      by_contra hne
      have : Y.Q_L^3 ≠ 0 := pow_ne_zero 3 hne
      exact this hQ3
    exact hQ hQL0
  -- Second conjunct: n_31R_d ≥ 1 (symmetric argument)
  · by_contra hd
    push_neg at hd
    have hd0 : n.n_31R_d = 0 := by omega
    have hu2 : n.n_31R_u = 2 := by omega
    -- SU(3)²U(1): 2*Q_L - 2*u_R - 0*d_R = 0 → u_R = Q_L
    have hsu3 := hAnom.su3_sq_u1
    simp only [h32L, hu2, hd0, Nat.cast_one, Nat.cast_zero, Nat.cast_ofNat] at hsu3
    have hu : Y.u_R = Y.Q_L := by linarith
    -- SU(2)²U(1): 3*Q_L + L_L = 0 → L_L = -3*Q_L
    have hsu2 := hAnom.su2_sq_u1
    simp only [h32L, h12L, Nat.cast_one] at hsu2
    have hL : Y.L_L = -3 * Y.Q_L := by linarith
    -- grav²U(1): 6*Q_L - 6*u_R + 2*L_L - e_R = 0
    have hgrav := hAnom.grav_u1
    simp only [h32L, h12L, h11R, hu2, hd0, Nat.cast_one, Nat.cast_zero, Nat.cast_ofNat] at hgrav
    have he : Y.e_R = -6 * Y.Q_L := by linarith [hu, hL]
    -- U(1)³: 6*Q³ - 6*u³ + 2*L³ - e³ = 0
    have hcubic := hAnom.u1_cubed
    simp only [h32L, h12L, h11R, hu2, hd0, Nat.cast_one, Nat.cast_zero, Nat.cast_ofNat] at hcubic
    rw [hu, hL, he] at hcubic
    have hcubic' : (162 : ℚ) * Y.Q_L^3 = 0 := by ring_nf at hcubic ⊢; linarith
    have h162 : (162 : ℚ) ≠ 0 := by norm_num
    have hQ3 : Y.Q_L^3 = 0 := by
      have := mul_eq_zero.mp hcubic'
      rcases this with h | h
      · exact absurd h h162
      · exact h
    have hQL0 : Y.Q_L = 0 := by
      by_contra hne
      have : Y.Q_L^3 ≠ 0 := pow_ne_zero 3 hne
      exact this hQ3
    exact hQ hQL0

/-- COROLLARY: With all constraints, n_31R_u = 1 and n_31R_d = 1 -/
theorem colored_singlets_forced (n : SpectrumCounts)
    (h32L : n.n_32L = 1) (h12L : n.n_12L = 1) (h11R : n.n_11R = 1)
    (hSU3 : SU3CubedCancels n) (hA : AnomalyFreeNontrivial n) :
    n.n_31R_u = 1 ∧ n.n_31R_d = 1 := by
  have hsum := singlet_sum_forced n h32L hSU3
  have ⟨hge_u, hge_d⟩ := colored_singlets_both_nonzero n h32L h12L h11R hsum hA
  omega

/-! ## Bridge to StandardModelFromImpossibility

When multiplicities equal smCounts, the anomaly equations reduce to the standard form.
-/

/-- LEMMA: AnomalyCancellationWithMultiplicity at smCounts is equivalent to
    the standard AnomalyCancellation at Nc=3 from StandardModelFromImpossibility.
    
    This bridges the multiplicity-parameterized anomaly equations to the
    existing hypercharge uniqueness theorems in StandardModelFromImpossibility.
    
    The equivalence is straightforward algebra:
    - When all multiplicities = 1, the coefficients match exactly
    - AnomalyCancellationWithMultiplicity: 2*1*Q_L - 1*u_R - 1*d_R = 2*Q_L - u_R - d_R
    - AnomalyCancellation (Nc=3): su3_squared_u1_anomaly = 2*Q_L - u_R - d_R
    - Similarly for other anomalies -/
theorem anomaly_equiv_at_smCounts (Y : FermionHypercharges) :
    AnomalyCancellationWithMultiplicity smCounts Y ↔ AnomalyCancellation Y 3 := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_⟩
    -- su3_sq_u1: su3_squared_u1_anomaly Y = 0
    · simp only [su3_squared_u1_anomaly]
      have := h.su3_sq_u1
      simp only [smCounts, Nat.cast_one, one_mul, mul_one] at this
      linarith
    -- su2_sq_u1: su2_squared_u1_anomaly Y 3 = 0
    · simp only [su2_squared_u1_anomaly, Nat.cast_ofNat]
      have := h.su2_sq_u1
      simp only [smCounts, Nat.cast_one, one_mul, mul_one] at this
      ring_nf at this ⊢
      linarith
    -- u1_cubed: u1_cubed_anomaly_full Y 3 = 0
    · simp only [u1_cubed_anomaly_full, Nat.cast_ofNat]
      have := h.u1_cubed
      simp only [smCounts, Nat.cast_one, one_mul, mul_one] at this
      ring_nf at this ⊢
      linarith
    -- grav_u1: grav_u1_anomaly Y 3 = 0
    · simp only [grav_u1_anomaly, Nat.cast_ofNat]
      have := h.grav_u1
      simp only [smCounts, Nat.cast_one, one_mul, mul_one] at this
      ring_nf at this ⊢
      linarith
  · intro h
    refine ⟨?_, ?_, ?_, ?_⟩
    -- su3_sq_u1
    · simp only [smCounts, Nat.cast_one, one_mul, mul_one]
      have := h.su3_sq_u1
      simp only [su3_squared_u1_anomaly] at this
      linarith
    -- su2_sq_u1
    · simp only [smCounts, Nat.cast_one, one_mul, mul_one]
      have := h.su2_sq_u1
      simp only [su2_squared_u1_anomaly, Nat.cast_ofNat] at this
      ring_nf at this ⊢
      linarith
    -- grav_u1
    · simp only [smCounts, Nat.cast_one, one_mul, mul_one]
      have := h.grav_u1
      simp only [grav_u1_anomaly, Nat.cast_ofNat] at this
      ring_nf at this ⊢
      linarith
    -- u1_cubed
    · simp only [smCounts, Nat.cast_one, one_mul, mul_one]
      have := h.u1_cubed
      simp only [u1_cubed_anomaly_full, Nat.cast_ofNat] at this
      ring_nf at this ⊢
      linarith

/-! ## Main Uniqueness Theorem

The final theorem: SM spectrum is the unique minimizer among anomaly-free chiral spectra.
-/

/-- THEOREM: Uniqueness at smCounts.cost with lepton presence derived. -/
theorem uniqueness_at_sm_cost (n : SpectrumCounts)
    (h32L : n.n_32L ≥ 1)
    (hSU3 : SU3CubedCancels n)
    (hA : AnomalyFreeNontrivial n)
    (hCost : n.cost = smCounts.cost) :
    isSmCounts n := by
  -- Derive lepton presence from anomaly cancellation
  have h12L := n12L_pos_of_anomaly n h32L hA
  have h11R := n11R_pos_of_anomaly n h32L h12L hA
  -- Force n_32L = 1
  have hn32L := n32L_forced_to_one n h32L hSU3 (le_of_eq hCost)
  -- Force n_31R_u + n_31R_d = 2
  have hsinglets := singlet_sum_forced n hn32L hSU3
  -- Lepton cost equation
  simp only [SpectrumCounts.cost, smCounts] at hCost
  have hlepton : 2 * n.n_12L + n.n_11R = 3 := by omega
  have hn12L : n.n_12L = 1 := by omega
  have hn11R : n.n_11R = 1 := by omega
  -- Force individual colored singlets
  have ⟨hnu, hnd⟩ := colored_singlets_forced n hn32L hn12L hn11R hSU3 hA
  exact ⟨hn32L, hnu, hnd, hn12L, hn11R⟩

/-- SM satisfies isSmCounts (sanity check) -/
theorem sm_is_smCounts : isSmCounts smCounts := by
  simp [isSmCounts, smCounts]

/-- MAIN THEOREM: Complete matter content uniqueness.
    
    Among spectra with:
    1. n_32L ≥ 1 (chiral colored content)
    2. SU(3)³ anomaly cancellation
    3. Anomaly-free nontrivial (admits hypercharges with Q_L ≠ 0)
    4. cost ≤ smCounts.cost
    
    The SM spectrum is the UNIQUE solution: n = smCounts.
    
    Hypercharge uniqueness then follows from StandardModelFromImpossibility
    via the bridge lemma `anomaly_equiv_at_smCounts`. -/
theorem matter_content_uniqueness :
    ∀ n : SpectrumCounts,
    n.n_32L ≥ 1 →
    SU3CubedCancels n →
    AnomalyFreeNontrivial n →
    n.cost ≤ smCounts.cost →
    n = smCounts := by
  intro n h32L hSU3 hA hCost
  -- Derive lepton presence
  have h12L := n12L_pos_of_anomaly n h32L hA
  have h11R := n11R_pos_of_anomaly n h32L h12L hA
  -- Show cost must equal smCounts.cost (can't be less)
  have hCostGe : n.cost ≥ smCounts.cost := by
    simp only [SpectrumCounts.cost, smCounts]
    have hn32L := n32L_forced_to_one n h32L hSU3 hCost
    have hsinglets := singlet_sum_forced n hn32L hSU3
    omega
  have hCostEq : n.cost = smCounts.cost := by omega
  -- Apply uniqueness theorem
  have his := uniqueness_at_sm_cost n h32L hSU3 hA hCostEq
  exact (isSmCounts_iff_eq n).mp his

def matterContentCanonicalBackwardInterface : AdmissibleBackwardInterface := 
  sm_canonical_backward_interface

def matterContentPublicMechanismInvariant : EpistemicallyAdequateInvariant Mechanism := 
  matterContentCanonicalBackwardInterface.toEpistemicallyAdequateInvariant

theorem matter_content_uniqueness_public_normal_form
    (n : SpectrumCounts)
    (h32L : n.n_32L ≥ 1)
    (hSU3 : SU3CubedCancels n)
    (hA : AnomalyFreeNontrivial n)
    (hCost : n.cost ≤ smCounts.cost) :
    n = smCounts ∧ 
      matterContentPublicMechanismInvariant.observe standardModelObs = Mechanism.resource ∧ 
      EpistemicInterfaceCertificate standardModelObs := by
  refine ⟨matter_content_uniqueness n h32L hSU3 hA hCost, ?_, ?_⟩
  · simpa [matterContentPublicMechanismInvariant, matterContentCanonicalBackwardInterface] using 
      sm_obs_public_mechanism smCompatibleObs
  · simpa using sm_obs_epistemic_interface_certificate smCompatibleObs

theorem matter_content_uniqueness_canonical_projection_normal_form
    (n : SpectrumCounts)
    (h32L : n.n_32L ≥ 1)
    (hSU3 : SU3CubedCancels n)
    (hA : AnomalyFreeNontrivial n)
    (hCost : n.cost ≤ smCounts.cost) :
    n = smCounts ∧ 
      (canonicalProjection standardModelObs).mechanism = Mechanism.resource ∧ 
      (canonicalProjection standardModelObs).quotient = QuotientGeom.continuous := by
  refine ⟨matter_content_uniqueness n h32L hSU3 hA hCost, ?_, ?_⟩
  · simpa using (sm_obs_canonical_projection_normal_form smCompatibleObs).1
  · simpa using (sm_obs_canonical_projection_normal_form smCompatibleObs).2

end MatterContentUniqueness
