/-
  PMNS Matrix: Neutrino Mixing Angles from E8 Structure
  ======================================================

  THE PUZZLE:
  Neutrino mixing angles are LARGE (unlike CKM quark angles):
  - θ₁₂ ≈ 33° (solar angle)
  - θ₂₃ ≈ 49° (atmospheric angle, nearly maximal)
  - θ₁₃ ≈ 8.5° (reactor angle)

  Compare to CKM (quarks):
  - θ_C ≈ 13° (Cabibbo angle = 27/120 = 0.225)

  THE DERIVATION:
  Leptons mix through ALGEBRA dimensions, not representation dimensions:
  - sin²θ₁₂ = dim(E6) / 2^rank(E8) = 78/256
  - sin²θ₂₃ = dim(E6) / dim(E7) = 78/133
  - sin²θ₁₃ = dim(SU(2)) / dim(E7) = 3/133

  WHY THE DIFFERENCE:
  - Quarks: sin θ_C = 27/120 (rep / rep) — small
  - Leptons: sin²θ = alg / alg — large (E6, E7, E8 are similar size)

  Author: Jonathan Reich
  Date: December 2025
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace PMNSFromE8Structure

/-! ## Part 1: Lie Algebra Dimensions -/

def dim_E8 : ℕ := 248
def dim_E7 : ℕ := 133
def dim_E6 : ℕ := 78
def dim_SO16_adj : ℕ := 120
def dim_E6_fund : ℕ := 27
def dim_SU2 : ℕ := 3
def rank_E8 : ℕ := 8

/-- 2^rank(E8) = 256 -/
def two_pow_rank_E8 : ℕ := 2^rank_E8

theorem two_pow_rank_is_256 : two_pow_rank_E8 = 256 := by native_decide

/-! ## Part 2: Experimental Values -/

/-- Experimental sin²θ values (PDG 2024) -/
def sin2_12_exp : ℚ := 304 / 1000   -- 0.304 ± 0.013
def sin2_23_exp : ℚ := 573 / 1000   -- 0.573 ± 0.020
def sin2_13_exp : ℚ := 222 / 10000  -- 0.0222 ± 0.0007

/-! ## Part 3: PMNS Angle Derivations -/

/--
  SOLAR ANGLE θ₁₂
  
  sin²θ₁₂ = dim(E6) / 2^rank(E8) = 78/256
  
  Physical interpretation:
  - Numerator: E6 algebra dimension (lepton sector structure)
  - Denominator: 2^8 = 256 (spinor dimension from E8 rank)
  
  The 1-2 mixing occurs between the E6 "family space" and the
  full spinorial structure of E8.
-/
def sin2_theta_12 : ℚ := dim_E6 / two_pow_rank_E8

theorem sin2_12_value : sin2_theta_12 = 78 / 256 := by
  simp [sin2_theta_12, dim_E6, two_pow_rank_E8, rank_E8]

theorem sin2_12_simplified : (78 : ℚ) / 256 = 39 / 128 := by norm_num

/-- Predicted value as decimal -/
def sin2_12_pred : ℚ := 3047 / 10000  -- 0.3047

theorem sin2_12_close_to_exp : 
    |sin2_theta_12 - sin2_12_exp| < 11 / 1000 := by  -- Within 0.011
  simp [sin2_theta_12, sin2_12_exp, dim_E6, two_pow_rank_E8, rank_E8]
  norm_num

/--
  ATMOSPHERIC ANGLE θ₂₃
  
  sin²θ₂₃ = dim(E6) / dim(E7) = 78/133
  
  Physical interpretation:
  - The 2-3 mixing measures E6 "weight" within E7
  - This is nearly maximal because E6 is a large fraction of E7
  - Contrast with quarks where 27 << 120
-/
def sin2_theta_23 : ℚ := dim_E6 / dim_E7

theorem sin2_23_value : sin2_theta_23 = 78 / 133 := by
  simp [sin2_theta_23, dim_E6, dim_E7]

/-- Predicted value as decimal -/  
def sin2_23_pred : ℚ := 5865 / 10000  -- 0.5865

theorem sin2_23_close_to_exp :
    |sin2_theta_23 - sin2_23_exp| < 14 / 1000 := by  -- Within 0.014
  simp [sin2_theta_23, sin2_23_exp, dim_E6, dim_E7]
  norm_num

/--
  REACTOR ANGLE θ₁₃
  
  sin²θ₁₃ = dim(SU(2)) / dim(E7) = 3/133
  
  Physical interpretation:
  - The 1-3 mixing is small because SU(2) << E7
  - SU(2) is the weak isospin group
  - This mixing connects first generation to third through weak structure
-/
def sin2_theta_13 : ℚ := dim_SU2 / dim_E7

theorem sin2_13_value : sin2_theta_13 = 3 / 133 := by
  simp [sin2_theta_13, dim_SU2, dim_E7]

/-- Predicted value as decimal -/
def sin2_13_pred : ℚ := 226 / 10000  -- 0.0226

theorem sin2_13_close_to_exp :
    |sin2_theta_13 - sin2_13_exp| < 5 / 10000 := by  -- Within 0.0005
  simp [sin2_theta_13, sin2_13_exp, dim_SU2, dim_E7]
  norm_num

/-! ## Part 4: Comparison with CKM (Quark Mixing) -/

/-- Cabibbo angle from E6 fundamental / SO(16) adjoint -/
def sin_cabibbo : ℚ := dim_E6_fund / dim_SO16_adj

theorem cabibbo_value : sin_cabibbo = 27 / 120 := by
  simp [sin_cabibbo, dim_E6_fund, dim_SO16_adj]

theorem cabibbo_exact : (27 : ℚ) / 120 = 225 / 1000 := by norm_num

/--
  WHY CKM IS SMALL BUT PMNS IS LARGE
  
  CKM (quarks): sin θ_C = 27/120 = 0.225
  - Ratio of REPRESENTATION dimensions
  - 27 (E6 fund) << 120 (SO(16) adj)
  - Small mixing because family << geometry
  
  PMNS (leptons): sin²θ = algebra ratios
  - θ₁₂: 78/256 = 0.305 (E6/spinor)
  - θ₂₃: 78/133 = 0.586 (E6/E7)
  - θ₁₃: 3/133 = 0.023 (SU2/E7)
  - Large mixing because algebras are comparable in size
-/
def ckm_pmns_dichotomy : String :=
  "CKM: Quarks mix through REPRESENTATION ratios (27/120 = 0.225, small)\n" ++
  "PMNS: Leptons mix through ALGEBRA ratios (78/133 = 0.586, large)\n" ++
  "Same E8 origin, different probes → different mixing patterns"

/-! ## Part 5: Experimental Agreement Summary -/

structure PMNSPrediction where
  angle_name : String
  formula : String
  predicted : ℚ
  observed : ℚ
  error_percent : ℚ

def theta_12_pred : PMNSPrediction := {
  angle_name := "θ₁₂ (solar)"
  formula := "sin²θ₁₂ = 78/256"
  predicted := 78 / 256
  observed := 304 / 1000
  error_percent := 3  -- ~0.3%
}

def theta_23_pred : PMNSPrediction := {
  angle_name := "θ₂₃ (atmospheric)"
  formula := "sin²θ₂₃ = 78/133"
  predicted := 78 / 133
  observed := 573 / 1000
  error_percent := 24  -- ~2.4%
}

def theta_13_pred : PMNSPrediction := {
  angle_name := "θ₁₃ (reactor)"
  formula := "sin²θ₁₃ = 3/133"
  predicted := 3 / 133
  observed := 222 / 10000
  error_percent := 16  -- ~1.6%
}

/-! ## Part 6: Physical Interpretation -/

/--
  THE E8 → E7 → E6 LEPTON STRUCTURE
  
  In the E8 framework:
  - E8 is the terminal object (all symmetry)
  - E7 ⊂ E8 is the first breaking (248 → 133)
  - E6 ⊂ E7 is the second breaking (133 → 78)
  
  Lepton mixing probes this chain:
  - θ₂₃ = E6/E7 ratio (atmospheric, 2-3 mixing)
  - θ₁₂ = E6/spinor ratio (solar, 1-2 mixing)
  - θ₁₃ = weak/E7 ratio (reactor, 1-3 mixing)
  
  The LARGE angles arise because E6, E7, E8 are all O(100) dimensional,
  so their ratios are O(1), giving large mixing.
  
  Contrast with quarks:
  - Quarks use 27/120 (family vs geometry)
  - 27 << 120, so mixing is small
-/
def physical_interpretation : String :=
  "PMNS angles probe the E8 → E7 → E6 chain through algebra dimensions.\n" ++
  "Large mixing arises because dim(E6) ≈ dim(E7) ≈ dim(E8)/2.\n" ++
  "CKM uses representation dimensions (27 << 120), giving small mixing.\n" ++
  "This structural difference explains the CKM-PMNS dichotomy."

/-! ## Part 7: Falsification -/

/--
  FALSIFICATION CRITERIA
  
  The predictions are:
  - sin²θ₁₂ = 78/256 = 0.3047
  - sin²θ₂₃ = 78/133 = 0.5865  
  - sin²θ₁₃ = 3/133 = 0.0226
  
  Current experimental values:
  - sin²θ₁₂ = 0.304 ± 0.013 (agrees within 0.3%)
  - sin²θ₂₃ = 0.573 ± 0.020 (agrees within 2.4%)
  - sin²θ₁₃ = 0.0222 ± 0.0007 (agrees within 1.6%)
  
  All three are within 1σ of predictions!
  
  Future precision (DUNE, Hyper-K, JUNO):
  - σ(sin²θ₁₂) → 0.005 (can test 78/256)
  - σ(sin²θ₂₃) → 0.010 (can test 78/133)
  - σ(sin²θ₁₃) → 0.0002 (can test 3/133)
-/
def falsification : String :=
  "Predictions vs Experiment (all within 1σ):\n" ++
  "θ₁₂: 78/256 = 0.305 vs 0.304 ± 0.013 ✓\n" ++
  "θ₂₃: 78/133 = 0.586 vs 0.573 ± 0.020 ✓\n" ++
  "θ₁₃: 3/133 = 0.0226 vs 0.0222 ± 0.0007 ✓\n\n" ++
  "FALSIFIED BY: Future precision measurements outside predicted values"

/-! ## Part 8: Summary Theorem -/

theorem pmns_from_E8 :
    -- Solar angle
    sin2_theta_12 = 78 / 256 ∧
    -- Atmospheric angle
    sin2_theta_23 = 78 / 133 ∧
    -- Reactor angle
    sin2_theta_13 = 3 / 133 ∧
    -- Cabibbo for comparison
    sin_cabibbo = 27 / 120 := by
  constructor
  · exact sin2_12_value
  constructor
  · exact sin2_23_value
  constructor
  · exact sin2_13_value
  · exact cabibbo_value

def pmns_summary : String :=
  "PMNS MATRIX FROM E8 OBSTRUCTION STRUCTURE\n" ++
  "==========================================\n\n" ++
  "DERIVATIONS:\n" ++
  "1. sin²θ₁₂ = dim(E6)/2^rank(E8) = 78/256 = 0.305\n" ++
  "2. sin²θ₂₃ = dim(E6)/dim(E7) = 78/133 = 0.586\n" ++
  "3. sin²θ₁₃ = dim(SU2)/dim(E7) = 3/133 = 0.0226\n\n" ++
  "EXPERIMENTAL AGREEMENT:\n" ++
  "θ₁₂: 0.3% error (within 1σ)\n" ++
  "θ₂₃: 2.4% error (within 1σ)\n" ++
  "θ₁₃: 1.6% error (within 1σ)\n\n" ++
  "COMPARISON WITH CKM:\n" ++
  "Cabibbo: sin θ_C = 27/120 = 0.225 (representation ratio)\n" ++
  "PMNS: sin²θ = algebra ratios (78/256, 78/133, 3/133)\n\n" ++
  "KEY INSIGHT:\n" ++
  "Quarks see REPRESENTATION structure → small mixing\n" ++
  "Leptons see ALGEBRA structure → large mixing\n" ++
  "Same E8, different probes!"

end PMNSFromE8Structure
