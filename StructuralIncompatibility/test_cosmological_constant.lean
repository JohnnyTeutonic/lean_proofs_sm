/-
Quick Test for CosmologicalConstant.lean
=========================================

This file tests the main theorems to ensure compilation succeeds.
Run: lake build test_cosmological_constant

Author: Jonathan Reich
Date: December 2025
-/

import StructuralIncompatibility.CosmologicalConstant
import Mathlib.Data.Real.Basic

namespace TestCosmologicalConstant

open CosmologicalConstant

/-! ## Test 1: Basic Structure -/

/-- Test: Can construct a PlanckObstruction -/
example : PlanckObstruction := example_planck_obstruction

/-- Test: Entropy calculation works -/
example : planck_obstruction_entropy example_planck_obstruction = 248 := 
  example_entropy

/-! ## Test 2: Main Theorems Typecheck -/

/-- Test: Main cosmological constant theorem typechecks -/
example (P : PlanckObstruction) : 
    ∃ κ : ℝ, κ > 0 ∧ Λ_obs / Λ_QFT = Real.exp (- κ * 248) :=
  cosmological_constant_from_planck_obstruction P

/-- Test: QG → E₈ → cosmological constant chain -/
example (H : QGTotalImpossibility) :
    ∃ κ : ℝ, κ > 0 ∧ Λ_obs / Λ_QFT = Real.exp (- κ * 248) :=
  cosmological_constant_from_QG_impossibility H

/-- Test: Complete theorem typechecks -/
example (H : QGTotalImpossibility) :
    (∃ κ : ℝ, κ > 0 ∧ Λ_obs / Λ_QFT = Real.exp (- κ * 248)) ∧
    abs (decimal_exponent Λ_obs Λ_QFT + 122) < 2 :=
  cosmological_constant_complete H

/-! ## Test 3: E₈ Dimension -/

/-- Test: E₈ dimension is 248 -/
example : E8_dimension = 248 := E8_dim_is_248

/-- Test: Planck obstruction with E₈ dimension has correct entropy -/
example (P : PlanckObstruction) (h : P.O.dim = E8_dimension) :
    obstruction_entropy P.O = 248 :=
  planck_obstruction_dim_248 P h

/-! ## Test 4: Construction from QG -/

/-- Test: Can construct PlanckObstruction from QG impossibility -/
example (H : QGTotalImpossibility) : PlanckObstruction :=
  PlanckObstruction.from_QG H

/-- Test: Constructed obstruction has correct structure -/
example (H : QGTotalImpossibility) :
    (PlanckObstruction.from_QG H).sym = H.forced_symmetry := rfl

/-! ## Test 5: Numerical Aspects -/

/-- Test: Decimal exponent function typechecks -/
example (x y : ℝ) : ℝ := decimal_exponent x y

/-- Test: Numerical verification theorem exists -/
example : abs (decimal_exponent Λ_obs Λ_QFT + 122) < 2 :=
  cosmological_constant_numerical_verification

/-! ## Summary -/

#check cosmological_constant_from_planck_obstruction
#check cosmological_constant_from_QG_impossibility  
#check cosmological_constant_complete
#check E8_dim_is_248
#check example_planck_obstruction

end TestCosmologicalConstant

/-
TEST STATUS
===========

All tests should compile successfully once lake build completes.

Tests verify:
✓ Structure construction
✓ Entropy calculations
✓ Main theorems typecheck
✓ E₈ dimension verification
✓ QG → cosmological constant chain
✓ Numerical verification framework

If this compiles cleanly, CosmologicalConstant.lean is ready!
-/
