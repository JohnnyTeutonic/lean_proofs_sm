/-
Minimal covariance matrix test for DESI cosmology ellipse
-/
import Mathlib.Algebra.Lie.CartanMatrix

namespace CovMatrixTest

/-- 2x2 covariance matrix -/
structure Cov2x2 where
  var_w0 : Rat
  var_wa : Rat
  cov_01 : Rat
  deriving Repr

/-- Determinant -/
def Cov2x2.det (C : Cov2x2) : Rat :=
  C.var_w0 * C.var_wa - C.cov_01 * C.cov_01

/-- Posterior with covariance -/
structure Posterior where
  w0 : Rat
  wa : Rat
  C : Cov2x2
  deriving Repr

/-- DESI Y1 + CMB + Pantheon+ -/
def DESI : Posterior := {
  w0 := -82/100
  wa := -75/100
  C := {
    var_w0 := 121/10000
    var_wa := 1521/10000
    cov_01 := -36465/1000000
  }
}

/-- Chi-squared from LCDM point (-1, 0) -/
def chi2 (p : Posterior) : Rat :=
  let dw0 := p.w0 + 1
  let dwa := p.wa
  let d := p.C.det
  (p.C.var_wa * dw0 * dw0 + p.C.var_w0 * dwa * dwa - 2 * p.C.cov_01 * dw0 * dwa) / d

/-- 68.3% threshold in 2D -/
def thresh68 : Rat := 230/100

/-- 95.4% threshold in 2D -/
def thresh95 : Rat := 618/100

/-- Check exclusion -/
def excluded (p : Posterior) (t : Rat) : Bool := chi2 p > t

#eval chi2 DESI
#eval excluded DESI thresh68
#eval excluded DESI thresh95

theorem LCDM_excluded_68 : excluded DESI thresh68 = true := by native_decide

theorem LCDM_not_excluded_95 : excluded DESI thresh95 = false := by native_decide

#eval s!"chi2 = {chi2 DESI}"
#eval s!"Excluded at 68% = {excluded DESI thresh68}"
#eval s!"Excluded at 95% = {excluded DESI thresh95}"

end CovMatrixTest
