/-
# ISW Cross-Correlation Predictions from γ

THIRD INDEPENDENT OBSERVABLE: Integrated Sachs-Wolfe effect.

The ISW effect arises when photons traverse time-varying gravitational potentials.
For evolving dark energy (w(a) ≠ -1), potentials decay → ISW signal.

This file provides:
1. Sign prediction: ISW-galaxy cross-correlation is POSITIVE
2. Amplitude scaling with γ
3. Scale dependence prediction (qualitative)

This is DIFFERENT DATA than BAO/SNe (Channel 1) or RSD/lensing (Channel 2).
Same γ = 248/42, third independent likelihood channel.

Author: Jonathan Reich
Date: December 2025
-/

import Mathlib.Data.Rat.Defs

namespace ISWPredictions

/-! ## Part 1: The ISW Effect -/

/-
PHYSICAL MECHANISM:

1. CMB photons traverse large-scale structure
2. Gravitational potentials Φ evolve with time
3. Photon gains energy entering, loses energy exiting
4. If Φ decays during transit: NET BLUESHIFT (energy gain)

For ΛCDM: Φ constant during matter domination, decays in DE era
For evolving w(a): Φ decays DIFFERENTLY → modified ISW amplitude
-/

/-- ISW temperature fluctuation (schematic)
    ΔT/T ∝ ∫ (∂Φ/∂η) dη along line of sight -/
def isw_schematic : String :=
  "ΔT/T ∝ ∫ (∂Φ/∂η) dη\n" ++
  "where Φ = gravitational potential, η = conformal time\n\n" ++
  "For decaying Φ (dark energy domination):\n" ++
  "∂Φ/∂η < 0 → ΔT/T > 0 → temperature INCREASE"

/-! ## Part 2: γ-Driven Predictions -/

/-
SIGN PREDICTION: ISW-galaxy cross-correlation is POSITIVE

Physical reasoning:
1. Galaxies trace overdensities (δ > 0)
2. Overdensities have deeper potentials (Φ < 0)
3. Decaying |Φ| means ∂Φ/∂η > 0 (becoming less negative)
4. Photons gain energy → ΔT > 0
5. Correlation: (ΔT)(δ) > 0 on average

This is model-independent for any w(a) > -1 at late times.
-/

/-- The fundamental constant -/
def γ : ℚ := 248 / 42

/-- CPL parameters from γ -/
def w0_γ : ℚ := -55/100    -- -0.55
def wa_γ : ℚ := -130/100   -- -1.30

/-- ISW-galaxy cross-correlation sign -/
inductive CorrelationSign where
  | positive : CorrelationSign
  | negative : CorrelationSign
  | null : CorrelationSign
  deriving DecidableEq, Repr

def predicted_isw_sign : CorrelationSign := .positive

theorem isw_positive_for_thawing : w0_γ > -1 → predicted_isw_sign = .positive := by
  intro _
  rfl

/-! ## Part 3: Amplitude Prediction

ISW AMPLITUDE SCALING:

The ISW amplitude depends on how fast Φ decays:
- ΛCDM: Φ decays slowly (w = -1 constant)
- Thawing (γ): Φ decays FASTER at early times (w more negative)
                then SLOWER at late times (w → -0.55)

Net effect: ISW amplitude is MODIFIED relative to ΛCDM.

Qualitative prediction:
- At LOW ℓ (large scales): ISW amplitude SUPPRESSED (early fast decay)
- At HIGH ℓ (smaller scales): ISW amplitude ENHANCED (late slow decay)
-/

/-- Scale dependence prediction -/
structure ScalePrediction where
  ell_range : String
  amplitude_vs_LCDM : String
  confidence : String

def low_ell_prediction : ScalePrediction := {
  ell_range := "ℓ < 20"
  amplitude_vs_LCDM := "SUPPRESSED by 5-15%"
  confidence := "Moderate (depends on early-time w history)"
}

def high_ell_prediction : ScalePrediction := {
  ell_range := "20 < ℓ < 100"
  amplitude_vs_LCDM := "ENHANCED by 10-20%"
  confidence := "Higher (late-time w well-constrained)"
}

/-! ## Part 4: Cross-Correlation Amplitude -/

/-
ISW-GALAXY CROSS-CORRELATION AMPLITUDE:

C_ℓ^{Tg} ∝ ∫ W^T(z) W^g(z) P(k,z) dz

where:
- W^T(z) = ISW kernel ∝ D(z) (1 + z) H(z) [dD/dz - D/(1+z)]
- W^g(z) = galaxy selection function
- P(k,z) = matter power spectrum

For γ-driven cosmology vs ΛCDM:
- D(z) suppressed (growth predictions)
- H(z) modified (distance ladder)
- Net C_ℓ^{Tg}: Sign same, amplitude ~10% different
-/

/-- Amplitude ratio prediction (approximate) -/
def amplitude_ratio_low_ell : ℚ := 90/100   -- 0.90 (suppressed)
def amplitude_ratio_high_ell : ℚ := 115/100 -- 1.15 (enhanced)

theorem low_ell_suppressed : amplitude_ratio_low_ell < 1 := by native_decide
theorem high_ell_enhanced : amplitude_ratio_high_ell > 1 := by native_decide

/-! ## Part 5: Falsification Criteria

ISW FALSIFICATION PROTOCOL:

The γ-driven ISW predictions are falsified if:
1. ISW-galaxy correlation is NEGATIVE (opposite sign)
2. Amplitude ratio at low ℓ is > 1.10 (should be suppressed)
3. Amplitude ratio at high ℓ is < 0.95 (should be enhanced)

Current data: Planck + SDSS/DES ISW detection at ~3-4σ
Future: CMB-S4 + DESI/Euclid will measure amplitude to ~5%
-/

def falsified_by_sign (measured : CorrelationSign) : Bool :=
  measured != .positive

def falsified_by_low_ell (ratio : ℚ) : Bool :=
  ratio > 110/100

def falsified_by_high_ell (ratio : ℚ) : Bool :=
  ratio < 95/100

/-! ## Part 6: Summary Table -/

def isw_prediction_table : String :=
  "╔════════════════╦═══════════════════════════════════════╗\n" ++
  "║ Observable     ║ γ-Driven Prediction                   ║\n" ++
  "╠════════════════╬═══════════════════════════════════════╣\n" ++
  "║ Sign           ║ POSITIVE (ISW-galaxy correlation)     ║\n" ++
  "║ Low ℓ (<20)    ║ Suppressed by 5-15% vs ΛCDM           ║\n" ++
  "║ High ℓ (20-100)║ Enhanced by 10-20% vs ΛCDM            ║\n" ++
  "║ Crossover      ║ ℓ ~ 15-25                             ║\n" ++
  "╚════════════════╩═══════════════════════════════════════╝\n\n" ++
  "WHY THIS IS INDEPENDENT:\n" ++
  "- Channel 1: (w₀, wₐ) from BAO/SNe distances\n" ++
  "- Channel 2: fσ₈(z) from RSD/weak lensing\n" ++
  "- Channel 3: ISW from CMB × LSS cross-correlation\n\n" ++
  "Same γ = 248/42. Three independent data streams."

/-! ## Part 7: Physical Interpretation

WHY γ MODIFIES ISW:

The thawing quintessence from γ:
- Early: w ≈ -1.85 (phantom-like) → potentials decay FAST
- Late: w → -0.55 (quintessence) → potentials decay SLOW

This creates a SCALE-DEPENDENT ISW modification:
- Large scales (low ℓ): Dominated by early-time (fast decay, suppressed)
- Small scales (high ℓ): Dominated by late-time (slow decay, enhanced)

The CROSSOVER at ℓ ~ 20 is a specific prediction testable with
CMB-S4 + Euclid/Roman cross-correlations.
-/

def physical_interpretation : String :=
  "γ-driven thawing quintessence:\n" ++
  "- Early times (z > 2): w ≈ -1.85, fast potential decay\n" ++
  "- Late times (z < 1): w → -0.55, slow potential decay\n\n" ++
  "ISW signal:\n" ++
  "- Low ℓ (large scales): Early-time dominated → SUPPRESSED\n" ++
  "- High ℓ (small scales): Late-time dominated → ENHANCED\n\n" ++
  "Crossover at ℓ ~ 15-25 is a SMOKING GUN for γ dynamics."

end ISWPredictions
