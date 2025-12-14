/-
# Evaluation Driver for GrowthFromGamma

This file is a small trusted computation layer:
- Uses the Float/RK4 implementation in GrowthFromGamma.lean
- Prints fσ₈(z) predictions for γ-driven cosmology and ΛCDM

Author: Jonathan Reich
Date: December 2025
-/

import StructuralIncompatibility.GrowthFromGamma

open GrowthFromGamma

#eval gamma_predictions
#eval lcdm_predictions
