import Mathlib.Data.Nat.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

/-!
# Yukawa Selection Rules from Z₃ Family Symmetry

Copyright (c) 2025 Jonathan Reich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

## Overview

This file derives **exact texture zeros** in Yukawa matrices from residual Z₃ family symmetry.

The key insight: if the Yukawa sector respects a residual Z₃ symmetry (surviving from E₈ → E₆ × SU(3)),
then specific matrix entries must vanish exactly—not approximately, not suppressed, but **zero**.

## Main Results

1. `Z3ChargeInvariant Y ↔ Diagonal Y`: Z₃ charge conservation forces diagonal structure
2. `z3_forces_texture_zeros`: Explicit enumeration of which entries must vanish
3. `z3_forbids_mixing`: Off-diagonal Yukawa couplings forbidden under exact Z₃

## Physical Interpretation

- **If Z₃ is exact**: No inter-generational mixing in the Yukawa sector
- **If mixing observed**: Z₃ must be broken (falsifiable prediction)
- **Hierarchy of breaking**: Small Z₃ breaking → small mixing angles

This parallels the proton decay selection rules but applies to flavor physics.

Author: Jonathan Reich
Date: January 2026
-/

namespace YukawaSelectionRulesFromZ3

/-! ## Part 1: Generation Structure -/

/-- Number of generations -/
def N_gen : ℕ := 3

/-- Generation index type -/
abbrev Gen : Type := Fin N_gen

/-- Named generations -/
def gen1 : Gen := ⟨0, by decide⟩
def gen2 : Gen := ⟨1, by decide⟩
def gen3 : Gen := ⟨2, by decide⟩

/-! ## Part 2: Z₃ Charge Assignment -/

/-- Z₃ charge assignment: generation i has charge i mod 3 -/
def z3Charge : Gen → ZMod N_gen := fun g => (g.val : ZMod N_gen)

/-- The Z₃ charges are distinct -/
theorem z3_charges_distinct :
    z3Charge gen1 = 0 ∧ z3Charge gen2 = 1 ∧ z3Charge gen3 = 2 := by
  simp [z3Charge, gen1, gen2, gen3]

/-! ## Part 3: Yukawa Matrix Structure -/

/-- A Yukawa-type matrix (real for simplicity; complex phases not needed for texture zeros) -/
def YukawaMat := Gen → Gen → ℚ

/-- A matrix is diagonal if all off-diagonal entries vanish -/
def Diagonal (M : YukawaMat) : Prop :=
  ∀ i j : Gen, i ≠ j → M i j = 0

/-! ## Part 4: Z₃ Charge Invariance (Correct Physical Definition) -/

/--
**CORRECT Z₃ INVARIANCE**: Based on Z₃ charge transformation.

Under Z₃, generation i transforms with phase ω^i where ω = e^{2πi/3}.
A Yukawa coupling Y_{ij} transforms as ω^{i-j} (from ψ̄_i Y_{ij} ψ_j).

Z₃ invariance requires: ω^{i-j} = 1 for all entries Y_{ij} ≠ 0.
Since ω³ = 1 and ω ≠ 1, this means: i - j ≡ 0 (mod 3).

For i,j ∈ {0,1,2}, the only solutions are i = j.
Therefore: **Z₃ invariance forces Y to be diagonal**.
-/
def Z3ChargeInvariant (Y : YukawaMat) : Prop :=
  ∀ i j : Gen, (i.val : ZMod 3) ≠ (j.val : ZMod 3) → Y i j = 0

/-- Z3ChargeInvariant is equivalent to Diagonal for 3 generations -/
theorem z3_charge_invariant_iff_diagonal (Y : YukawaMat) :
    Z3ChargeInvariant Y ↔ Diagonal Y := by
  constructor
  · intro hZ3 i j hij
    apply hZ3
    -- Need to show (i.val : ZMod 3) ≠ (j.val : ZMod 3) from i ≠ j
    intro heq
    apply hij
    -- i.val and j.val are both < 3, and equal mod 3, so equal
    have hi : i.val < 3 := i.isLt
    have hj : j.val < 3 := j.isLt
    have heq' : i.val = j.val := by
      have h1 : (i.val : ZMod 3).val = i.val := ZMod.val_natCast_of_lt hi
      have h2 : (j.val : ZMod 3).val = j.val := ZMod.val_natCast_of_lt hj
      have h3 : (i.val : ZMod 3).val = (j.val : ZMod 3).val := by rw [heq]
      omega
    exact Fin.ext heq'
  · intro hdiag i j hij
    apply hdiag
    intro heq
    apply hij
    simp only [heq]

/--
**MAIN THEOREM (Correct Version): Z₃ charge invariance forces exact texture zeros**

This is the physically correct statement: if the Yukawa matrix respects Z₃ family
charge conservation, then all off-diagonal entries must vanish exactly.
-/
theorem z3_forces_texture_zeros (Y : YukawaMat) (hZ3 : Z3ChargeInvariant Y) :
    Y gen1 gen2 = 0 ∧ Y gen1 gen3 = 0 ∧
    Y gen2 gen1 = 0 ∧ Y gen2 gen3 = 0 ∧
    Y gen3 gen1 = 0 ∧ Y gen3 gen2 = 0 := by
  have hdiag := z3_charge_invariant_iff_diagonal Y |>.mp hZ3
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hdiag gen1 gen2 (by decide)
  · exact hdiag gen1 gen3 (by decide)
  · exact hdiag gen2 gen1 (by decide)
  · exact hdiag gen2 gen3 (by decide)
  · exact hdiag gen3 gen1 (by decide)
  · exact hdiag gen3 gen2 (by decide)

/-! ## Part 8: Physical Consequences -/

/--
**Mixing Angle Prediction**: Under exact Z₃, no CKM/PMNS mixing.

If Yukawa matrices are Z₃-invariant (both up-type and down-type),
then both are diagonal in the same basis, so V_CKM = I.
-/
theorem z3_forbids_mixing (Yu Yd : YukawaMat) 
    (hYu : Z3ChargeInvariant Yu) (hYd : Z3ChargeInvariant Yd) :
    Diagonal Yu ∧ Diagonal Yd := by
  exact ⟨z3_charge_invariant_iff_diagonal Yu |>.mp hYu,
         z3_charge_invariant_iff_diagonal Yd |>.mp hYd⟩

/--
**Falsification Criterion**: Observed mixing implies Z₃ breaking.

If CKM mixing is observed (|V_{us}| ≠ 0), then Z₃ cannot be exact.
This is the contrapositive of z3_forbids_mixing.
-/
theorem mixing_implies_z3_broken (Yu Yd : YukawaMat) 
    (hMixing : Yu gen1 gen2 ≠ 0 ∨ Yd gen1 gen2 ≠ 0) :
    ¬(Z3ChargeInvariant Yu ∧ Z3ChargeInvariant Yd) := by
  intro ⟨hYu, hYd⟩
  have ⟨hYu_zeros, _⟩ := z3_forces_texture_zeros Yu hYu
  have ⟨hYd_zeros, _⟩ := z3_forces_texture_zeros Yd hYd
  cases hMixing with
  | inl h => exact h hYu_zeros
  | inr h => exact h hYd_zeros

/-! ## Part 9: Connection to E8 Programme -/

/--
**Structural Claim**: The Z₃ grading comes from E8 → E6 × SU(3).

The SU(3)_family factor induces a Z₃ grading on generations.
If this Z₃ is preserved in the Yukawa sector, texture zeros are exact.

This connects to:
- `E8BranchingSelectionRules.lean`: proton decay selection rules
- `SelectionRuleFromFamilySymmetry.lean`: commutant lemma
- `ProtonDecayHierarchyFromE8.lean`: end-to-end pipeline
-/
def e8_z3_connection : String :=
  "Z₃ ⊂ SU(3)_family ⊂ E8 → texture zeros in Yukawa sector"

/-! ## Summary

**MAIN RESULTS**:

1. `Z3ChargeInvariant Y ↔ Diagonal Y`: Z₃ charge conservation ⇔ diagonal Yukawa
2. `z3_forces_texture_zeros`: Explicit list of vanishing entries
3. `z3_forbids_mixing`: Exact Z₃ implies no CKM/PMNS mixing
4. `mixing_implies_z3_broken`: Observed mixing → Z₃ must be broken

**PHYSICAL INTERPRETATION**:

- Z₃ family symmetry (from E8 → E6 × SU(3)) would forbid inter-generational Yukawas
- Observed mixing (Cabibbo angle ≈ 0.22) implies Z₃ is broken
- The *amount* of breaking controls the *size* of mixing angles
- This explains hierarchy: small breaking → small off-diagonal → small mixing

**FALSIFICATION**:

- Exact Z₃: V_CKM = I, V_PMNS = I
- If ANY mixing observed → Z₃ broken
- Prediction: mixing angles are NOT structural constants, but measure Z₃ breaking

**STATUS**: Fully proven (after removing initial sorry-laden attempt), 0 sorrys in final theorems.
-/

end YukawaSelectionRulesFromZ3
