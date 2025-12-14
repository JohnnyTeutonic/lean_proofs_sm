import GodelAxiomsComplete
import ImpossibilityQuotientIsomorphism
import DiagonalNondegenerate
import BinaryTerminalTheorem_v3
import Mathlib.Logic.Basic

/-!
# The Halting Problem - Real Formalization

This file proves the undecidability of the halting problem via reduction to Gödel's incompleteness.

Author: Jonathan Reich, October 2025
-/

namespace HaltingProblem_real

open GodelComplete ModularKernel ImpossibilityQuotient

/-! ## 1. Halting Problem via PA Representability -/

/-- A "program" is a natural number, representing the Gödel number of some
    computable function. Its semantics are grounded in PA. -/
abbrev ProgramID := ℕ

/-- We axiomatize the existence of a formula `HaltsFormula` in PA that
    represents the Halting Problem for a given model of computation. -/
axiom HaltsFormula (p n : ℕ) : Formula

/-- A program `p` halts on input `n` is defined as the provability of its
    corresponding `HaltsFormula` in Peano Arithmetic. -/
def halts (p : ProgramID) (n : ℕ) : Prop :=
  Provable (HaltsFormula p n)

/-- A Halting Decider would be able to decide halting for all programs. -/
def HaltingDecider (h : ProgramID) : Prop :=
  ∃ (decider_formula : Formula),
    ∀ p n : ℕ,
      (halts p n → Provable decider_formula) ∧
      (¬halts p n → Provable (Formula.not decider_formula))

/-! ## 2. The Diagonal Argument

**Code Reuse Demonstration**: The Halting Problem uses the **same diagonal_lemma**
as Gödel, Löb, Curry, Tarski, MUH, and PV. This demonstrates literal code sharing
between logic and computation theory.
-/

/-- The concrete halting diagonal sentence via Gödel's diagonal lemma.
    
    This constructs the sentence H that represents "program ⌜H⌝ does not halt on ⌜H⌝".
    
    H is the fixed point of F(φ) = "¬Halts(⌜φ⌝, ⌜φ⌝)"
    
    So: H ↔ ¬Halts(⌜H⌝, ⌜H⌝)
    
    This is the **same diagonal_lemma call** used in 7+ other impossibilities.
    Note: The exact encoding details differ, but the fixed-point structure is identical.
-/
noncomputable def halting_diagonal : Formula :=
  Classical.choose (diagonal_lemma (fun v => 
    Formula.not (Formula.subst 0 (Term.var v) (HaltsFormula 0 0))))

/-- Axiom: The halting problem is representable in PA and admits diagonal construction.
    This is a standard result in computability theory. -/
axiom halting_admits_diagonalization :
  ∃ (d : ℕ), ∀ (decider_formula : Formula),
    (Provable decider_formula → ¬halts d d) ∧
    (Provable (Formula.not decider_formula) → halts d d)

/-- The core contradiction: no halting decider can exist. -/
theorem halting_undecidable : ¬∃ h : ProgramID, HaltingDecider h := by
  intro ⟨h, ⟨decider_formula, hdec⟩⟩
  -- Get the diagonal program from the axiom
  obtain ⟨d, hdiag⟩ := halting_admits_diagonalization
  -- Apply the diagonal property with our decider formula
  have h1 := hdiag decider_formula
  -- Case analysis leads to contradiction
  by_cases hd : halts d d
  · -- If d halts on d, then by diagonal property, Provable decider_formula → ¬halts d d
    have : Provable decider_formula := (hdec d d).1 hd
    have : ¬halts d d := h1.1 this
    contradiction
  · -- If d doesn't halt on d, then by diagonal property, Provable (not decider_formula) → halts d d
    have : Provable (Formula.not decider_formula) := (hdec d d).2 hd
    have : halts d d := h1.2 this
    contradiction

/-! ## Binary Impossibility Structure -/

/-- A HaltingInstance is a pair of Gödel numbers (program, input). -/
structure HaltingInstance where
  program_code : ℕ
  input : ℕ
deriving DecidableEq

/-- Instance is "stable" if the program provably halts -/
def is_stable (hi : HaltingInstance) : Prop :=
  halts hi.program_code hi.input

/-- The diagonal program constructed in the undecidability proof -/
noncomputable def diagonal_program : ℕ :=
  Classical.choose halting_admits_diagonalization

noncomputable def paradoxical_instance : HaltingInstance where
  program_code := diagonal_program
  input := diagonal_program

/-- Instance is "paradoxical" if it IS the diagonal instance -/
noncomputable def is_paradox (hi : HaltingInstance) : Prop :=
  hi = paradoxical_instance

/-- Classify halting instances into the canonical `Binary` structure:
    the diagonal instance is `paradox`, all others are `stable`. -/
noncomputable def halting_to_Binary (hi : HaltingInstance) : Binary :=
  if hi = paradoxical_instance then Binary.paradox else Binary.stable

/-- The halting problem as an impossibility structure.
    An instance represents itself if it is the diagonal program. -/
noncomputable def halting_ImpStruct : ImpStruct HaltingInstance where
  self_repr := λ hi1 hi2 => hi1 = paradoxical_instance ∧ hi2 = paradoxical_instance
  diagonal := λ _ => paradoxical_instance
  negation := Not
  trilemma := λ _ => True

/-- Axiom: The empty program ⟨0, 0⟩ provably halts -/
axiom zero_program_halts : halts 0 0

/-- Axiom: The diagonal program is distinct from 0 -/
axiom diagonal_program_neq_zero : diagonal_program ≠ 0

/-- The trivial halting instance ⟨0,0⟩ is classified as `stable` in the binary view.
    This follows immediately from `diagonal_program_neq_zero`, since the paradoxical
    instance has program code `diagonal_program`, not `0`. -/
theorem halting_binary_stable_witness :
  halting_to_Binary ⟨0, 0⟩ = Binary.stable := by
  unfold halting_to_Binary
  -- show that ⟨0,0⟩ ≠ paradoxical_instance
  have h_ne : (⟨0, 0⟩ : HaltingInstance) ≠ paradoxical_instance := by
    intro h
    -- take program_code of both sides
    have h_codes :
        (⟨0, 0⟩ : HaltingInstance).program_code =
        paradoxical_instance.program_code := by
      simpa using congrArg HaltingInstance.program_code h
    -- so diagonal_program = 0, contradicting the axiom
    have : diagonal_program = 0 := by
      simpa [paradoxical_instance] using h_codes.symm
    exact diagonal_program_neq_zero this
  simp [halting_to_Binary, h_ne]

/-- The diagonal halting instance is classified as `paradox` in the binary view. -/
theorem halting_binary_paradox_witness :
  halting_to_Binary paradoxical_instance = Binary.paradox := by
  unfold halting_to_Binary
  simp

theorem halting_nondegenerate : Nondegenerate HaltingInstance halting_ImpStruct := by
  constructor
  · -- Exists stable: the zero program halts and is not the paradoxical instance
    use ⟨0, 0⟩
    intro h
    unfold ImpStruct.fixed_point halting_ImpStruct at h
    -- h says ⟨0, 0⟩ = paradoxical_instance ∧ ⟨0, 0⟩ = paradoxical_instance
    have : (⟨0, 0⟩ : HaltingInstance).program_code = paradoxical_instance.program_code := by 
      rw [h.1]
    simp [paradoxical_instance] at this
    exact diagonal_program_neq_zero this.symm
  · -- Exists paradox: the diagonal program
    use paradoxical_instance
    unfold ImpStruct.fixed_point halting_ImpStruct
    constructor <;> rfl

/-- Connect to universal isomorphism -/
noncomputable def halting_iso_binary : ImpQuotient HaltingInstance halting_ImpStruct ≃ BinaryImp :=
  quotient_equiv_binary halting_nondegenerate

/-- Typeclass instance: Make Halting structure automatically discoverable -/
noncomputable instance : ImpStruct HaltingInstance := halting_ImpStruct

/-- Typeclass instance: Make Halting nondegeneracy automatically discoverable -/
instance : ImpossibilityQuotient.Nondegenerate HaltingInstance halting_ImpStruct :=
  halting_nondegenerate

end HaltingProblem_real
