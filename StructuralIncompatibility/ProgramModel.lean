import Mathlib.Logic.Basic

namespace ProgramModel

/-! # Shared Program Model

Minimal shared definitions used by multiple files (Halting, Rice).
-/

abbrev Program := ℕ → Option ℕ

def halts (p : Program) (n : ℕ) : Prop := ∃ m : ℕ, p n = some m

axiom encode_program : Program → ℕ
axiom encode_pair : ℕ → ℕ → ℕ

axiom decode_pair : ℕ → ℕ × ℕ
axiom decode_pair_spec : ∀ a b, decode_pair (encode_pair a b) = (a, b)

axiom program_of : ℕ → Program
axiom program_of_encode : ∀ p : Program, program_of (encode_program p) = p

def HaltingDecider (h : Program) : Prop :=
  ∀ p : Program, ∀ n : ℕ,
    (h (encode_pair (encode_program p) n) = some 1 ↔ halts p n) ∧
    (h (encode_pair (encode_program p) n) = some 0 ↔ ¬ halts p n)

end ProgramModel


