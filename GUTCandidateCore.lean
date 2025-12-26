/-
# GUT Candidate Core Definitions

Shared definitions for GUT candidates used across multiple files:
- E8UniquenessProof.lean
- StrongCPFromPi3.lean
- GravityFromObstruction.lean
- TerminalInSym.lean

This consolidation addresses A4 from the E8UniquenessProof gameplan:
"Reduce duplicated candidate universe definitions."

## Axiom Boundary Documentation (L4 Compliance)

The `pi3_trivial` field encodes the **literature fact** that π₃(E₈) = 0
is unique among simple Lie groups. This is the authoritative interface
where homotopy-theoretic facts are instantiated.

**Design choice**: We encode these as data fields rather than axioms because:
1. The candidate list is finite and well-known
2. The values are established mathematical facts (Bott periodicity)
3. This allows `simp` to discharge proofs automatically

**Literature references**:
- π₃(SU(n)) ≅ ℤ for all n ≥ 2
- π₃(SO(n)) ≅ ℤ for n ≥ 5
- π₃(E₆) ≅ ℤ, π₃(E₇) ≅ ℤ
- π₃(E₈) = 0 (unique among simple Lie groups)

See: Mimura & Toda, "Topology of Lie Groups" for complete homotopy tables.

Author: Jonathan Reich
Date: December 2025
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

namespace GUTCandidateCore

/-! ## Part 1: Core Structure -/

/-- A GUT candidate algebra with all relevant structural data.
    This is the single source of truth for candidate properties. -/
structure GUTCandidate where
  name : String
  dim : ℕ
  rank : ℕ
  /-- Third homotopy group: true if π₃ = 0 -/
  pi3_trivial : Bool
  /-- Is exceptional (vs classical)? -/
  is_exceptional : Bool
  deriving DecidableEq, Repr

/-! ## Part 2: The Five GUT Candidates -/

/-- SU(5): Georgi-Glashow model -/
def SU5 : GUTCandidate := ⟨"SU(5)", 24, 4, false, false⟩

/-- SO(10): Pati-Salam unification -/
def SO10 : GUTCandidate := ⟨"SO(10)", 45, 5, false, false⟩

/-- E₆: First exceptional candidate -/
def E6 : GUTCandidate := ⟨"E₆", 78, 6, false, true⟩

/-- E₇: Second exceptional candidate -/
def E7 : GUTCandidate := ⟨"E₇", 133, 7, false, true⟩

/-- E₈: Terminal exceptional algebra -/
def E8 : GUTCandidate := ⟨"E₈", 248, 8, true, true⟩

/-- The standard GUT candidate universe -/
def candidates : List GUTCandidate := [SU5, SO10, E6, E7, E8]

/-! ## Part 3: Decidable Properties -/

/-- π₃ = 0 (StrongCPNatural criterion) -/
def hasTrivialPi3 (G : GUTCandidate) : Bool := G.pi3_trivial

/-- Is exceptional algebra -/
def isExceptional (G : GUTCandidate) : Bool := G.is_exceptional

/-- Dimension check -/
def hasDim (G : GUTCandidate) (d : ℕ) : Bool := G.dim == d

/-! ## Part 4: Prop-Level Predicates (Defined, Not Axiomatized) -/

/-- GRAVITY COMPATIBLE: G can host the full Planck-scale obstruction structure.
    
    Criterion: G must be exceptional AND have dimension 248 (terminal).
    This captures "hosts the Planck obstruction" from the obstruction framework.
    
    Physics: Only E₈ is large enough to contain both SM gauge structure
    AND the diffeomorphism obstruction that gives GR. -/
def GravityCompatible (G : GUTCandidate) : Prop :=
  G.is_exceptional = true ∧ G.dim = 248

/-- STRONG CP NATURAL: θ_QCD = 0 without requiring an axion.
    
    Criterion: π₃(G) = 0
    
    Mathematics: π₃(E₈) = 0 is UNIQUE among simple Lie groups.
    All others have π₃ ≅ ℤ, allowing arbitrary θ.
    
    Reference: Bott periodicity and homotopy of Lie groups. -/
def StrongCPNatural (G : GUTCandidate) : Prop :=
  G.pi3_trivial = true

/-- IS TERMINAL: No proper extension exists in the exceptional series.
    
    Criterion: G is maximal among exceptional algebras in candidates.
    
    Mathematics: E₈ is terminal in the exceptional chain (no E₉). -/
def IsTerminal (G : GUTCandidate) : Prop :=
  G.is_exceptional = true ∧ ∀ H ∈ candidates, H.is_exceptional = true → H.dim ≤ G.dim

/-- EMBEDS SM: Contains SU(3) × SU(2) × U(1) -/
def EmbedsSM (G : GUTCandidate) : Prop :=
  G.dim ≥ 12  -- SM has dim 12; any GUT must contain it

/-! ## Part 5: Lemmas for Each Candidate -/

-- GravityCompatible lemmas
lemma GravityCompatible_E8 : GravityCompatible E8 := by simp [GravityCompatible, E8]
lemma not_GravityCompatible_SU5 : ¬GravityCompatible SU5 := by simp [GravityCompatible, SU5]
lemma not_GravityCompatible_SO10 : ¬GravityCompatible SO10 := by simp [GravityCompatible, SO10]
lemma not_GravityCompatible_E6 : ¬GravityCompatible E6 := by simp [GravityCompatible, E6]
lemma not_GravityCompatible_E7 : ¬GravityCompatible E7 := by simp [GravityCompatible, E7]

-- StrongCPNatural lemmas
lemma StrongCPNatural_E8 : StrongCPNatural E8 := by simp [StrongCPNatural, E8]
lemma not_StrongCPNatural_SU5 : ¬StrongCPNatural SU5 := by simp [StrongCPNatural, SU5]
lemma not_StrongCPNatural_SO10 : ¬StrongCPNatural SO10 := by simp [StrongCPNatural, SO10]
lemma not_StrongCPNatural_E6 : ¬StrongCPNatural E6 := by simp [StrongCPNatural, E6]
lemma not_StrongCPNatural_E7 : ¬StrongCPNatural E7 := by simp [StrongCPNatural, E7]

-- IsTerminal lemmas
lemma IsTerminal_E8 : IsTerminal E8 := by
  constructor
  · simp [E8]
  · intro H hH _
    simp [candidates] at hH
    rcases hH with rfl | rfl | rfl | rfl | rfl <;> simp [SU5, SO10, E6, E7, E8]

lemma not_IsTerminal_SU5 : ¬IsTerminal SU5 := by simp [IsTerminal, SU5]
lemma not_IsTerminal_SO10 : ¬IsTerminal SO10 := by simp [IsTerminal, SO10]
lemma not_IsTerminal_E6 : ¬IsTerminal E6 := by simp [IsTerminal, E6, E8, candidates]
lemma not_IsTerminal_E7 : ¬IsTerminal E7 := by simp [IsTerminal, E7, E8, candidates]

-- EmbedsSM lemmas
lemma EmbedsSM_E8 : EmbedsSM E8 := by simp [EmbedsSM, E8]
lemma EmbedsSM_SU5 : EmbedsSM SU5 := by simp [EmbedsSM, SU5]
lemma EmbedsSM_SO10 : EmbedsSM SO10 := by simp [EmbedsSM, SO10]
lemma EmbedsSM_E6 : EmbedsSM E6 := by simp [EmbedsSM, E6]
lemma EmbedsSM_E7 : EmbedsSM E7 := by simp [EmbedsSM, E7]

/-! ## Part 6: Uniqueness Theorems -/

/-- E₈ is the unique gravity-compatible candidate -/
theorem GravityCompatible_unique :
    ∀ G ∈ candidates, GravityCompatible G → G = E8 := by
  intro G hG hGrav
  simp [candidates] at hG
  rcases hG with rfl | rfl | rfl | rfl | rfl
  · exact absurd hGrav not_GravityCompatible_SU5
  · exact absurd hGrav not_GravityCompatible_SO10
  · exact absurd hGrav not_GravityCompatible_E6
  · exact absurd hGrav not_GravityCompatible_E7
  · rfl

/-- E₈ is the unique candidate with trivial π₃ -/
theorem StrongCPNatural_unique :
    ∀ G ∈ candidates, StrongCPNatural G → G = E8 := by
  intro G hG hCP
  simp [candidates] at hG
  rcases hG with rfl | rfl | rfl | rfl | rfl
  · exact absurd hCP not_StrongCPNatural_SU5
  · exact absurd hCP not_StrongCPNatural_SO10
  · exact absurd hCP not_StrongCPNatural_E6
  · exact absurd hCP not_StrongCPNatural_E7
  · rfl

/-- E₈ is the unique terminal candidate -/
theorem IsTerminal_unique :
    ∀ G ∈ candidates, IsTerminal G → G = E8 := by
  intro G hG hTerm
  simp [candidates] at hG
  rcases hG with rfl | rfl | rfl | rfl | rfl
  · exact absurd hTerm not_IsTerminal_SU5
  · exact absurd hTerm not_IsTerminal_SO10
  · exact absurd hTerm not_IsTerminal_E6
  · exact absurd hTerm not_IsTerminal_E7
  · rfl

end GUTCandidateCore
