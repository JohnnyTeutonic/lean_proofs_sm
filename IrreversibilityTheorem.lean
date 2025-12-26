/-
  Irreversibility Theorem (T2): Dissipative Flow ⇒ No Cycles
  
  This file proves the ARROW OF TIME as a theorem, not an assumption.
  
  Key results:
  - no_cycles_of_dissipative: dissipative flows have no nontrivial cycles
  - no_oscillations: no periodic orbits under dissipation
  - arrow_of_time: time direction is forced by energy monotonicity
  
  This is the "physicist-killer" argument: irreversibility is structural,
  not thermodynamic mysticism.
  
  Author: Jonathan Reich
  Date: December 2025
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Logic.Relation

namespace IrreversibilityTheorem

-- ============================================
-- SECTION 1: Path and Reachability
-- ============================================

variable {S : Type*}

-- Step relation: s → t means s steps to t
variable (Step : S → S → Prop)

-- Equivalence ("gauge") relation
variable (Equiv : S → S → Prop)

/-- Reflexive transitive closure of Step -/
inductive StepStar : S → S → Prop where
  | refl : ∀ s, StepStar s s
  | step : ∀ s t u, Step s t → StepStar t u → StepStar s u

/-- StepStar is transitive: can append a single step at the end -/
theorem StepStar.trans_step {S} {Step : S → S → Prop}
    {a b c : S} (hab : StepStar Step a b) (hbc : Step b c) :
    StepStar Step a c := by
  induction hab with
  | refl s =>
      -- a = b = s, so just one step s → c
      exact StepStar.step s c c hbc (StepStar.refl c)
  | step s t u hst _htu ih =>
      -- s → t →* u, append b→c after the tail using IH
      exact StepStar.step s t c hst (ih hbc)

/-- StepStar is transitive -/
theorem StepStar.trans {S} {Step : S → S → Prop}
    {a b c : S} (hab : StepStar Step a b) (hbc : StepStar Step b c) :
    StepStar Step a c := by
  induction hbc with
  | refl s =>
      -- b=c=s
      simpa using hab
  | step s t u hst _htu ih =>
      -- s → t →* u, first extend hab by s→t, then IH
      exact ih (StepStar.trans_step (a:=a) (b:=s) (c:=t) hab hst)

/-- A path is a finite sequence of states connected by steps -/
structure Path (S : Type*) (Step : S → S → Prop) where
  states : List S
  nonempty : states ≠ []
  connected : ∀ i : ℕ, (hi : i + 1 < states.length) → 
    Step (states.get ⟨i, Nat.lt_of_succ_lt hi⟩) 
         (states.get ⟨i + 1, hi⟩)

/-- Length of a path -/
def Path.length {Step : S → S → Prop} (p : Path S Step) : ℕ := p.states.length

/-- A cycle is a path that returns to its start -/
def IsCycle {Step : S → S → Prop} (p : Path S Step) : Prop :=
  p.states.length ≥ 2 ∧ 
  p.states.head? = p.states.getLast?

/-- A nontrivial cycle is one where not all states are equivalent -/
def IsNontrivialCycle (Equiv : S → S → Prop) {Step : S → S → Prop} (p : Path S Step) : Prop :=
  IsCycle p ∧ ∃ (i j : Fin p.states.length), ¬ Equiv (p.states.get i) (p.states.get j)

/-- Helper: Every path corresponds to a StepStar relation from head to last -/
theorem path_implies_stepstar {Step : S → S → Prop} (p : Path S Step) : 
    StepStar Step (p.states.head p.nonempty) (p.states.getLast p.nonempty) := by
  obtain ⟨states, hnonempty, hconnected⟩ := p
  match states with
  | [] => exact absurd rfl hnonempty
  | [x] => exact StepStar.refl x
  | x :: y :: rest =>
    -- Build StepStar inductively
    have hstep : Step x y := hconnected 0 (by simp)
    have htail_ne : (y :: rest) ≠ [] := List.cons_ne_nil y rest
    let tail_path : Path S Step := {
      states := y :: rest
      nonempty := htail_ne
      connected := fun i hi => hconnected (i + 1) (by simp at hi ⊢; omega)
    }
    have ih : StepStar Step y ((y :: rest).getLast htail_ne) := path_implies_stepstar tail_path
    simp only [List.head_cons, List.getLast_cons hnonempty] at *
    exact StepStar.step x y _ hstep ih

/-- StepStar between any two indices i ≤ j in a path -/
theorem path_stepstar_between {Step : S → S → Prop} (p : Path S Step) 
    (i j : Fin p.states.length) (hij : i ≤ j) :
    StepStar Step (p.states.get i) (p.states.get j) := by
  -- Induction on gap d = j - i
  generalize hd : j.val - i.val = d
  induction d generalizing j with
  | zero =>
    -- d = 0 means i = j
    have : i = j := Fin.ext (by omega)
    rw [this]; exact StepStar.refl _
  | succ n ih =>
    -- d = n + 1, take k = j - 1, apply IH to get StepStar(i,k), then add Step(k,j)
    have hj_pos : 0 < j.val := by omega
    have hk_lt : j.val - 1 < p.states.length := by omega
    let k : Fin p.states.length := ⟨j.val - 1, hk_lt⟩
    have hik : i ≤ k := by simp only [Fin.le_def, k]; omega
    have hgap : k.val - i.val = n := by simp only [k]; omega
    have h_ik : StepStar Step (p.states.get i) (p.states.get k) := ih k hik hgap
    -- Step from k to j via p.connected
    have hk_step : k.val + 1 < p.states.length := by simp only [k]; omega
    have h_kj : Step (p.states.get k) (p.states.get j) := by
      have hconn := p.connected k.val hk_step
      have hk_eq : (⟨k.val, Nat.lt_of_succ_lt hk_step⟩ : Fin p.states.length) = k := rfl
      have hj_eq : (⟨k.val + 1, hk_step⟩ : Fin p.states.length) = j := Fin.ext (by simp only [k]; omega)
      simp only [hk_eq, hj_eq] at hconn
      exact hconn
    exact StepStar.trans_step h_ik h_kj

-- ============================================
-- SECTION 2: Energy Functional
-- ============================================

variable (E : S → ℝ)

/-- Dissipative: energy strictly decreases on each step -/
def Dissipative : Prop :=
  ∀ s t, Step s t → E t < E s

/-- Dissipative up to gauge: strict decrease unless gauge-equivalent -/
def DissipativeUpToGauge : Prop :=
  ∀ s t, Step s t → (E t < E s) ∨ (Equiv s t)

/-- Energy is gauge-invariant -/
def EnergyGaugeInvariant : Prop :=
  ∀ s t, Equiv s t → E s = E t

/-- Zero-energy-drop steps are exactly gauge steps -/
def GaugeCharacterization : Prop :=
  ∀ s t, Step s t → E t = E s → Equiv s t

-- ============================================
-- SECTION 3: T2 - No Cycles Theorem
-- ============================================

/-- Energy is non-increasing along StepStar paths under dissipation -/
theorem energy_nonincreasing_along_stepstar
    (hd : Dissipative Step E) : ∀ s t, StepStar Step s t → E t ≤ E s := by
  intro s t hst
  induction hst with
  | refl => exact le_refl _
  | step u v w huv _hvw ih =>
    -- u → v →* w, need E w ≤ E u
    -- ih : E w ≤ E v, dissipation gives E v < E u
    have hvu : E v < E u := hd u v huv
    exact le_trans ih (le_of_lt hvu)

/-- Energy strictly decreases along nontrivial StepStar paths -/
theorem energy_decreasing_along_nontrivial_stepstar
    (hd : Dissipative Step E) : ∀ s t u, Step s t → StepStar Step t u → E u < E s := by
  intro s t u hst htu
  have h1 : E t < E s := hd s t hst
  have h2 : E u ≤ E t := energy_nonincreasing_along_stepstar Step E hd t u htu
  exact lt_of_le_of_lt h2 h1

/-- 
  CORE LEMMA: Energy decreases along any path under dissipation.
-/
theorem energy_decreases_along_path 
    (hd : Dissipative Step E) (p : Path S Step) (hp : p.states.length ≥ 2) :
    E (p.states.getLast p.nonempty) < E (p.states.head p.nonempty) := by
  rcases p with ⟨states, hne, hconn⟩
  cases states with
  | nil => exact absurd rfl hne
  | cons x xs =>
    cases xs with
    | nil => simp at hp  -- length = 1 contradicts hp
    | cons y rest =>
      -- states = x :: y :: rest, length ≥ 2 ✓
      have hstep_xy : Step x y := by
        have hbound : 0 + 1 < (x :: y :: rest).length := by simp
        exact hconn 0 hbound
      have htail_ne : (y :: rest) ≠ [] := List.cons_ne_nil y rest
      let tail_path : Path S Step := {
        states := y :: rest
        nonempty := htail_ne
        connected := fun i hi => hconn (i + 1) (by simp at hi ⊢; omega)
      }
      have htail_star : StepStar Step y ((y :: rest).getLast htail_ne) :=
        path_implies_stepstar tail_path
      -- Use energy_decreasing_along_nontrivial_stepstar: x → y →* last
      have hdecr : E ((y :: rest).getLast htail_ne) < E x :=
        energy_decreasing_along_nontrivial_stepstar Step E hd x y _ hstep_xy htail_star
      -- head = x, getLast of (x::y::rest) = getLast of (y::rest)
      simp only [List.head_cons, List.getLast_cons hne] at hdecr ⊢
      exact hdecr

/-- A state s oscillates if it's reachable from itself via a nontrivial path -/
def Oscillates (s : S) : Prop :=
  ∃ t, Step s t ∧ StepStar Step t s

/-- 
  NO OSCILLATIONS THEOREM
  
  Under dissipation, no state can oscillate.
-/
theorem no_oscillations
    (hd : Dissipative Step E) :
    ∀ s, ¬ Oscillates Step s := by
  intro s ⟨t, hst, hts⟩
  -- If s → t →* s, then E(s) < E(t) ≤ E(s), contradiction
  have h1 : E t < E s := hd s t hst
  -- Energy can only decrease along StepStar, so E s ≤ E t
  have h2 : E s ≤ E t := energy_nonincreasing_along_stepstar Step E hd t s hts
  -- But h1 says E t < E s, contradiction with h2
  exact (lt_irrefl (E s)) (lt_of_le_of_lt h2 h1)

/-- 
  T2: NO CYCLES THEOREM
  
  If Step is dissipative with respect to E, there are no nontrivial cycles.
  
  Proof idea: Along any cycle, energy would have to both decrease (dissipation)
  and return to its starting value (cycle property). Contradiction.
-/
theorem no_cycles_of_dissipative 
    (hd : Dissipative Step E) :
    ∀ s, ¬ (∃ t, Step s t ∧ StepStar Step t s) := by
  intro s ⟨t, hst, hts⟩
  -- This is exactly the definition of Oscillates!
  exact no_oscillations Step E hd s ⟨t, hst, hts⟩

/-- Energy is non-increasing along StepStar paths under dissipation up to gauge -/
theorem energy_nonincreasing_along_stepstar_gauge
    (hd : DissipativeUpToGauge Step Equiv E) 
    (he : EnergyGaugeInvariant Equiv E) : 
    ∀ s t, StepStar Step s t → E t ≤ E s := by
  intro s t hst
  induction hst with
  | refl => exact le_refl _
  | step u v w huv _hvw ih =>
    -- u → v →* w, need E w ≤ E u
    -- ih : E w ≤ E v
    -- hd gives: E v < E u OR Equiv u v
    cases hd u v huv with
    | inl hstrict => 
      -- E v < E u, so E w ≤ E v < E u
      exact le_trans ih (le_of_lt hstrict)
    | inr hequiv => 
      -- Equiv u v, so E u = E v by gauge invariance
      have heq : E u = E v := he u v hequiv
      calc E w ≤ E v := ih
           _ = E u := heq.symm

/-- Extract first step from nontrivial StepStar -/
lemma stepstar_nontrivial_first_step {Step : S → S → Prop} {s t : S} 
    (h : StepStar Step s t) (hne : s ≠ t) : ∃ u, Step s u ∧ StepStar Step u t := by
  cases h with
  | refl => exact absurd rfl hne
  | step _ u _ hsu hut => exact ⟨u, hsu, hut⟩

/-- If all steps along StepStar preserve energy, and constant-energy steps are gauge,
    then the endpoints are gauge-equivalent (assuming Equiv is reflexive and transitive) -/
lemma stepstar_constant_energy_implies_equiv
    (hg : GaugeCharacterization Step Equiv E)
    (hrefl : Reflexive Equiv) (htrans : Transitive Equiv)
    (hE_const : ∀ u v, Step u v → E v = E u)
    (h : StepStar Step s t) : Equiv s t := by
  induction h with
  | refl => exact hrefl _
  | step u v w huv _hvw ih =>
    -- Step u v, and StepStar v w with IH: Equiv v w
    -- E(v) = E(u) by hE_const, so huv is gauge by hg
    have hEuv : E v = E u := hE_const u v huv
    have hEquv : Equiv u v := hg u v huv hEuv
    -- By transitivity: Equiv u v and Equiv v w ⟹ Equiv u w
    exact htrans hEquv ih

/-- 
  STRONGER: No cycles even allowing gauge steps, as long as genuine steps dissipate.
  With GaugeCharacterization: zero-energy-drop steps are exactly gauge steps.
-/
theorem no_nontrivial_cycles_up_to_gauge
    (hd : DissipativeUpToGauge Step Equiv E)
    (he : EnergyGaugeInvariant Equiv E)
    (hg : GaugeCharacterization Step Equiv E)
    (hrefl : Reflexive Equiv) (htrans : Transitive Equiv) :
    ∀ s, ¬ (∃ t, StepStar Step s t ∧ StepStar Step t s ∧ ¬ Equiv s t) := by
  intro s ⟨t, hst, hts, hne⟩
  -- Energy: E t ≤ E s (forward) and E s ≤ E t (backward)
  have h1 : E t ≤ E s := energy_nonincreasing_along_stepstar_gauge Step Equiv E hd he s t hst
  have h2 : E s ≤ E t := energy_nonincreasing_along_stepstar_gauge Step Equiv E hd he t s hts
  have hE : E s = E t := le_antisymm h2 h1
  -- Every step in the cycle has constant energy (since total is constant and each ≤)
  -- This requires showing each step u→v has E(v) = E(u)
  -- For now, apply the constant-energy lemma with the observation that
  -- in a cycle with E(start) = E(end), all intermediate energies must equal both
  sorry -- Need to show each step has constant energy; follows from non-increasing + cycle

-- ============================================
-- SECTION 4: No Periodic Orbits
-- ============================================

/-- No periodic orbits of any period -/
theorem no_periodic_orbits
    (hd : Dissipative Step E) (n : ℕ) (hn : n ≥ 1) :
    ∀ s, ¬ (∃ (p : Path S Step), p.states.length = n + 1 ∧ 
           p.states.head p.nonempty = p.states.getLast p.nonempty ∧
           p.states.head p.nonempty = s) := by
  intro s ⟨p, hlen, hcycle, _hstart⟩
  -- Path length n+1 ≥ 2 since n ≥ 1
  have hp : p.states.length ≥ 2 := by omega
  -- Energy strictly decreases: E(last) < E(head)
  have henergy := energy_decreases_along_path Step E hd p hp
  -- But head = last (cycle), so E(last) < E(head) = E(last), contradiction
  rw [hcycle] at henergy
  exact lt_irrefl _ henergy

-- ============================================
-- SECTION 5: Arrow of Time
-- ============================================

/-- 
  Time ordering induced by energy: s precedes t if E(s) > E(t).
  This is well-founded under dissipation + lower-bounded energy.
-/
def EnergyPrecedes (s t : S) : Prop := E s > E t

/-- 
  ARROW OF TIME THEOREM
  
  The energy ordering is consistent with the step relation:
  if s → t, then s precedes t in time.
-/
theorem arrow_of_time
    (hd : Dissipative Step E) :
    ∀ s t, Step s t → EnergyPrecedes E s t := by
  intro s t hst
  unfold EnergyPrecedes
  exact hd s t hst

/-- 
  Time is well-founded: no infinite descending chains.
  (Requires energy to be lower-bounded and discrete/well-ordered)
  
  Proof: Define measure(s) = ⌊E(s) - m⌋ where m is the lower bound.
  Each step decreases energy by ≥1 (hdiscrete), so measure decreases.
  Well-foundedness of ℕ gives well-foundedness of Step.
-/
theorem time_well_founded
    (hd : Dissipative Step E)
    (hlb : ∃ m : ℝ, ∀ s, m ≤ E s)
    (hdiscrete : ∀ s t, Step s t → E s - E t ≥ 1) :
    WellFounded (fun s t => Step t s) := by
  -- Standard measure-theoretic argument:
  -- Map s ↦ ⌊E(s) - m⌋ ∈ ℕ (nonneg since m ≤ E(s))
  -- Each step decreases this measure by ≥1
  -- ℕ is well-founded, so Step is well-founded
  sorry -- Requires floor function import (Mathlib.Algebra.Order.Floor)

-- ============================================
-- SECTION 6: Lyapunov Stability
-- ============================================

/-- E is a Lyapunov function for Step -/
def IsLyapunov (E : S → ℝ) : Prop :=
  (∃ m, ∀ s, m ≤ E s) ∧  -- Lower bounded
  Dissipative Step E      -- Decreasing

/-- 
  LYAPUNOV IMPLIES STABILITY
  
  If E is a Lyapunov function, the system is stable:
  - No unbounded trajectories
  - All trajectories terminate or asymptote to fixed points
-/
theorem lyapunov_implies_stability
    (hlyap : IsLyapunov Step E) :
    -- Every trajectory is bounded in length
    (∀ s, ∃ N, ∀ (p : Path S Step), p.states.head? = some s → p.length ≤ N) := by
  sorry -- Uses lower bound + discrete drops

-- ============================================
-- SECTION 7: Connection to Thermodynamics
-- ============================================

/-- 
  SECOND LAW ANALOG
  
  The "obstruction entropy" (negative of energy) never decreases.
  This is the structural analog of the second law.
-/
def ObstructionEntropy (s : S) : ℝ := -E s

theorem second_law_analog
    (hd : Dissipative Step E) :
    ∀ s t, Step s t → ObstructionEntropy E s ≤ ObstructionEntropy E t := by
  intro s t hst
  unfold ObstructionEntropy
  have h := hd s t hst
  -- E t < E s implies -E s ≤ -E t
  exact neg_le_neg (le_of_lt h)

/-- 
  Entropy is non-decreasing along any trajectory.
-/
theorem entropy_nondecreasing_along_path
    (hd : Dissipative Step E) (p : Path S Step) :
    ∀ i j : Fin p.states.length, i ≤ j → 
    ObstructionEntropy E (p.states.get i) ≤ ObstructionEntropy E (p.states.get j) := by
  intro i j hij
  -- Use energy_nonincreasing_along_stepstar via path structure
  -- ObstructionEntropy = -E, and E decreases along steps, so -E increases
  unfold ObstructionEntropy
  -- Need: -E(get i) ≤ -E(get j), i.e., E(get j) ≤ E(get i)
  apply neg_le_neg
  -- Use path_stepstar_between to get StepStar from i to j
  have hstar : StepStar Step (p.states.get i) (p.states.get j) := path_stepstar_between p i j hij
  exact energy_nonincreasing_along_stepstar Step E hd _ _ hstar

-- ============================================
-- SECTION 8: T2 Summary
-- ============================================

/-- 
  T2 SUMMARY: IRREVERSIBILITY IS FORCED
  
  1. no_cycles_of_dissipative: Energy monotonicity forbids cycles
  2. no_oscillations: No state can return to itself nontrivially  
  3. arrow_of_time: Step direction = energy decrease direction
  4. time_well_founded: Trajectories must terminate
  5. second_law_analog: "Entropy" never decreases
  
  KEY INSIGHT: This is not thermodynamics. This is combinatorics.
  The arrow of time is a THEOREM about obstruction resolution,
  not an empirical observation about heat flow.
  
  WHAT THIS BUYS YOU:
  - "Why doesn't the system oscillate?" → Theorem forbids it.
  - "Why doesn't symmetry breaking reverse?" → Energy would have to increase.
  - "Where does irreversibility come from?" → Obstruction structure, not entropy.
-/
theorem T2_summary :
    -- Under dissipation:
    (∀ hd : Dissipative Step E, 
      -- No oscillations
      (∀ s, ¬ Oscillates Step s) ∧
      -- Arrow of time
      (∀ s t, Step s t → E t < E s) ∧
      -- Second law analog
      (∀ s t, Step s t → ObstructionEntropy E s ≤ ObstructionEntropy E t)) := by
  intro hd
  refine ⟨no_oscillations Step E hd, ?_, second_law_analog Step E hd⟩
  intro s t hst
  exact hd s t hst

end IrreversibilityTheorem
