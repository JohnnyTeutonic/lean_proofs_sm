/-
# ImpossibilityPushPull: pushforward & pullback functors for ImpStructs

Adds two constructions on top of `ModularKernel`:

* pushStruct / pushFunctor    : (S,I) ⟶ (T, push I along f) when g is a left inverse of f
* pullbackFunctor             : (T, push I along f) ⟶ (S,I) when (f,g) are two-sided inverses

Together these give a round-trip equivalence in the split-isomorphism case.
-/

import ModularKernel
import Mathlib.Logic.Function.Basic

namespace ModularKernel

open Function

/-- A convenient package: f,g are two-sided inverses. -/
structure TwoSided {S T : Type*} (f : S → T) (g : T → S) : Prop :=
  (left  : LeftInverse g f)     -- g ∘ f = id_S
  (right : RightInverse g f)    -- f ∘ g = id_T

/-! ## Pushforward along a map with a section (left inverse) -/

/-- Push the ImpStruct `I` across `f` using a section `g` with `LeftInverse g f`. -/
def pushStruct {S T : Type*}
    (I : ImpStruct S) (f : S → T) (g : T → S) (sec : LeftInverse g f) : ImpStruct T :=
{ self_repr := fun t u => I.self_repr (g t) (g u),
  diagonal   := fun (Q : T → Prop) => f (I.diagonal (fun s => Q (f s))),
  negation   := I.negation,
  trilemma   := I.trilemma }

/-- Key fiber-collapse lemma under a two-sided inverse. -/
lemma fiber_exists_iff_of_twoSided {S T : Type*}
    (f : S → T) (g : T → S) (ts : TwoSided f g) (P : S → Prop) (s : S) :
    (∃ s', f s' = f s ∧ P s') ↔ P s := by
  constructor
  · intro h
    rcases h with ⟨s', hs, Ps'⟩
    -- From f s' = f s, derive g (f s') = g (f s)
    have heq : g (f s') = g (f s) := congrArg g hs
    -- Use g ∘ f = id_S to get s' = s
    rw [ts.left s', ts.left s] at heq
    rw [← heq]
    exact Ps'
  · intro Ps
    exact ⟨s, rfl, Ps⟩

/-- Pushforward functor - temporarily with sorry for diagonal preservation. -/
def pushFunctor' {S T : Type*}
    (I : ImpStruct S) (f : S → T) (g : T → S) (_sec : LeftInverse g f)
    : ImpFunctor I (pushStruct I f g _sec) :=
{ map := f,
  preserves_self_repr := by
    intro x y; constructor
    · intro h; simpa [pushStruct, _sec x, _sec y] using h
    · intro h; simpa [pushStruct, _sec x, _sec y] using h,
  preserves_diagonal := by
    intro P
    have hfun : (fun s => ∃ s', f s' = f s ∧ P s') = P := by
      funext s
      apply propext
      constructor
      · intro h
        rcases h with ⟨s', hs, Ps'⟩
        have : g (f s') = g (f s) := congrArg g hs
        have hss : s' = s := by simpa [(_sec s'), (_sec s)] using this
        simpa [hss] using Ps'
      · intro Ps
        exact ⟨s, rfl, Ps⟩
    simpa [pushStruct] using congrArg (fun Q => f (I.diagonal Q)) hfun.symm }

/-! ## Pullback functor back to the source (requires two-sided inverse) -/

/-- Pullback functor `(T, pushStruct I f g left) ⟶ (S,I)` using `g`,
requiring also `RightInverse f g` so that diagonals line up. -/
def pullbackFunctor {S T : Type*}
    (I : ImpStruct S) (f : S → T) (g : T → S)
    (ts : TwoSided f g)
    : ImpFunctor (pushStruct I f g ts.left) I :=
{ map := g,
  preserves_self_repr := by
    intro t u; constructor <;> intro h <;> simpa [pushStruct] using h,
  preserves_diagonal := by
    intro Q
    have hfun : (fun s => Q (f s)) = (fun s => ∃ t, g t = s ∧ Q t) := by
      funext s
      apply propext
      constructor
      · intro hQs
        exact ⟨f s, by simpa [ts.left s], hQs⟩
      · intro h
        rcases h with ⟨t, hgs, Qt⟩
        have : f (g t) = f s := by
          simpa [hgs] using congrArg f hgs
        have htf : t = f s := by
          simpa [ts.right t] using this
        simpa [htf] using Qt
    -- Chain equalities explicitly
    calc
      g ((pushStruct I f g ts.left).diagonal Q)
          = g (f (I.diagonal (fun s => Q (f s)))) := rfl
      _ = I.diagonal (fun s => Q (f s)) := by
          simpa using ts.left (I.diagonal (fun s => Q (f s)))
      _ = I.diagonal (fun s => ∃ t, g t = s ∧ Q t) := by
          simpa [hfun] using congrArg (fun R => I.diagonal R) hfun
      _ = I.diagonal (ImpFunctor.Push g Q) := rfl }

/-! ## Roundtrip stability in the split case -/

/-- With two-sided inverses, push then pull is roundtrip-stable on self_repr. -/
theorem roundtrip_stable_split
  {S T : Type*} {I : ImpStruct S} {f : S → T} {g : T → S}
  (ts : TwoSided f g) :
  ∀ s : S,
    I.self_repr s s ↔
    I.self_repr ((pullbackFunctor I f g ts).map ((pushFunctor' I f g ts.left).map s))
                ((pullbackFunctor I f g ts).map ((pushFunctor' I f g ts.left).map s)) := by
  intro s
  -- pullbackFunctor.map = g, pushFunctor'.map = f
  -- So: g (f s) = s by left inverse ts.left
  simp only [pullbackFunctor, pushFunctor', ts.left s]

@[simp] def pushStruct_id {S} (I : ImpStruct S) :
    pushStruct I (id : S → S) (id : S → S) (by intro x; rfl) = I := rfl

@[simp] def pushFunctor_id {S} (I : ImpStruct S) :
    pushFunctor' I (id : S → S) (id : S → S) (by intro x; rfl) = ImpFunctor.id I := rfl

end ModularKernel

