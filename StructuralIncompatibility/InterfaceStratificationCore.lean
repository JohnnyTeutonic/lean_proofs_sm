import Mathlib.Data.Nat.Basic
import Mathlib.Logic.Function.Basic
import InterfaceTheory
import InterfaceTheoryCategorical

/-!
# Stratifications of Interface Levels

This file builds three things:

1. A general notion of **stratification** of types by interfaces,
   plus the **trivial identity tower** as a canonical example.

2. An **epistemic presheaf** over a stratification: we lift
   the `GlobalEpistemicStructure` from `InterfaceTheoryCategorical`
   to a level-indexed, contravariant stability assignment.

3. A **strict bicategory-style structure** of stratifications:
   - objects: stratifications,
   - 1-morphisms: levelwise interface maps commuting with the steps,
   - 2-morphisms: pointwise equalities between those families.

Everything is expressed in terms of your existing `InterfaceFunctor`,
`functional_equivalence`, and `GlobalEpistemicStructure`.
-/

open InterfaceTheory
open InterfaceTheoryCategorical

namespace InterfaceStratification

/-! ############################################################
## 1. Basic Definition of a Stratification
############################################################# -/

/--
A *stratification* is an ω-indexed tower of types
    Level 0, Level 1, Level 2, ...
equipped with interfaces between successive levels:
    step n : Level n ⟶ Level (n+1)
where `β ⟶ α` is your existing `InterfaceFunctor α β`
(read "β is implemented inside α").

We deliberately do **not** add extra axioms (no size conditions,
no special properties) here: just the bare tower with its steps.
-/
structure Stratification where
  /-- The type at each level of the hierarchy. -/
  Level : ℕ → Type*
  /-- The interface from level n to level n+1. -/
  step  : ∀ n : ℕ, Level n ⟶ Level (n+1)

namespace Stratification

variable (S : Stratification)

/--
Iterated interface map along the stratification:
from level `m` to level `n` for any `m ≤ n`.

This is the "composite interface" obtained by chaining
all steps from `m` up to `n-1`.
-/
def stepIter : ∀ {m n : ℕ}, m ≤ n → S.Level m ⟶ S.Level n
  | m, n, h =>
    match n, h with
    | _, Nat.le_refl _ =>
        interfaceId (S.Level m)
    | n+1, Nat.succ_le_succ h' =>
        -- First go m ⟶ n, then apply the step n ⟶ n+1.
        (S.stepIter h') ≫ (S.step n)

@[simp]
lemma stepIter_refl (m : ℕ) :
    S.stepIter (m := m) (n := m) (Nat.le_refl m)
      = interfaceId (S.Level m) := rfl

@[simp]
lemma stepIter_succ {m n : ℕ} (h : m ≤ n) :
    S.stepIter (m := m) (n := n+1) (Nat.succ_le_succ h)
      = S.stepIter (m := m) (n := n) h ≫ S.step n := rfl

end Stratification

/-! ############################################################
## 1.a The Trivial Identity Tower
############################################################# -/

/--
The trivial "identity" stratification on a type `α`:
- every level is literally `α`
- every step is the identity interface.
-/
def IdentityStratification (α : Type*) : Stratification :=
{ Level := fun _ => α,
  step  := fun _ => interfaceId α }

namespace IdentityStratification

@[simp]
theorem level (α : Type*) (n : ℕ) :
    (IdentityStratification α).Level n = α := rfl

@[simp]
theorem step (α : Type*) (n : ℕ) :
    (IdentityStratification α).step n = interfaceId α := rfl

end IdentityStratification

/-! ############################################################
## 2. Functional Equivalence Along a Stratification
############################################################# -/

/--
A single step in a stratification has **functional equivalence**
if the interface between those two levels witnesses your
`functional_equivalence` notion.
-/
def StepFunctionalEquivalence (S : Stratification) (n : ℕ) : Prop :=
  functional_equivalence (S.Level n) (S.Level (n+1))

/--
If every step of a stratification has `functional_equivalence`,
then *any* two levels with `m ≤ n` are functionally equivalent.

This is the "climb the tower" theorem:
  Level m  → Level (m+1) → ... → Level n
-/
theorem functional_equivalence_chain
    (S : Stratification)
    (hstep : ∀ n, StepFunctionalEquivalence S n)
    (m n : ℕ) (h : m ≤ n) :
    functional_equivalence (S.Level m) (S.Level n) := by
  induction h with
  | refl =>
      -- m = n: reflexivity axiom from InterfaceTheory
      simpa using functional_equivalence_refl (S.Level m)
  | step hmn ih =>
      -- m ≤ n → m ≤ n+1 by composition
      have hstep_n : functional_equivalence (S.Level n) (S.Level (n+1)) :=
        hstep n
      exact functional_equivalence_trans ih hstep_n

/--
Special case: functional equivalence from level 0 to any level `n`
when all steps are functionally equivalent.
-/
theorem functional_equivalence_from_zero
    (S : Stratification)
    (hstep : ∀ n, StepFunctionalEquivalence S n)
    (n : ℕ) :
    functional_equivalence (S.Level 0) (S.Level n) :=
  functional_equivalence_chain S hstep 0 n (Nat.zero_le n)

/-! ############################################################
## 3. Epistemic Stability as a Stratified Presheaf
############################################################# -/

/--
A *stratified epistemic structure* takes a global epistemic-stability
assignment and requires **non-expansiveness along the stratification
steps**.

Intuitively: going "up a level" (via a step interface) cannot *increase*
stability of properties when transported along that interface.
This is precisely the contravariant behaviour you want.
-/
structure StratifiedEpistemic (S : Stratification) where
  G : GlobalEpistemicStructure
  nonexpansive_step :
    ∀ n : ℕ,
      respects_interface
        (G.E (S.Level (n+1)))
        (G.E (S.Level n))
        (S.step n)

namespace StratifiedEpistemic

variable {S : Stratification} (SE : StratifiedEpistemic S)

/-- Stability of a property `P` at level `n`. -/
def levelStability (n : ℕ) (P : S.Level n → Prop) : Stability :=
  (SE.G.E (S.Level n)).stab P

/--
Non-expansiveness along a *single* step, in the explicit form:
Pulling back a property `Q` on level `n+1` along the step
does not increase its stability score at level `n`.
-/
theorem step_nonexpansive (n : ℕ)
    (Q : S.Level (n+1) → Prop) :
    SE.levelStability n (fun x => Q ((S.step n).functor x))
      ≤ SE.levelStability (n+1) Q := by
  -- `respects_interface` is phrased with the inequality
  --   Eβ.stab (P ∘ f) ≤ Eα.stab P
  -- where `f : β ⟶ α`.
  -- Here α = Level (n+1), β = Level n, f = step n.
  have h := SE.nonexpansive_step n Q
  -- Note direction: respects_interface (Eα) (Eβ) (f)
  -- says: Eβ.stab (P ∘ f) ≤ Eα.stab P.
  -- So we just rewrite with the definitions:
  dsimp [levelStability] at *
  -- `h` is exactly the inequality we want, but with arguments in the
  -- order expected by `respects_interface`.
  simpa using h

end StratifiedEpistemic

/--
The **canonical** stratified epistemic structure:
just reuse `canonicalGlobalEpistemicStructure` from
`InterfaceTheoryCategorical` and observe that it is already
non-expansive for every interface (hence for every stratification
step).
-/
def canonicalStratifiedEpistemic (S : Stratification) : StratifiedEpistemic S :=
{ G := canonicalGlobalEpistemicStructure,
  nonexpansive_step := by
    intro n
    exact canonical_respects_interface (S.step n) }

/-! ############################################################
## 4. Bicategory-Style Structure on Stratifications
############################################################# -/

/--
A morphism of stratifications `F : S ⟶ T` is given by:
- a family of interfaces `mapLevel n : S.Level n ⟶ T.Level n`,
- such that the squares formed with the step interfaces commute:

      S.Level n   --step-->   S.Level (n+1)
        |                         |
      mapLevel n               mapLevel (n+1)
        |                         |
        v                         v
      T.Level n   --step-->   T.Level (n+1)
-/
structure StratificationHom (S T : Stratification) where
  mapLevel : ∀ n : ℕ, S.Level n ⟶ T.Level n
  commute  : ∀ n : ℕ,
    (S.step n) ≫ (mapLevel (n+1))
      =
    (mapLevel n) ≫ (T.step n)

namespace StratificationHom

variable {S T U : Stratification}

/-- Identity morphism of a stratification. -/
def id (S : Stratification) : StratificationHom S S where
  mapLevel := fun n => interfaceId (S.Level n)
  commute  := by
    intro n
    -- All maps are identities, so the square commutes definitionally.
    simp [interface_strict_left_unit, interface_strict_right_unit]

@[simp]
lemma id_mapLevel (S : Stratification) (n : ℕ) :
    (id S).mapLevel n = interfaceId (S.Level n) := rfl

/--
Horizontal composition of morphisms of stratifications.
Levelwise composition of the interface maps, and check the
commuting square by associativity.
-/
def comp (F : StratificationHom S T) (G : StratificationHom T U) :
    StratificationHom S U where
  mapLevel := fun n => F.mapLevel n ≫ G.mapLevel n
  commute  := by
    intro n
    -- We need: (S.step n ≫ F.mapLevel (n+1) ≫ G.mapLevel (n+1))
    --          = (F.mapLevel n ≫ T.step n ≫ G.mapLevel (n+1))
    -- and use the commuting squares for F and G.
    have hF := F.commute n
    have hG := G.commute n
    -- Rewrite both sides using associativity and these equalities.
    -- Left side:
    calc
      (S.step n ≫ (F.mapLevel (n+1) ≫ G.mapLevel (n+1)))
          = (S.step n ≫ F.mapLevel (n+1)) ≫ G.mapLevel (n+1) := by
              simp [interface_strict_assoc]
      _   = ((F.mapLevel n) ≫ T.step n) ≫ G.mapLevel (n+1) := by
              simpa [interface_strict_assoc] using congrArg (fun f => f ≫ G.mapLevel (n+1)) hF
      _   = (F.mapLevel n) ≫ (T.step n ≫ G.mapLevel (n+1)) := by
              simp [interface_strict_assoc]
      _   = (F.mapLevel n) ≫ (G.mapLevel n ≫ U.step n) := by
              simpa [interface_strict_assoc] using congrArg (fun f => F.mapLevel n ≫ f) hG
      _   = (F.mapLevel n ≫ G.mapLevel n) ≫ U.step n := by
              simp [interface_strict_assoc]

infixr:80 " ⊚ " => comp

end StratificationHom

/-!
### 2-Morphisms: pointwise equalities between levelwise interfaces
-/

/--
A 2-morphism between stratification morphisms is just pointwise
equality of their levelwise interfaces.
-/
structure Stratification2Morphism
    {S T : Stratification}
    (F G : StratificationHom S T) where
  hom_eq : ∀ n : ℕ, F.mapLevel n.functor = G.mapLevel n.functor

namespace Stratification2Morphism

variable {S T U : Stratification}

/-- Vertical composition of 2-morphisms (just transitivity of equality). -/
def vcomp {F G H : StratificationHom S T}
    (η : Stratification2Morphism F G)
    (θ : Stratification2Morphism G H) :
    Stratification2Morphism F H :=
{ hom_eq := fun n => by
    trans G.mapLevel n.functor <;> [apply η.hom_eq, apply θ.hom_eq] }

/-- Horizontal composition of 2-morphisms (compatibility with `≫`). -/
def hcomp
    {F₁ G₁ : StratificationHom S T}
    {F₂ G₂ : StratificationHom T U}
    (η₁ : Stratification2Morphism F₁ G₁)
    (η₂ : Stratification2Morphism F₂ G₂) :
    Stratification2Morphism (StratificationHom.comp F₁ F₂)
                            (StratificationHom.comp G₁ G₂) :=
{ hom_eq := fun n => by
    -- We need equality of underlying functions of:
    --   (F₁.mapLevel n ≫ F₂.mapLevel n) and (G₁.mapLevel n ≫ G₂.mapLevel n)
    funext x
    -- expand compositions and use η₁, η₂ pointwise
    simp [StratificationHom.comp, interfaceComp_functor,
          η₁.hom_eq n, η₂.hom_eq n] }

/-- Identity 2-morphism on a stratification morphism. -/
def id (F : StratificationHom S T) : Stratification2Morphism F F :=
{ hom_eq := fun _ => rfl }

end Stratification2Morphism

/-!
We now have:
- Objects: `Stratification`
- 1-Morphisms: `StratificationHom`
- 2-Morphisms: `Stratification2Morphism`

with composition and identities defined. Coherence (associativity,
unit, interchange) follows from the strict associativity and unit
laws for `InterfaceFunctor`; we can package this into a "strict
bicategory" structure if needed, but the raw data is often enough
for applications.
-/

/-! ############################################################
## 5. Aristotle-style 3-level stratification
############################################################# -/

/--
An abstract Aristotle-style domain with three levels:
* `Sensible`  – level 0: concrete, particular substances
* `Rational`  – level 1: predicative / syllogistic level
* `Noetic`    – level 2+: pure noesis / highest "intellect" level

We also include "interpretation" maps which give the *intended*
interfaces between these levels.
-/
structure AristotleDomain where
  Sensible : Type*
  Rational : Type*
  Noetic   : Type*
  /-- Abstraction from sensible particulars to rational forms. -/
  abstr    : Sensible → Rational
  /-- Reflection from rational forms to noetic objects. -/
  reflect  : Rational → Noetic
  /-- Closure on the noetic level (can be the identity). -/
  close    : Noetic → Noetic

/--
The Aristotle-style stratification as an instance of `Stratification`:
- Level 0: `Sensible`
- Level 1: `Rational`
- Level n≥2: `Noetic` (stabilises at the noetic horizon)

Steps:
- `step 0`   : `Sensible ⟶ Rational` given by abstraction
- `step 1`   : `Rational ⟶ Noetic`   given by reflection
- `step n≥2` : `Noetic ⟶ Noetic`     given by `close`
-/
def AristotleStratification (A : AristotleDomain) : Stratification :=
{ Level := fun
    | 0       => A.Sensible
    | 1       => A.Rational
    | (_+2)   => A.Noetic,
  step := fun
    | 0       => ⟨A.abstr⟩
    | 1       => ⟨A.reflect⟩
    | (_+2)   => ⟨A.close⟩ }

namespace AristotleStratification

variable (A : AristotleDomain)

@[simp] lemma level_zero :
    (AristotleStratification A).Level 0 = A.Sensible := rfl

@[simp] lemma level_one :
    (AristotleStratification A).Level 1 = A.Rational := rfl

@[simp] lemma level_two :
    (AristotleStratification A).Level 2 = A.Noetic := rfl

@[simp] lemma level_ge_two (n : ℕ) :
    (AristotleStratification A).Level (n + 2) = A.Noetic := rfl

@[simp] lemma step_zero :
    (AristotleStratification A).step 0 = ⟨A.abstr⟩ := rfl

@[simp] lemma step_one :
    (AristotleStratification A).step 1 = ⟨A.reflect⟩ := rfl

@[simp] lemma step_ge_two (n : ℕ) :
    (AristotleStratification A).step (n + 2) = ⟨A.close⟩ := rfl

end AristotleStratification

/-! ############################################################
## 6. Aristotle: no self-predication at level 0, resolution above
############################################################# -/

/-- A would-be "self-predicate" over a type. -/
def SelfPredicate (α : Type*) := α → Prop

/--
`NoTruthComplete α` says:
> there is **no** self-predicate `T : α → Prop` which holds of *all*
> elements of `α`.

This is a very weak schematic way to capture Aristotle's idea that
the sensible level does not carry a global, self-complete truth-predicate.
-/
def NoTruthComplete (α : Type*) : Prop :=
  ¬ ∃ (T : SelfPredicate α), ∀ x : α, T x

/--
Axiom: on an Aristotle domain, the sensible level does *not* admit a
truth-complete self-predicate.
-/
axiom Aristotle_no_self_truth (A : AristotleDomain) :
  NoTruthComplete A.Sensible

/--
Axiom: there is at least one "noetic witness" – some object living
at the noetic level. This is a minimal way of saying the noetic
layer actually exists and is inhabited.
-/
axiom Aristotle_noetic_witness (A : AristotleDomain) :
  ∃ n : A.Noetic, True

/-! ############################################################
## 7. Aristotle steps are functionally resolving
############################################################# -/

/--
Axiom: the abstraction step from `Sensible` to `Rational` is
functionally equivalent in the sense of `InterfaceTheory`.

Intuition: for every satisfiable sensible property, there is a rational
representation that realises it.
-/
axiom Aristotle_step0_functional (A : AristotleDomain) :
  StepFunctionalEquivalence (AristotleStratification A) 0

/--
Axiom: the reflection step from `Rational` to `Noetic` is also
functionally equivalent.

Intuition: for every satisfiable rational predicate, there is a noetic
object implementing it.
-/
axiom Aristotle_step1_functional (A : AristotleDomain) :
  StepFunctionalEquivalence (AristotleStratification A) 1

/--
For all higher levels (n ≥ 2) the stratification has stabilised to
`Noetic`, and we can use reflexive functional equivalence on that type.
-/
lemma Aristotle_step_ge_two_functional (A : AristotleDomain) (n : ℕ) :
  StepFunctionalEquivalence (AristotleStratification A) (n + 2) := by
  -- For n+2 ≥ 2, both Level (n+2) and Level (n+3) are definitionally `A.Noetic`.
  have hFE : functional_equivalence A.Noetic A.Noetic :=
    functional_equivalence_refl A.Noetic
  -- Now just rewrite the levels to `A.Noetic`.
  -- Level (n+2) = A.Noetic, Level (n+3) = A.Noetic.
  change functional_equivalence
    ((AristotleStratification A).Level (n + 2))
    ((AristotleStratification A).Level (n + 3))
  simpa [AristotleStratification.level_ge_two] using hFE

/--
Collect all step-wise functional equivalences for the Aristotle stratification:
- step 0: by `Aristotle_step0_functional`
- step 1: by `Aristotle_step1_functional`
- step n≥2: by reflexivity on `Noetic`.
-/
lemma Aristotle_all_steps_functional (A : AristotleDomain) :
  ∀ n, StepFunctionalEquivalence (AristotleStratification A) n := by
  intro n
  cases n with
  | zero =>
      simpa using Aristotle_step0_functional A
  | succ n =>
      cases n with
      | zero =>
          -- n = 1
          simpa using Aristotle_step1_functional A
      | succ k =>
          -- n = k+2 ≥ 2
          simpa using Aristotle_step_ge_two_functional A k

/--
**Main chain theorem (Aristotle pattern):**

From the sensible level (0) to the noetic level (2),
there is functional equivalence in the sense of `InterfaceTheory`.

This uses only the step-wise functional equivalences plus reflexivity,
glued together via the general `functional_equivalence_chain` theorem.
-/
theorem Aristotle_sensible_to_noetic_functional_equivalence (A : AristotleDomain) :
  functional_equivalence A.Sensible A.Noetic := by
  let S := AristotleStratification A
  have hstep : ∀ n, StepFunctionalEquivalence S n :=
    Aristotle_all_steps_functional A
  -- Use the generic chain theorem from level 0 to level 2.
  have hFE := functional_equivalence_chain S hstep 0 2 (Nat.zero_le 2)
  -- Rewrite `Level 0` and `Level 2` to the underlying types.
  simpa [AristotleStratification.level_zero, AristotleStratification.level_two] using hFE

/--
A more "philosophical" framing:

If the sensible level lacks a truth-complete self-predicate
(`NoTruthComplete`) – an Aristotelian-style ban on self-truth –
then there nevertheless exists a noetic witness and a functional
equivalence between sensible and noetic.

This packages the two ingredients:
1. `Aristotle_no_self_truth A`   – expressive limitation at level 0
2. `Aristotle_sensible_to_noetic_functional_equivalence A`
   – resolution via higher stratification levels.
-/
theorem Aristotle_escape_self_reference (A : AristotleDomain) :
  NoTruthComplete A.Sensible →
  ∃ (meta : A.Noetic),
    functional_equivalence A.Sensible A.Noetic := by
  intro _
  obtain ⟨n, _⟩ := Aristotle_noetic_witness A
  refine ⟨n, ?_⟩
  exact Aristotle_sensible_to_noetic_functional_equivalence A

/-! ############################################################
## 8. Tarski-style internal truth predicates on the sensible level
############################################################# -/

/--
A minimal Tarski-style language whose "sentences" are coded
as elements of a type `α`, together with:
* `interp : α → Prop`  – the actual truth condition in the meta-theory
* `Definable : (α → Prop) → Prop` – which predicates on codes are
    themselves definable in the object-language.
-/
structure TarskiLanguage (α : Type*) where
  interp    : α → Prop
  Definable : (α → Prop) → Prop

/--
An *internal* truth predicate for a Tarski language `L` is a predicate
on sentence-codes which:
1. matches the meta-theoretic interpretation, and
2. is definable in the object-language.
-/
def InternalTruthPredicate {α : Type*}
    (L : TarskiLanguage α) (Tr : α → Prop) : Prop :=
  (∀ σ : α, Tr σ ↔ L.interp σ) ∧ L.Definable Tr

/--
Tarski-style undefinability: there is *no* internal truth predicate
for the language `L`.
-/
def NoInternalTruth {α : Type*} (L : TarskiLanguage α) : Prop :=
  ¬ ∃ Tr : α → Prop, InternalTruthPredicate L Tr

/--
An Aristotle domain equipped with a Tarski language whose sentence-codes
live on the *sensible* level.

This isolates the "Aristotle + internal language" configuration.
-/
structure AristotleSensibleLanguage (A : AristotleDomain) where
  L : TarskiLanguage A.Sensible

/--
Axiom: the Tarski language on the sensible level does *not* admit
an internal truth predicate. This is the clean Tarski-style sharpening
of `Aristotle_no_self_truth`.
-/
axiom Aristotle_tarski_undefinability
    (A : AristotleDomain) (Lang : AristotleSensibleLanguage A) :
    NoInternalTruth Lang.L

/--
Tarski-style escape theorem:

If the sensible-level language has no internal truth predicate
(`NoInternalTruth`), then there exists a noetic witness and a
functional-equivalence interface from `Sensible` to `Noetic`.

This is the same meta-resolution as before, now with a Tarski schema
as the "impossibility" assumption.
-/
theorem Aristotle_escape_Tarski
    (A    : AristotleDomain)
    (Lang : AristotleSensibleLanguage A) :
    NoInternalTruth Lang.L →
    ∃ (meta : A.Noetic),
      functional_equivalence A.Sensible A.Noetic := by
  intro _
  -- Use the same noetic witness and chain equivalence as before.
  obtain ⟨n, _⟩ := Aristotle_noetic_witness A
  refine ⟨n, ?_⟩
  exact Aristotle_sensible_to_noetic_functional_equivalence A

end InterfaceStratification
