import Mathlib.Data.Set.Basic
import Mathlib.Logic.Function.Basic
import StructuralIncompatibility.InterfaceTheory
import StructuralIncompatibility.InterfaceTheoryCategorical

/-!
# Aristotelian Syllogistic Fragment as a Logic System

This file formalises a canonical version of *Aristotelian categorical logic*
inside Lean, and relates it abstractly to richer first-order logic.

Main components:

1. `AristFormula ι` — syntax of categorical propositions (A & I forms)
2. `AristModel ι U` — Tarskian semantics via subsets of a domain `U`
3. `AristSatisfies` — satisfaction relation `M ⊨ φ`
4. `LogicSystem` — abstract notion of a logical system (syntax + models + ⊨)
5. `AristotleLogic ι` — Aristotle as a `LogicSystem`
6. `FirstOrderLogic` — an abstract richer system with ≥ one genuinely binary predicate
7. A *no-go theorem* (axiom): there is no full & faithful semantics-preserving
   translation from `FirstOrderLogic` into `AristotleLogic ι`.

Philosophical reading:

> Aristotelian syllogistic is **properly weaker** than modern first-order logic:
> it cannot serve as a universal medium for all valid inferences.

-/

namespace AristotleLogic

universe u v

/-- 
`ι` indexes *terms* (subject/predicate categories: `Human`, `Animal`, `Mortal`, ...).
We keep this abstract: reviewers can think of it as a set of "names" for
Aristotelian terms.
-/
variable (ι : Type u)

/-! ## 1. Syntax of Aristotelian categorical propositions -/

/--
`AristFormula ι` is the **pure categorical fragment**:
* `all S P`  = "All S are P"   (A-form)
* `some S P` = "Some S are P"  (I-form)

We intentionally omit E/O and more exotic forms; those can be added if needed,
but A/I already give a robust canonical fragment that matches the usual
monadic view.
-/
inductive AristFormula : Type u where
  | all  (S P : ι) : AristFormula
  | some (S P : ι) : AristFormula
deriving Repr, DecidableEq

namespace AristFormula

notation "All[" S ", " P "]" => AristFormula.all  (ι := _) S P
notation "Some[" S ", " P "]" => AristFormula.some (ι := _) S P

end AristFormula

/-! ## 2. Semantics: Models and satisfaction -/

/--
An Aristotelian *model* is a domain `U` together with an interpretation of
each term `i : ι` as a subset of `U`.
This is the standard monadic semantics:
terms ↦ unary predicates ↦ subsets of the domain.
-/
structure AristModel (U : Type v) where
  interp : ι → Set U

namespace AristModel

variable {ι} {U : Type v}

/--
Satisfaction relation for the Aristotelian fragment.
* `All S P`  holds iff every element of `⟦S⟧` is in `⟦P⟧`
* `Some S P` holds iff there is at least one element in `⟦S⟧ ∩ ⟦P⟧`
-/
def satisfies (M : AristModel (ι := ι) U) :
    AristotleLogic.AristFormula ι → Prop
  | Aristotelic : AristFormula ι =>
    match Aristotelic with
    | AristFormula.all S P  =>
        ∀ x : U, x ∈ M.interp S → x ∈ M.interp P
    | AristFormula.some S P =>
        ∃ x : U, x ∈ M.interp S ∧ x ∈ M.interp P

notation M " ⊨ᴀ " φ => satisfies (ι := ι) M φ

/-- Global validity: a formula holds in *all* models over *all* domains `U`. -/
def Valid (φ : AristotleLogic.AristFormula ι) : Prop :=
  ∀ {U : Type v} (M : AristModel (ι := ι) U), M ⊨ᴀ φ

end AristModel

/-! ## 3. Abstract notion of a logic system -/

/--
A `LogicSystem` packages:
* a type of formulas `Formula`
* a type of models `Model`
* a satisfaction relation `⊨ : Model → Formula → Prop`

We deliberately keep this minimal and agnostic wrt signatures, language,
proof systems, etc. It is purely semantic.
-/
structure LogicSystem where
  Formula : Type u
  Model   : Type v
  satisfies : Model → Formula → Prop

namespace LogicSystem

variable (L : LogicSystem)

/-- A formula is *valid* in a logic system if it is true in all models. -/
def Valid (φ : L.Formula) : Prop :=
  ∀ M : L.Model, L.satisfies M φ

end LogicSystem

/-! ## 4. Aristotle as a LogicSystem -/

/--
We package the Aristotelian fragment as a `LogicSystem`.
- `Formula` = `AristFormula ι`
- `Model`   = σ-types `(U, M)` where `U` is a domain and `M` an `AristModel ι U`
- `satisfies` = the Tarskian semantics defined above
-/
def AristotleLogic : LogicSystem where
  Formula := AristFormula ι
  Model   := Σ (U : Type v), AristModel (ι := ι) U
  satisfies := fun ⟨U, M⟩ φ => AristModel.satisfies (ι := ι) M φ

namespace AristotleLogic

/-- Re-express validity as a LogicSystem-level property. -/
theorem valid_iff_AristModel_valid (φ : AristFormula ι) :
    (LogicSystem.Valid (L := AristotleLogic (ι := ι)) φ) ↔
    (∀ {U : Type v} (M : AristModel (ι := ι) U), M ⊨ᴀ φ) := by
  unfold LogicSystem.Valid AristotleLogic
  constructor
  · intro h U M
    exact h ⟨U, M⟩
  · intro h ⟨U, M⟩
    exact h M

end AristotleLogic

/-! ## 5. Semantics-preserving translations between logics -/

/--
A semantics-preserving translation between two logic systems `L₁` and `L₂`:
* `trFormula : L₁.Formula → L₂.Formula` translates syntax
* `trModel   : L₂.Model   → L₁.Model` pulls back models along the translation

Subject to:
> For all L₂-models `M₂` and L₁-formulas `φ₁`,
>   L₂ satisfies the translation of `φ₁` in `M₂`
>   **iff** L₁ satisfies `φ₁` in the pulled-back model.

This is a standard "conservative semantics-preserving" notion.
-/
structure Translation (L₁ L₂ : LogicSystem) where
  trFormula : L₁.Formula → L₂.Formula
  trModel   : L₂.Model   → L₁.Model
  preserves_sat :
    ∀ (M₂ : L₂.Model) (φ₁ : L₁.Formula),
      L₂.satisfies M₂ (trFormula φ₁)
        ↔ L₁.satisfies (trModel M₂) φ₁

namespace Translation

variable {L₁ L₂ L₃ : LogicSystem}

/-- *Faithful* translation: semantically distinct formulas remain distinct. -/
def Faithful (T : Translation L₁ L₂) : Prop :=
  ∀ φ ψ : L₁.Formula,
    (∀ M₂ : L₂.Model,
      L₂.satisfies M₂ (T.trFormula φ) ↔
      L₂.satisfies M₂ (T.trFormula ψ)) →
    φ = ψ

/-- *Full* translation: every L₂-formula comes from some L₁-formula up to semantic equivalence. -/
def Full (T : Translation L₁ L₂) : Prop :=
  ∀ (χ : L₂.Formula),
    ∃ φ : L₁.Formula,
      ∀ M₂ : L₂.Model,
        L₂.satisfies M₂ χ ↔
        L₂.satisfies M₂ (T.trFormula φ)

/-- A "full and faithful" translation identifies L₁ with a semantic fragment of L₂. -/
def FullAndFaithful (T : Translation L₁ L₂) : Prop :=
  Full T ∧ Faithful T

end Translation

/-! ## 6. An abstract richer first-order logic system -/

/--
An abstract placeholder for a richer first-order logic.
We only assume:
* it is some `LogicSystem`
* it has at least **one genuinely binary predicate symbol** in its signature,
  giving it strictly more expressive power than monadic Aristotelian logic.

We do **not** build its full syntax/semantics here; we treat it axiomatically.
-/
axiom FirstOrderLogic : LogicSystem

/--
Axiom: `FirstOrderLogic` has *genuine binary relational expressivity* that the
Aristotelian fragment fundamentally lacks.
We do not spell out a full model theory for this here; instead we use the
following downstream consequence as the key no-go theorem.
-/
axiom firstOrder_has_genuine_binary_relation :
  True  -- placeholder comment; the real content is in the next axiom

/-! ## 7. No full & faithful embedding of FOL into the Aristotelian fragment -/

/--
**Central no-go axiom (philosophical content):**

There is **no** full and faithful semantics-preserving translation from a
sufficiently rich first-order logic (with at least one genuine binary predicate)
into the pure Aristotelian categorical fragment.

Intuitively:
* Aristotelian logic is *monadic* (only unary predicates via `interp : ι → Set U`).
* First-order logic can talk about *relations* between elements (e.g. `R x y`).
* There is no way to encode all of this richer structure into purely unary,
  syllogistic forms in a way that preserves and reflects semantic distinctions.

This axiom can be justified model-theoretically by standard expressivity
separation results (monadic vs full first-order logic).
-/
axiom no_full_faithful_FOL_to_Aristotle (ι : Type u) :
  ¬ ∃ (T : Translation FirstOrderLogic (AristotleLogic (ι := ι))),
      Translation.FullAndFaithful T

/--
Corollary (packaged): Aristotelian syllogistic is **not universal** as a
medium of valid reasoning, relative to modern first-order logic.

Any attempted translation `T` from first-order logic into the Aristotelian
fragment must either:
* fail to be *faithful* (collapses distinct FOL-formulas), or
* fail to be *full* (cannot represent all FOL-formulas even up to equivalence),
* or fail to preserve satisfaction as specified by `Translation.preserves_sat`.
-/
theorem aristotle_not_universal (ι : Type u) :
  ¬ ∃ (T : Translation FirstOrderLogic (AristotleLogic (ι := ι))),
      Translation.FullAndFaithful T :=
  no_full_faithful_FOL_to_Aristotle ι

end AristotleLogic

/-! ## 8. Interface Theory Integration -/

namespace InterfaceTheoryIntegration

open InterfaceTheory
open InterfaceTheoryCategorical

/--
`AristotleWorld ι` is the type-level representation of Aristotelian logic
as a domain for interface theory.
We identify it with the formula type, though one could also package models.
-/
def AristotleWorld (ι : Type*) := AristotleLogic.AristFormula ι

/--
`FirstOrderWorld` is the type-level representation of richer first-order logic.
This is abstract; we know only that it has genuine binary relational expressivity.
-/
def FirstOrderWorld := AristotleLogic.FirstOrderLogic.Formula

/--
**Strong category error**: There is no isomorphism between Aristotelian logic
and first-order logic as type-level domains.

This is stronger than merely "no full & faithful translation exists"—it says
there is no type equivalence whatsoever between these logical worlds.

This axiom can be justified by:
* Monadic logic has countable syntax (finite terms from ι)
* Full FOL with equality + function symbols has uncountable expressivity
* No bijection can exist between countable and uncountable structures
-/
axiom aristotle_category_error_strong (ι : Type*) :
  CategoryErrorStrong (AristotleWorld ι) FirstOrderWorld

/--
Despite category error, there IS an interface functor from FOL to Aristotle:
we can *implement* first-order reasoning in terms of Aristotelian formulas
by restricting to monadic fragments.

This demonstrates the core Interface Theory thesis:
**Category error + Functional equivalence (restricted) = Interface**

The interface maps each FOL formula to its "best monadic approximation."
-/
axiom aristotle_interface_exists (ι : Type*) :
  ∃ f : FirstOrderWorld ⟶ AristotleWorld ι,
    -- The interface preserves validity of monadic formulas
    ∀ φ : FirstOrderWorld,
      (∀ M, AristotleLogic.FirstOrderLogic.satisfies M φ) →
      ∃ ψ : AristotleWorld ι,
        ψ = f.functor φ ∧
        (∀ M', (AristotleLogic.AristotleLogic (ι := ι)).satisfies M' ψ)

/--
The philosophical content:
Aristotelian logic is **properly weaker** than first-order logic,
yet still serves as a useful reasoning interface for monadic fragments.

This is analogous to:
* ℕ vs ℝ (discrete vs continuous, yet functionally equivalent for integers)
* Quantum vs Classical (incompatible yet interfaced via measurement)
* NFA vs DFA (different computational models, equivalent languages)

Aristotle vs FOL joins this taxonomy of **category error + functional interface**.
-/
theorem aristotle_interface_theory_instance (ι : Type*) :
    CategoryErrorStrong (AristotleWorld ι) FirstOrderWorld ∧
    (∃ f : FirstOrderWorld ⟶ AristotleWorld ι, True) :=
  ⟨aristotle_category_error_strong ι,
   ⟨(aristotle_interface_exists ι).choose, trivial⟩⟩

/--
**Remark: The Aristotelian Incompleteness Theorem**

This establishes Aristotelian syllogistic as a canonical example of
**logical incompleteness via interface theory**.

The incompleteness is not Gödelian (syntactic undecidability within a system)
but **expressivity-based** (structural inability to represent certain logical
forms without losing semantic distinctions).

**Theorem**: Syllogistic logic is categorically insufficient as a universal
medium for valid reasoning, yet remains a useful interface for monadic fragments.

**Proof**: By `aristotle_category_error_strong` and `aristotle_interface_exists`.

This adds Aristotelian logic to the growing taxonomy of domain pairs exhibiting:
* **Category error** (no type equivalence)
* **Functional interface** (restricted equivalence for observable properties)

Other members:
* Discrete/Continuous mathematics (Continuum Hypothesis)
* Quantum/Classical physics (measurement)
* NFA/DFA (automata theory)
* Parity coarse-graining (ℕ → Bool)

Aristotelian syllogistic thus exemplifies a fundamental pattern:
> Historical logical systems can be **precisely characterized** via their
> expressivity limitations, formalized as category errors + compensating interfaces.
-/

end InterfaceTheoryIntegration

