/-
  Core/DecorationFibre.lean

  Decoration fibres as groupoids:
  - Raw decoration space with gauge/redundancy group action
  - Physical fibre = orbit groupoid quotient
  - Invariant functions on fibres (derived observables like CKM)
-/

import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Groupoid
import Mathlib.GroupTheory.GroupAction.Basic
import ImpossibilityTheory.Mathematics.Core.Contingency

namespace ImpossibilityTheory.Mathematics

open CategoryTheory

universe u v

variable {C : Type u} [Category.{u} C]

/-!
## Decoration Fibres with Gauge Redundancy

A decoration fibre consists of:
1. Raw decoration space (e.g., Yukawa matrices)
2. Redundancy group (e.g., flavour transformations)
3. Group action on decorations
4. Physical fibre = orbit space (groupoid quotient)
-/

/-- A decoration fibre with gauge/redundancy structure.

This captures the full structure of contingent parameters:
- `Raw` is the space of all decorations (e.g., Yukawa matrices)
- `RedundancyGroup` is the group of basis changes (e.g., U(3)^n)
- `action` is how the redundancy acts on raw decorations -/
structure DecorationFibre (obs : FunctorialObstructionSet C) where
  /-- Raw decoration space for each model. -/
  Raw : Model obs → Type u
  /-- Redundancy group for each model (e.g., flavour transformations). -/
  RedundancyGroup : Model obs → Type u
  /-- Group structure on RedundancyGroup. -/
  [grp : ∀ M, Group (RedundancyGroup M)]
  /-- Group action of redundancy on raw decorations. -/
  [act : ∀ M, MulAction (RedundancyGroup M) (Raw M)]

attribute [instance] DecorationFibre.grp DecorationFibre.act

namespace DecorationFibre

variable {obs : FunctorialObstructionSet C}

/-- Two raw decorations are gauge-equivalent if related by a redundancy transformation. -/
def GaugeEquiv (F : DecorationFibre obs) (M : Model obs) (d₁ d₂ : F.Raw M) : Prop :=
  ∃ g : F.RedundancyGroup M, g • d₁ = d₂

/-- GaugeEquiv is an equivalence relation. -/
theorem gaugeEquiv_equiv (F : DecorationFibre obs) (M : Model obs) :
    Equivalence (F.GaugeEquiv M) where
  refl d := ⟨1, one_smul _ d⟩
  symm := fun ⟨g, hg⟩ => ⟨g⁻¹, by simp [← hg]⟩
  trans := fun ⟨g, hg⟩ ⟨h, hh⟩ => ⟨h * g, by simp [← hg, ← hh, mul_smul]⟩

/-- The physical fibre: gauge orbits in the raw decoration space.

This is the quotient by redundancy, i.e., `[Raw(M) / RedundancyGroup(M)]`. -/
def PhysicalFibre (F : DecorationFibre obs) (M : Model obs) : Type u :=
  Quotient (Setoid.mk (F.GaugeEquiv M) (F.gaugeEquiv_equiv M))

/-- Project a raw decoration to its physical (gauge-invariant) class. -/
def toPhysical (F : DecorationFibre obs) (M : Model obs) : F.Raw M → F.PhysicalFibre M :=
  Quotient.mk _

/-- A gauge-invariant function: descends to the physical fibre. -/
structure GaugeInvariant (F : DecorationFibre obs) (M : Model obs) (α : Type v) where
  /-- The underlying function on raw decorations. -/
  fn : F.Raw M → α
  /-- Invariance under gauge transformations. -/
  invariant : ∀ g : F.RedundancyGroup M, ∀ d : F.Raw M, fn (g • d) = fn d

/-- A gauge-invariant function induces a function on the physical fibre. -/
def GaugeInvariant.descend {F : DecorationFibre obs} {M : Model obs} {α : Type v}
    (f : GaugeInvariant F M α) : F.PhysicalFibre M → α :=
  Quotient.lift f.fn (fun _ _ ⟨g, hg⟩ => by rw [← hg, f.invariant])

end DecorationFibre

/-!
## Derived Invariants

Invariant quantities computed from the fibre (e.g., CKM from Yukawas).
-/

/-- A derived invariant: a gauge-invariant function on a decoration fibre.

Examples: CKM matrix from Yukawa matrices, Higgs mass from potential parameters. -/
structure DerivedInvariant (F : DecorationFibre obs) where
  /-- Target type of the invariant. -/
  Target : Model obs → Type u
  /-- The invariant function for each model. -/
  compute : ∀ M : Model obs, F.GaugeInvariant M (Target M)

/-- A derived invariant yields a function on physical fibres. -/
def DerivedInvariant.onPhysical {F : DecorationFibre obs} (inv : DerivedInvariant F)
    (M : Model obs) : F.PhysicalFibre M → inv.Target M :=
  (inv.compute M).descend

/-!
## The Fibre Theorem

Structural resolution fixes the base; decorations are coordinates on fibres.
-/

/-- The fibre non-uniqueness theorem:

If the physical fibre is non-trivial (more than one orbit), then the decoration
is not determined by obstruction resolution alone.

This is the formal statement that CKM angles, Higgs mass, etc. are not
structurally forced. -/
theorem fibre_nonuniqueness (F : DecorationFibre obs) (M : Model obs)
    (h : ∃ p q : F.PhysicalFibre M, p ≠ q) :
    ∃ d₁ d₂ : F.Raw M, ¬ F.GaugeEquiv M d₁ d₂ := by
  obtain ⟨p, q, hpq⟩ := h
  obtain ⟨d₁, rfl⟩ := Quotient.exists_rep p
  obtain ⟨d₂, rfl⟩ := Quotient.exists_rep q
  use d₁, d₂
  intro ⟨g, hg⟩
  apply hpq
  exact Quotient.sound ⟨g, hg⟩

/-- Decoration is a fibre over the resolved model: projection is forgetful. -/
def DecorationFibre.asDecoration (F : DecorationFibre obs) : Decoration obs where
  Param M := F.PhysicalFibre M

end ImpossibilityTheory.Mathematics
