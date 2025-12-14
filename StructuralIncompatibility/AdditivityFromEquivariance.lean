/-
AdditivityFromEquivariance.lean  (Lean 4, Mathlib-free)
Author: Jonathan Reich, October 2025

Goal:
  If an intertwiner J satisfies J ∘ flow(t) = flow(ρ t) ∘ J
  for a one-parameter flow with the Stone-style group law,
  and the flow is faithful "through J", then ρ is additive:
      ρ (s + t) = ρ s + ρ t.

This encodes the "equivariance ⇒ additivity" lemma abstractly,
ruling out nonlinear reparameterizations like t ↦ t^3 under the hypotheses.

Integration with quantum gravity framework:
- Complements NoetherLite (positive conservation kernel)
- Provides abstract version of QuantumGravityTheorems.additive_from_equivariance
- Shows the structural constraint: equivariant intertwiners force linearity
-/

namespace AdditivityFromEquivariance

/-- Bare-bones additive time signature. -/
structure AddTime where
  T     : Type
  zero  : T
  add   : T → T → T
  add_zero_left  : ∀ t, add zero t = t
  add_assoc      : ∀ r s t, add (add r s) t = add r (add s t)

/-- A one-parameter flow carrying the Stone-style laws: flow(0) = id, flow(s+t) = flow s ∘ flow t. -/
structure Flow (A : AddTime) (X : Type) where
  flow      : A.T → X → X
  flow_zero : ∀ x, flow A.zero x = x
  flow_add  : ∀ s t x, flow (A.add s t) x = flow s (flow t x)

/-- Equivariance of an intertwiner J with respect to a reparameterization ρ. -/
def Equivariant (A : AddTime) {X : Type} (Φ : Flow A X)
  (ρ : A.T → A.T) (J : X → X) : Prop :=
  ∀ t x, J (Φ.flow t x) = Φ.flow (ρ t) (J x)

/-- Faithfulness "through J":
    equality of flow-parameters is detected on the image of J. -/
def FaithfulThrough (A : AddTime) {X : Type} (Φ : Flow A X) (J : X → X) : Prop :=
  ∀ u v, (∀ x, Φ.flow u (J x) = Φ.flow v (J x)) → u = v

/-- Main lemma:
    Equivariance of J with respect to ρ + Stone laws + faithfulness through J
    force additivity of ρ. -/
theorem additive_from_equivariance
  (A : AddTime) {X : Type} (Φ : Flow A X)
  (ρ : A.T → A.T) (J : X → X)
  (hEqv : Equivariant A Φ ρ J)
  (hFaith : FaithfulThrough A Φ J) :
  ∀ s t, ρ (A.add s t) = A.add (ρ s) (ρ t) := by
  intro s t
  -- Compare J ∘ flow(s+t) with flow(ρ s + ρ t) ∘ J pointwise, then use faithfulness.
  apply hFaith (ρ (A.add s t)) (A.add (ρ s) (ρ t))
  intro x
  -- Left route: equivariance at (s+t)
  have L : J (Φ.flow (A.add s t) x) = Φ.flow (ρ (A.add s t)) (J x) := 
    hEqv (A.add s t) x
  -- Right route: equivariance at t then at s, using flow_add twice
  have R₁ : J (Φ.flow (A.add s t) x) = J (Φ.flow s (Φ.flow t x)) := by
    rw [Φ.flow_add]
  have R₂ : J (Φ.flow s (Φ.flow t x)) = Φ.flow (ρ s) (J (Φ.flow t x)) := 
    hEqv s (Φ.flow t x)
  have R₃ : J (Φ.flow t x) = Φ.flow (ρ t) (J x) := 
    hEqv t x
  have R : J (Φ.flow (A.add s t) x) = Φ.flow (A.add (ρ s) (ρ t)) (J x) := by
    -- chain the equalities and use flow_add on the RHS
    calc J (Φ.flow (A.add s t) x)
        = J (Φ.flow s (Φ.flow t x))           := R₁
      _ = Φ.flow (ρ s) (J (Φ.flow t x))       := R₂
      _ = Φ.flow (ρ s) (Φ.flow (ρ t) (J x))   := by rw [R₃]
      _ = Φ.flow (A.add (ρ s) (ρ t)) (J x)    := by rw [← Φ.flow_add]
  -- Now compare L and R; cancel the LHS to get equality of flows on Im(J)
  -- L:  J (flow (s+t) x) = flow (ρ(s+t)) (J x)
  -- R:  J (flow (s+t) x) = flow (ρ s + ρ t) (J x)
  -- Hence: flow (ρ(s+t)) (J x) = flow (ρ s + ρ t) (J x) for all x
  have : Φ.flow (ρ (A.add s t)) (J x) = Φ.flow (A.add (ρ s) (ρ t)) (J x) := 
    Eq.trans (Eq.symm L) R
  exact this

/-! ## Monoid Homomorphism Packaging -/

/-- If, in addition, ρ respects the zero element (ρ 0 = 0),
    then it is a monoid homomorphism on the additive time structure. -/
theorem rho_is_monoid_hom
  (A : AddTime) {X : Type} (Φ : Flow A X)
  (ρ : A.T → A.T) (J : X → X)
  (hEqv : Equivariant A Φ ρ J)
  (hFaith : FaithfulThrough A Φ J)
  (hρ0 : ρ A.zero = A.zero) :
  (ρ A.zero = A.zero) ∧ (∀ s t, ρ (A.add s t) = A.add (ρ s) (ρ t)) := by
  constructor
  · exact hρ0
  · exact additive_from_equivariance A Φ ρ J hEqv hFaith

/-- Convenience structure: ρ is an additive monoid homomorphism. -/
structure IsAddMonoidHom (A : AddTime) (ρ : A.T → A.T) : Prop where
  map_zero : ρ A.zero = A.zero
  map_add  : ∀ s t, ρ (A.add s t) = A.add (ρ s) (ρ t)

/-- Bundle the previous facts into the standard homomorphism form. -/
theorem rho_add_monoid_hom
  (A : AddTime) {X : Type} (Φ : Flow A X)
  (ρ : A.T → A.T) (J : X → X)
  (hEqv : Equivariant A Φ ρ J)
  (hFaith : FaithfulThrough A Φ J)
  (hρ0 : ρ A.zero = A.zero) :
  IsAddMonoidHom A ρ := by
  refine ⟨hρ0, ?_⟩
  exact additive_from_equivariance A Φ ρ J hEqv hFaith

/-! ## Note on Deriving map_zero

The condition `ρ A.zero = A.zero` can be derived from equivariance:
- By `flow_zero`, we have `Φ.flow A.zero x = x`
- By equivariance: `J (Φ.flow A.zero x) = Φ.flow (ρ A.zero) (J x)`
- This gives: `J x = Φ.flow (ρ A.zero) (J x)` for all x
- By faithfulness through J: `A.zero = ρ A.zero` (comparing with flow A.zero)

So `hρ0` is actually derivable from the other hypotheses, but we state it
explicitly for clarity.
-/

/-! ## Interpretation and Integration

**Structure**:
- `A : AddTime` encodes time with addition (e.g., ℝ, ℤ, ℚ, abstract)
- `Φ : Flow A X` encodes one-parameter dynamics with Stone laws
- `J : X → X` is an intertwiner (equivariant map)
- `ρ : A.T → A.T` is a time reparametrization

**Hypotheses**:
- `hEqv`: Equivariance condition `J ∘ flow t = flow (ρ t) ∘ J`
- `hFaith`: Faithfulness through J (parameters determined on image)

**Conclusion**:
ρ must be additive: `ρ (s + t) = ρ s + ρ t`

Hence nonlinear reparametrizations (t ↦ t³, etc.) are excluded.

**How to Use**:
1. Instantiate `A.T` with your time set
2. Define `Φ.flow` as your evolution operator
3. Provide intertwiner `J` (e.g., Heisenberg/Schrödinger picture map)
4. Verify equivariance and faithfulness conditions
5. Conclude: no nonlinear reparams compatible with assumptions

**Relationship to Other Modules**:
- **NoetherLite**: Positive conservation (when symmetry drives dynamics)
- **This module**: Constraint theorem (equivariance forces linearity)
- **QuantumGravityTheorems**: Concrete instance with Hilbert spaces
- Together: complete characterization of compatible symmetries

**Algebraic Pipeline Summary**:

| Layer | Concept | Formal Statement |
|-------|---------|------------------|
| NoetherLite | Symmetry → Conservation | `Invariant ⇒ Conserved` |
| AdditivityFromEquivariance | Equivariance + Faithfulness → Additive ρ | `ρ(s+t) = ρ s + ρ t` |
| Monoid Homomorphism | Plus ρ(0)=0 ⇒ Monoid Hom | `IsAddMonoidHom A ρ` |
| QuantumGravityTheorems | Concrete Physics Instance | Hilbert spaces + unitarity |

**Bottom Line**:
Equivariant intertwiners for faithful flows force ρ to be a monoid homomorphism.
Hence nonlinear reparametrizations (t ↦ t³, etc.) are structurally excluded.
-/

end AdditivityFromEquivariance
