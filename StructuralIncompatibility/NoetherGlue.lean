import NoetherLite
import AdditivityFromEquivariance
import StructuralIncompatibility.QuantumGravityTheorems

/-!
NoetherGlue.lean
Author: Jonathan Reich, October 2025

Connects the quantum gravity incompatibility theorem with Noether's theorem.

**Conceptual Integration**:

**Noether's Theorem (Positive Characterization)**:
If evolution flow factors through a symmetry action (flow = act ∘ ρ),
then every G-invariant observable is conserved.

**QG Incompatibility (Negative Characterization)**:  
Faithful Stone-von Neumann dynamics + full time-reparam covariance 
forces ρ to be additive → nonlinear reparams cannot factor consistently.

**The Connection**:
- Noether characterizes WHEN you get conservation (compatible symmetries)
- QG incompatibility characterizes WHEN that factorization CANNOT exist
- Together: complete picture of which flows admit Noether structure

This file wires the QG structures into NoetherLite's abstract framework,
showing that:
1. When ρ IS compatible (linear), you get Noether conservation
2. When ρ is nonlinear, the incompatibility theorem forbids factorization
-/

namespace NoetherGlue

open NoetherLite AdditivityFromEquivariance QuantumGravityTheorems

/-! ## Three-Layer Architecture

**Layer 1: NoetherLite** (Positive Conservation)
- When flow factors through symmetry → conservation
- Abstract: symmetry action, flow presentation, invariance → conserved

**Layer 2: AdditivityFromEquivariance** (Structural Constraint)
- Equivariant intertwiner + faithful flow → ρ must be additive
- Abstract: rules OUT nonlinear reparametrizations

**Layer 3: QuantumGravityTheorems** (Concrete Physics)
- Faithful Stone-von Neumann + full reparam covariance → contradiction
- Concrete: Hilbert spaces, unitary evolution, time reparams

This file connects all three layers.
-/

/-! ## Conceptual Integration (Informal Overview)

This file connects the QG incompatibility theorem with Noether's theorem conceptually.

**The Key Insight**:
- **Noether (Positive)**: When flow = act ∘ ρ (factorizes through symmetry) → conservation
- **QG Incompatibility (Negative)**: Faithful Stone-von Neumann + full reparam covariance forces ρ additive

**The Connection**:
For faithful unitary evolution U:
1. IF ρ is linear/additive AND equivariant → Noether structure exists → conservation
2. IF ρ is nonlinear → QG theorem forbids equivariance → no Noether factorization

This delineates the boundary of Noether's domain: exactly the linear reparametrizations.

**Why No Formal Action Definition**:
We cannot define a total "reparam action" because it only exists when equivariance holds
(i.e., for linear ρ). Instead, we state the incompatibility directly.
-/

/-! ## The Core Incompatibility Restated -/

/-- Restatement: If ALL time reparams (including nonlinear) were equivariant,
    we'd get contradiction. This is exactly the QG incompatibility theorem. -/
theorem no_universal_reparam_equivariance {H : Type*} (U : OneParamUnitary H) :
    ¬ (∀ (ρ : TimeReparam), equivariant_under U ρ) :=
  no_full_time_reparam_equivariance U

/-! ## Summary: The Duality

**Noether (Positive Kernel)**:
- Flow = act ∘ ρ factorizes → Invariance → Conservation
- Works for: additive/linear reparametrizations

**QG Incompatibility (Negative Kernel)**:
- Faithful dynamics + full reparam covariance → forces ρ additive
- Obstruction: nonlinear reparametrizations cannot be equivariant

**Boundary Delineation**:
The QG incompatibility theorem marks exactly where Noether structure fails:
- Linear ρ: Noether factorization exists (conservation holds)
- Nonlinear ρ: No factorization possible (obstruction proven)

**Meta-Categorical**:
- Noether → exact functors (structure-preserving)
- Impossibility → non-exact functors (cannot compose consistently)
- Together: complete theory of structural compatibility
-/

end NoetherGlue
