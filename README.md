# Standard Model from Impossibility Theory

[![Lean 4](https://img.shields.io/badge/Lean-4.25.0-blue.svg)](https://lean-lang.org/)
[![Mathlib](https://img.shields.io/badge/Mathlib-v4.25.0-green.svg)](https://github.com/leanprover-community/mathlib4)
[![License](https://img.shields.io/badge/License-Apache%202.0-orange.svg)](LICENSE)

Machine-verified derivations of Standard Model structure from impossibility constraints, formalized in Lean 4.

## Overview

This repository contains formal proofs exploring the question: *Can gauge symmetries be derived from physical impossibilities rather than postulated?*

The approach inverts the usual logic of theoretical physics. Rather than starting with symmetry groups and deriving constraints, we start with measurement impossibilities and derive the symmetries they force.

### Core Claim

The Standard Model gauge group SU(3) × SU(2) × U(1) can be characterized as the unique solution to a system of anomaly cancellation constraints, formalized as a categorical adjunction between obstruction and symmetry categories.

## Structure

### Standard Model Derivations
| File | Result |
|------|--------|
| `StandardModelFromImpossibilityCMP.lean` | Full SM derivation chain |
| `MatterContentUniqueness.lean` | SM matter content uniqueness |
| `SMMinimalConstraintsCMP.lean` | Minimal constraints forcing the gauge group |
| `U1ExtensionClassification.lean` | Classification of admissible U(1) extensions |
| `TrialityMixingConnection.lean` | D₄ triality breaking → fermion mixing angles |
| `YukawaSelectionRulesFromZ3.lean` | Yukawa selection rules from ℤ₃ grading |

### Defensive Architecture
| File | Result |
|------|--------|
| `AdversarialInputWitnessTestsCMP.lean` | Adversarial testing of input/encoding invariance |
| `OperationalSchemaCMP.lean` | Operational schema bridging the semantic gap to physical impossibilities |
| `SemanticContractCMP.lean` | Formal interface showing forced symmetry is invariant under schema-equivalent encodings |
| `Stage2InterfaceContract.lean` | Interface between the workflow and domain-specific derivations |

> **Note on generation number:** The `TrialityMixingConnection.lean` file derives mixing structure via D₄ triality (S₃ containing ℤ₃ as a normal subgroup; ℤ₃ breaking allows off-diagonal Yukawas). The companion paper also discusses an alternative route via E₈ → E₆ × SU(3) branching (248 → (78,1) ⊕ (1,8) ⊕ (27,3) ⊕ (27̄,3̄), where the 3 of SU(3) forces three families). Both routes yield N_gen = 3; this repository formalizes the triality route.

## Requirements

- **Lean**: 4.25.0
- **Mathlib**: v4.25.0

## Building

```bash
# Clone the repository
git clone https://github.com/JohnnyTeutonic/lean_proofs_sm.git
cd lean_proofs_sm

# Build with Lake
lake build
```

## Verification

All theorems are machine-checked. To verify:

```bash
lake env lean <filename>.lean
```

Key verified results:
- `sm_gauge_group_unique`: SM gauge group is unique solution to anomaly constraints
- `weinberg_angle_gut`: sin²θ_W = 3/8 at unification scale
- `generation_count_three`: Exactly 3 generations from triality structure
- `hypercharge_minimum`: Minimum hypercharge Y = 1/6

## Methodology

The framework proceeds in three steps:

1. **Identify physical impossibilities**: Measurements that cannot be performed (absolute phase, simultaneous position-momentum, etc.)

2. **Formalize as categorical obstructions**: Each impossibility defines a quotient geometry in the obstruction category Obs

3. **Apply the adjunction**: The functor P : Obs → Sym maps obstructions to forced symmetries; B : Sym → Obs is the right adjoint

The adjunction B ⊣ P satisfies tight round-trip conditions, ensuring the correspondence is not arbitrary.

## Limitations

This framework addresses *kinematics* (what structures must exist) rather than *dynamics* (how they evolve). Specifically:

**Derived (structural necessity)**:
- Gauge group structure
- Spacetime dimension and signature
- Generation count
- Mixing angles (Weinberg, Cabibbo)

**Not derived (contingent parameters)**:
- Yukawa couplings
- Higgs mass
- Absolute mass scales
- Full CKM matrix (only Cabibbo angle)

This distinction is formalized in the `ContingentSectorInterface` structures.

## Pre-registered Predictions

See [`PREDICTIONS_PREREGISTRATION.md`](PREDICTIONS_PREREGISTRATION.md) for a complete list of predictions with:
- Derivation method
- Lean file reference
- Falsification criteria
- Current empirical status

## Citation

```bibtex
@software{reich2025sm_impossibility,
  author = {Reich, Jonathan},
  title = {Standard Model from Impossibility Theory},
  year = {2025},
  url = {https://github.com/JohnnyTeutonic/lean_proofs_sm}
}
```

## Related Work

- Anomaly cancellation in gauge theories (Adler, Bell, Jackiw)
- Exceptional Lie algebras in physics (Gürsoy, Ramond)
- Categorical approaches to physics (Baez, Schreiber)
- Machine verification in mathematics (Mathlib, Lean community)

## License

Apache 2.0. See [LICENSE](LICENSE) for details.

## Contact

Jonathan Reich — jonathanreich100@gmail.com
