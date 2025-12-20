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

### Foundation
| File | Description |
|------|-------------|
| `ImpossibilityType.lean` | Core type theory: mechanisms, quotient geometries, Binary terminal object |
| `InverseNoetherV2.lean` | The B ⊣ P adjunction between Obs and Sym categories |

### Standard Model Derivations
| File | Result |
|------|--------|
| `GaugeFromImpossibility.lean` | Gauge group structure from measurement constraints |
| `GaugeGroupClassification.lean` | Classification of admissible gauge groups |
| `StandardModelFromImpossibility.lean` | Full SM derivation chain |
| `HyperchargeQuantization.lean` | Y_min = 1/6 from anomaly cancellation |
| `WeinbergAngleRefined.lean` | sin²θ_W = 3/8 at GUT scale |
| `GenerationNumberFromE8.lean` | N_gen = 3 from E₈ → E₆ × SU(3) branching |

### Gravity and Cosmology
| File | Result |
|------|--------|
| `GravityFromImpossibility.lean` | Diffeomorphism invariance from reference frame obstruction |
| `SpacetimeFromObstruction.lean` | d = 4 spacetime dimension |
| `CosmologicalConstantMinimal.lean` | Λ suppression from E₈ structure |
| `DarkMatterFromObstruction.lean` | Dark sector as measurement-inaccessible obstruction class |
| `DarkEnergyFromObstruction.lean` | w(a) dynamics from obstruction flow |

### Predictions
| File | Prediction | Status |
|------|------------|--------|
| `CabibboAngleFromE8.lean` | sin θ_C = 1/√20 ≈ 0.2236 | 0.77% from measured |
| `NeutrinoHierarchyFromE8.lean` | Normal ordering | Testable (JUNO) |
| `ProtonDecayFromE8.lean` | p → μ⁺π⁰ forbidden | Testable |
| `DESIDarkEnergyPredictions.lean` | w_a/(1+w_0) ≈ -5.9 | Consistent with DESI DR2 |

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
- `generation_count_three`: Exactly 3 generations from E₈ branching
- `hypercharge_minimum`: Minimum hypercharge Y = 1/6

## Methodology

The framework proceeds in three steps:

1. **Identify physical impossibilities**: Measurements that cannot be performed (absolute phase, simultaneous position-momentum, etc.)

2. **Formalize as categorical obstructions**: Each impossibility defines a quotient geometry in the obstruction category Obs

3. **Apply the adjunction**: The functor P : Obs → Sym maps obstructions to forced symmetries; B : Sym → Obs is the right adjoint

The adjunction B ⊣ P satisfies tight round-trip conditions (verified in `InverseNoetherV2.lean`), ensuring the correspondence is not arbitrary.

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

See `PREDICTIONS_PREREGISTRATION.md` for a complete list of predictions with:
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
