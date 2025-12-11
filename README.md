# Lean Proofs: Standard Model from Impossibility Theory

Machine-verified derivations of fundamental physics from measurement impossibilities.

## Result Tiers

We explicitly distinguish results by epistemic status:

### Tier A: DERIVED (Core Framework)
These follow directly from the obstruction methodology with minimal assumptions:

| Result | Mechanism | Status |
|--------|-----------|--------|
| SM gauge group SU(3)SU(2)U(1) | Anomaly cancellation | **Proven** |
| Number of colors N_c = 3 | Unique anomaly-free solution | **Proven** |
| Number of generations N_gen = 3 | E  E  SU(3) decomposition | **Proven** |
| General Relativity | Gravitational measurement impossibility | **Proven** |
| Hypercharge quantization Y = 1/6 | Follows from N_c = 3 | **Proven** |

### Tier B: STRONG PREDICTIONS (Dimensional Ratios)
These use representation-theoretic dimension counting:

| Result | Formula | Measured | Error |
|--------|---------|----------|-------|
| Weinberg angle | sinθ_W = 3/8 = 0.375 | 0.231 (low E) | GUT scale prediction |
| Cabibbo angle | sin θ_C = 1/20  0.2236 | 0.22534 | **0.77%** |

### Tier C: EXPLORATORY (If E Chain Correct)
These depend on specific assumptions about E breaking dynamics:

| Result | Prediction | Current Data | Confidence |
|--------|------------|--------------|------------|
| Dark energy w(z) | w  -0.81, mild evolution | DESI: w = -0.83  0.06 | Medium |
| Neutrino hierarchy | Normal (m < m << m) | Untested | Medium |
| Neutrino nature | Majorana | Untested | Medium |
| Mass scale | Σm_ν  0.06 eV | KATRIN < 0.45 eV | Consistent |
| Proton decay | τ_p ~ 10-10 years | > 2.410 yr | Low-Medium |
| Strong CP | θ_QCD = 0 | θ < 10 | Low-Medium |

**Important:** Tier C results are exploratory extensions. If falsified, they indicate the specific E breaking chain needs revision, not that the core framework (Tiers A-B) is wrong.

## Project Structure

`
lean_proofs_sm/
 ImpossibilityType.lean                     # Core impossibility mechanisms
 InverseNoetherV2.lean                      # P : Obs  Sym functor

 GaugeFromImpossibility.lean                # U(1) from phase impossibility
 GaugeGroupClassification.lean              # Lie algebra classification
 StandardModelFromImpossibility.lean        # Full SM derivation
 HyperchargeQuantization.lean               # Y = 1/6 from N_c = 3
 RenormalizabilityFromObstruction.lean      # dim  4 operators

 ExceptionalImpossibility.lean              # E uniqueness
 GenerationNumberFromE8.lean                # N_gen = 3 derivation
 CosmicFractionsFromE8.lean                 # 68/27/5 cosmic ratios

 GrandUnificationImpossibility.lean         # GUT constraints
 WeinbergAngleRefined.lean                  # sinθ_W = 3/8
 CabibboAngleFromE8.lean                    # sin θ_C = 1/20 (NEW)

 GravityFromImpossibility.lean              # GR derivation
 SpacetimeFromObstruction.lean              # d=4, signature (3,1)

 CosmologicalConstantMinimal.lean           # Λ suppression
 KappaGeometricMeaning.lean                 # κ = ln(248)/ln(133)
 DarkMatterFromObstruction.lean             # DM necessity
 DarkEnergyFromObstruction.lean             # DE = Λ

 QuantumGravityToE8Refined.lean             # QG  E terminus

 NeutrinoHierarchyFromE8.lean               # ν predictions (Tier C)
 DESIDarkEnergyPredictions.lean             # w(z) predictions (Tier C)
 ProtonDecayFromE8.lean                     # τ_p prediction (Tier C)
 StrongCPFromObstruction.lean               # θ = 0 argument (Tier C)

 [additional files...]
`

## Build Instructions

`ash
# Clone
git clone git@github.com:JohnnyTeutonic/lean_proofs_sm.git
cd lean_proofs_sm

# Setup (downloads Mathlib)
lake update
lake exe cache get

# Build all
lake build
`

### Toolchain
- **Lean:** 4.25.0
- **Mathlib:** v4.25.0
- **Lake:** 5.0.0

## Key Theorems (Tier A)

`lean
-- Standard Model gauge group (Tier A: Proven)
theorem sm_gauge_from_three_obstructions :
    (PhaseObs  IsospinObs  ColorObs) 
    GaugeGroup  SU(3)  SU(2)  U(1)

-- Three generations (Tier A: Proven)
theorem three_generations_from_E8 :
    E  E  SU(3) forces N_gen = 3

-- Cabibbo angle (Tier B: 0.77% error)
theorem cabibbo_from_gauge_gen_dim :
    sin θ_C = 1/(dim SU(3) + dim SU(2) + dim SU(3)_flavor + dim U(1))
            = 1/20  0.2236
`

## Falsifiability

**Tier A (would refute core framework):**
- Discovery of 4th generation with SM interactions
- Observation of fractional electric charges (free quarks)
- Lorentz violation in gravity sector

**Tier B (would refute dimension-counting):**
- Cabibbo angle measurement deviating >3% from 0.2236
- GUT-scale Weinberg angle  3/8

**Tier C (would refute specific E chain, not core):**
- Inverted neutrino hierarchy confirmed
- Proton decay outside 10-10 year range
- Large neutron EDM (d_n > 10 ecm)

## License

Apache 2.0. See LICENSE file.

## Citation

`ibtex
@software{reich2025lean_proofs_sm,
  author = {Reich, Jonathan},
  title = {Lean Proofs: Standard Model from Impossibility Theory},
  year = {2025},
  url = {https://github.com/JohnnyTeutonic/lean_proofs_sm}
}
`

## Contact

Jonathan Reich - jonathareich100@gmail.com

---

**Status:** All proofs verified  | Tier A: 5 core results | Tier B: 2 precision predictions | Tier C: 6 exploratory
