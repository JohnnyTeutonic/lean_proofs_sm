/-
Copyright 2025 Jonathan Reich
Licensed under the Apache License, Version 2.0
-/
import Lake
open Lake DSL

package lean_proofs_sm where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.25.0"

-- Core dependency
@[default_target]
lean_lib ImpossibilityType

lean_lib InverseNoetherV2 where
  roots := #[`InverseNoetherV2]

-- Physics derivation chain
lean_lib GaugeFromImpossibility
lean_lib GaugeGroupClassification
lean_lib StandardModelFromImpossibility
lean_lib HyperchargeQuantization
lean_lib ExceptionalImpossibility
lean_lib GenerationNumberFromE8
lean_lib CosmicFractionsFromE8
lean_lib GrandUnificationImpossibility
lean_lib WeinbergAngleRefined
lean_lib GravityFromImpossibility
lean_lib SpacetimeFromObstruction
lean_lib CosmologicalConstantMinimal
lean_lib KappaGeometricMeaning
lean_lib DarkMatterFromObstruction
lean_lib DarkEnergyFromObstruction
lean_lib QuantumGravityToE8Refined
lean_lib NeutrinoAnomalies
lean_lib ProtonDecayPrediction
lean_lib UVIRChainDiscrimination
lean_lib RenormalizabilityFromObstruction
lean_lib CabibboAngleFromE8
lean_lib DESIDarkEnergyPredictions
lean_lib NeutrinoHierarchyFromE8
lean_lib StrongCPFromObstruction
lean_lib ProtonDecayFromE8
lean_lib FineStructureFromE8
lean_lib HyperchargeFromSU5
