import Lake
open Lake DSL

package «impossibility_verification» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

-- Root libraries (each file at the formal_proofs root)
@[default_target]
lean_lib «ModularKernel»
lean_lib «NoetherLite»
lean_lib «NoetherImpossibilityDuality»
lean_lib «AdditivityFromEquivariance»
lean_lib «GodelAxiomsComplete»
lean_lib «HaltingProblem_Real»
lean_lib «ImpossibilityQuotientIsomorphism»
lean_lib «DiagonalNondegenerate»
lean_lib «ImpossibilityPredictor»
lean_lib «QuotientCategoryProperties»
lean_lib «NoetherObstructionDuality»
lean_lib «ContinuumProperties»
lean_lib «ContinuumFunctorImpossibility»
lean_lib «ContinuumOmegaOneIncompatibility»
lean_lib «ContinuumUncountability_Baire»
lean_lib «MutualReinforcement»
lean_lib «Minimality»
lean_lib «InterfaceTheory»
lean_lib «AllDiagonalsIsomorphic»
lean_lib «RiceTheorem_Real»
lean_lib «OrdinalHierarchy»
lean_lib «PvsNP_OrdinalAnalysis»
lean_lib «LobTheorem»
lean_lib «ContinuumHypothesis_Real»
lean_lib «GodelDiagonal»
lean_lib «RussellParadox_Real»
lean_lib «CantorRussell»
lean_lib «NoetherGlue»
lean_lib «BinaryTerminalTheorem_v3»
lean_lib «MathematicalUniverseHypothesis»
lean_lib «NeuralSelfReference»
lean_lib «ImpossibilityPushPull»
lean_lib «QuantumSelfMeasurement»
lean_lib «KolmogorovCompression»
lean_lib «CurryParadox»
lean_lib «TarskiUndefinability»
lean_lib «PVUnprovability»
lean_lib «SATDiagonal»
lean_lib «PhysicalComplexity»
lean_lib «ThermodynamicsImpossibility»
lean_lib «QuantumGravityTheorems»
lean_lib «StratificationCore»
lean_lib «InterfaceTheoryCategorical»
lean_lib «InterfaceStratificationCore»
lean_lib «TransfiniteBridge»
lean_lib «TripartiteStruct»
-- lean_lib «NPartiteStruct»  -- Has issues, PerfectCuboidImpossibility is self-contained
lean_lib «MeasurementProblem»
lean_lib «HaagTheoremImpossibility»
lean_lib «ImpossibilityMonad»
lean_lib «DualityMonadBridge»
lean_lib «PerfectCuboidImpossibility»

-- Von Neumann Exorcism
lean_lib «MinimaxTheorem»

-- =====================================================
-- CROWN JEWELS: Unified module hierarchy
-- =====================================================
-- These are the core files that import from each other

-- Base: Impossibility Type Theory (ALL crown jewels import this)
@[default_target]
lean_lib «ImpossibilityType» where
  roots := #[`ImpossibilityType]

-- Inverse Noether builds on ImpossibilityType
lean_lib «InverseNoetherV2» where
  roots := #[`InverseNoetherV2]

-- Physics applications build on InverseNoether
lean_lib «GaugeFromImpossibility» where
  roots := #[`GaugeFromImpossibility]

lean_lib «StandardModelFromImpossibility» where
  roots := #[`StandardModelFromImpossibility]

lean_lib «DarkMatterFromObstruction» where
  roots := #[`DarkMatterFromObstruction]

lean_lib «DarkEnergyFromObstruction» where
  roots := #[`DarkEnergyFromObstruction]

lean_lib «QuantumGravityToE8Refined» where
  roots := #[`QuantumGravityToE8Refined]

lean_lib «DimensionlessConstantsFromE8» where
  roots := #[`DimensionlessConstantsFromE8]

-- =====================================================
-- Other libraries (legacy, standalone)
-- =====================================================

-- Prescriptive Theory
lean_lib «PrescriptiveTheory»

-- Impossibility Field Theory
lean_lib «ImpossibilityFieldTheory»

-- Biological Impossibilities
lean_lib «BiologicalImpossibilities»

-- Information-Theoretic Impossibility
lean_lib «InformationTheoreticImpossibility»

-- Proof-Mechanism Correspondence
lean_lib «ProofMechanismCorrespondence»

-- Inverse Noether / Negative Algebra (radical extension)
lean_lib «InverseNoether»
lean_lib «NegativeAlgebra»
lean_lib «NegativeAlgebraV2»  -- Clean V2 version
lean_lib «InverseNoetherApplications»  -- Applications
lean_lib «ConstructiveImpossibility»

-- Subdirectory library
lean_lib «StructuralIncompatibility» where
  globs := #[.submodules `StructuralIncompatibility]

-- Add Mathlib cache support
meta if get_config? env = some "dev" then
require «doc-gen4» from git
  "https://github.com/leanprover/doc-gen4.git" @ "main"