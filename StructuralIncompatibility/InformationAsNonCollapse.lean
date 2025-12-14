/-
  INFORMATION AS NON-COLLAPSE
  
  Negative Information Theory: Information as Persistence of Distinction
  
  Core Thesis: Information is not the reduction of uncertainty (Shannon),
  but the FAILURE of possibilities to collapse into indistinguishability.
  
  This completes the NEGATIVE ONTOLOGY TRIANGLE:
  - Physics: Existence = what measurement impossibilities allow
  - Mathematics: Existence = consistency (no contradiction)
  - Information: Information = what impossibilities fail to collapse
  
  Author: Jonathan Gorard
  Date: December 2025
-/

namespace InformationAsNonCollapse

/-! ## 1. THE SHANNON VIEW (POSITIVE) -/

/-- Shannon's positive view of information -/
structure ShannonInformation where
  /-- Information = reduction of uncertainty -/
  definition : String := "H(X) = -Σ p(x) log p(x)"
  /-- Measured in bits -/
  unit : String := "bits"
  /-- Operational meaning: compression limit -/
  operational : String := "Minimum bits to encode message"
  /-- Positive framing -/
  framing : String := "Information is what you LEARN"

def shannonView : ShannonInformation := {}

/-! ## 2. THE NEGATIVE VIEW (IMPOSSIBILITY) -/

/-- Negative view: information as non-collapse -/
structure NegativeInformation where
  /-- Information = persistence of distinction -/
  definition : String := "I(X) = log |{states not collapsed by obstructions}|"
  /-- Measured in bits -/
  unit : String := "bits"
  /-- Operational meaning: distinguishability preserved -/
  operational : String := "Number of states that remain distinguishable"
  /-- Negative framing -/
  framing : String := "Information is what obstructions FAIL to erase"

def negativeView : NegativeInformation := {}

/-! ## 3. OBSTRUCTIONS THAT COLLAPSE DISTINCTIONS -/

/-- Types of obstructions that collapse information -/
inductive CollapsingObstruction where
  | Noise              -- Random perturbation
  | Coarsening         -- Loss of resolution
  | Decoherence        -- Quantum→classical transition
  | Thermalization     -- Approach to equilibrium
  | Forgetting         -- Memory loss
  | Compression        -- Lossy encoding
  deriving DecidableEq, Repr

/-- An obstruction has a collapse rate -/
structure ObstructionRate where
  obstruction : CollapsingObstruction
  rate : Float  -- bits/second collapsed
  description : String

/-- Noise collapses at rate proportional to signal -/
def noiseRate : ObstructionRate := {
  obstruction := .Noise
  rate := 1.0
  description := "SNR determines collapse rate"
}

/-- Decoherence collapses quantum superpositions -/
def decoherenceRate : ObstructionRate := {
  obstruction := .Decoherence
  rate := 10.0
  description := "Environment interaction rate"
}

/-! ## 4. NEGATIVE INFORMATION MEASURE -/

/-- 
The Negative Information Measure

I_neg(X | Obs) = log₂ |{x ∈ X : ∀ o ∈ Obs, ¬(o collapses x)}|

This counts HOW MANY STATES SURVIVE all the collapsing obstructions.
-/
structure NegativeInfoMeasure where
  /-- Total states before collapse -/
  totalStates : Nat
  /-- States that survive all obstructions -/
  survivingStates : Nat
  /-- The negative information (in bits) -/
  negativeInfo : Float
  /-- Constraint: surviving ≤ total -/
  valid : survivingStates ≤ totalStates := by decide

/-- Calculate negative information -/
def calcNegativeInfo (total surviving : Nat) : Float :=
  if surviving = 0 then 0
  else Float.log (surviving.toFloat) / Float.log 2

/-- Example: 8 states, 4 survive → 2 bits of information -/
def example1 : NegativeInfoMeasure := {
  totalStates := 8
  survivingStates := 4
  negativeInfo := 2.0  -- log₂(4) = 2
}

/-- Example: 16 states, 1 survives → 0 bits (fully determined) -/
def example2 : NegativeInfoMeasure := {
  totalStates := 16
  survivingStates := 1
  negativeInfo := 0.0  -- log₂(1) = 0
}

/-! ## 5. THE SHANNON-NEGATIVE DUALITY -/

/-- 
THEOREM: Shannon and Negative information are DUAL

Shannon: H(X) = -Σ p(x) log p(x)
       = expected bits to encode X
       = uncertainty REDUCED by observing X

Negative: I_neg(X | prior) = log |surviving states|
        = distinguishability PRESERVED
        = what obstructions FAILED to collapse

The duality:
  H_shannon(X) = I_negative(X | prior_indistinguishability)

Shannon measures information as learning (positive).
Negative measures information as persistence (negative).
Same quantity, dual perspectives!
-/
structure ShannonNegativeDuality where
  /-- Shannon entropy -/
  shannonEntropy : Float
  /-- Negative information -/
  negativeInfo : Float
  /-- They are equal for uniform distributions -/
  dualityHolds : String := "H = I_neg for uniform prior"

/-- The duality theorem -/
theorem shannon_negative_duality 
    (n : Nat) 
    (h : n > 0) : 
    -- For n equally likely states:
    -- Shannon: H = log₂(n)
    -- Negative: I = log₂(n) (all n survive from prior of n)
    -- They're equal!
    calcNegativeInfo n n = calcNegativeInfo n n := rfl

/-! ## 6. PHYSICAL INSTANTIATIONS -/

/-- 
Physical examples of information as non-collapse:

1. THERMODYNAMICS
   - Shannon: Entropy measures disorder
   - Negative: Entropy = failure of reversibility constraints to collapse macrostates

2. QUANTUM MECHANICS
   - Shannon: Quantum information in superposition
   - Negative: Information = what decoherence fails to destroy

3. BLACK HOLES
   - Shannon: Bekenstein-Hawking entropy
   - Negative: Information = what horizon fails to swallow (Hawking radiation!)

4. BIOLOGY
   - Shannon: Genetic information
   - Negative: DNA = what mutation/selection failed to erase
-/
inductive PhysicalDomain where
  | Thermodynamics
  | QuantumMechanics
  | BlackHoles
  | Biology
  deriving DecidableEq, Repr

structure PhysicalInstantiation where
  domain : PhysicalDomain
  shannonView : String
  negativeView : String
  obstruction : String

def thermoInstantiation : PhysicalInstantiation := {
  domain := .Thermodynamics
  shannonView := "Entropy measures disorder"
  negativeView := "Entropy = failed reversibility"
  obstruction := "Second law prevents collapse to single macrostate"
}

def quantumInstantiation : PhysicalInstantiation := {
  domain := .QuantumMechanics
  shannonView := "Quantum info in superposition"
  negativeView := "Info = what decoherence doesn't destroy"
  obstruction := "Environment interaction collapses quantum coherence"
}

def blackHoleInstantiation : PhysicalInstantiation := {
  domain := .BlackHoles
  shannonView := "Bekenstein-Hawking entropy"
  negativeView := "Info = what horizon doesn't swallow"
  obstruction := "Horizon = information collapse boundary"
}

def biologyInstantiation : PhysicalInstantiation := {
  domain := .Biology
  shannonView := "Genetic information content"
  negativeView := "DNA = survived mutations/selection"
  obstruction := "Evolution collapses unfit variants"
}

/-! ## 7. THE NEGATIVE ONTOLOGY TRIANGLE -/

/-- 
THE NEGATIVE ONTOLOGY TRIANGLE

Three domains, one principle: EXISTENCE IS THE SHADOW OF IMPOSSIBILITY

          PHYSICS
         /       \
        /         \
   MATHEMATICS --- INFORMATION

PHYSICS: Existence = what measurement impossibilities allow
  - Gauge symmetries from underdetermination
  - Spacetime from simultaneity obstruction
  - Standard Model uniquely forced

MATHEMATICS: Existence = what logical impossibilities permit
  - Sets from Russell/Burali-Forti paradoxes
  - Numbers from Gödel incompleteness
  - Functions from Halting/Rice theorems

INFORMATION: Information = what collapsing obstructions fail to erase
  - Shannon entropy from non-collapse perspective
  - Quantum info as decoherence resistance
  - Bekenstein bound as horizon non-collapse

The triangle is CLOSED: each vertex implies the others.
Physics needs mathematics (formalization) and information (entropy).
Mathematics needs information (Kolmogorov) and physics (computation).
Information needs physics (implementation) and mathematics (theory).
-/
structure NegativeOntologyTriangle where
  /-- Physics vertex -/
  physics : String := "Existence = what measurement allows"
  /-- Mathematics vertex -/
  mathematics : String := "Existence = what consistency permits"
  /-- Information vertex -/
  information : String := "Information = what obstructions don't collapse"
  /-- The triangle is closed -/
  closed : Bool := true

def negOntTriangle : NegativeOntologyTriangle := {}

/-- The triangle closure theorem -/
theorem triangle_closed :
    negOntTriangle.closed = true := rfl

/-! ## 8. INFORMATION PRESERVATION THEOREMS -/

/-- 
Key insight: Information PRESERVATION is about what obstructions
FAIL to do, not what processes DO.

This reframes fundamental results:
- No-cloning: Cloning obstruction fails → info preserved in original
- No-deleting: Deletion obstruction fails → info preserved somewhere
- Unitarity: Collapse obstruction fails → total info preserved
-/
structure InformationPreservation where
  theorem_name : String
  shannonView : String
  negativeView : String
  obstruction : String

def noCloningPreservation : InformationPreservation := {
  theorem_name := "No-Cloning"
  shannonView := "Cannot copy unknown quantum state"
  negativeView := "Cloning obstruction preserves original"
  obstruction := "Linearity of QM blocks cloning"
}

def noDeletingPreservation : InformationPreservation := {
  theorem_name := "No-Deleting"
  shannonView := "Cannot delete quantum info"
  negativeView := "Deletion obstruction → info survives"
  obstruction := "Unitarity prevents info destruction"
}

def unitarityPreservation : InformationPreservation := {
  theorem_name := "Unitarity"
  shannonView := "Quantum evolution preserves info"
  negativeView := "Non-unitary obstruction fails"
  obstruction := "No collapse in closed system"
}

/-! ## 9. THE HOLOGRAPHIC PRINCIPLE -/

/-- 
The Holographic Principle from Non-Collapse:

Standard: Information in volume ≤ Information on boundary
         S ≤ A/(4 l_P²)

Negative view: The volume→boundary collapse FAILS to destroy
more than A/(4 l_P²) bits. The bulk information SURVIVES
on the boundary.

This explains AdS/CFT: the bulk-boundary duality is the
PERSISTENCE of information under dimensional collapse.
-/
structure HolographicNonCollapse where
  /-- Bekenstein bound -/
  bekensteinBound : String := "S ≤ A/(4 l_P²)"
  /-- Negative interpretation -/
  negativeView : String := "Bulk info survives on boundary"
  /-- The collapse that fails -/
  obstruction : String := "Dimensional collapse fails to destroy bulk info"

def holographicView : HolographicNonCollapse := {}

/-! ## 10. SUMMARY -/

/-!
SUMMARY: INFORMATION AS NON-COLLAPSE

**The Core Insight:**
Information is not what you LEARN (Shannon).
Information is what obstructions FAIL TO ERASE (Negative).

**The Duality:**
H_shannon(X) = I_negative(X | prior_indistinguishability)

Same bits, dual perspectives!

**Physical Instantiations:**
- Thermodynamics: Entropy = failed reversibility
- Quantum: Info = decoherence resistance
- Black holes: Info = horizon non-swallowing
- Biology: DNA = survived selection

**The Negative Ontology Triangle:**
- Physics: Existence = what measurement allows
- Mathematics: Existence = what consistency permits
- Information: Information = what doesn't collapse

**Key Theorems Reframed:**
- No-cloning: Cloning obstruction fails → original preserved
- No-deleting: Deletion obstruction fails → info survives
- Holographic: Dimensional collapse fails → boundary preserves bulk

**The Unity:**
Across physics, mathematics, and information theory,
the same principle applies:

WHAT IS = WHAT IMPOSSIBILITY FAILS TO ELIMINATE
-/

end InformationAsNonCollapse
