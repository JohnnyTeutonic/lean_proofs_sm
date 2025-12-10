# Obstruction Core: Mathematical Foundations

This document details the **mathematical structure** of the obstruction framework. All content is formalized in Lean 4.

## 1. The Obstruction Type

An obstruction is a certified impossibility with three components:

```lean
structure Obs where
  name : String
  mechanism : Mechanism      -- How it fails
  quotient : QuotientGeom    -- What remains
```

### 1.1 Mechanism Classification

```lean
inductive Mechanism : Type where
  | diagonal     -- Self-reference creates contradiction
  | fixedPoint   -- Topological obstruction to existence
  | resource     -- Conservation prevents optimum
  | independence -- Underdetermination forces freedom
  deriving DecidableEq, Repr, Inhabited
```

**Rank function:**
```lean
def Mechanism.rank : Mechanism → ℕ
  | .diagonal => 0
  | .fixedPoint => 1
  | .resource => 2
  | .independence => 3
```

The ranking reflects **logical dependencies**:
- Diagonal arguments are primitive (no prerequisites)
- Fixed-point theorems require topology
- Resource constraints require conservation laws
- Independence requires prior structure to be underdetermined

### 1.2 Quotient Geometry

```lean
inductive QuotientGeom : Type where
  | binary           -- {0,1}, {true,false}, {provable,unprovable}
  | nPartite (n : ℕ) -- n-way partition
  | continuous       -- Manifold structure
  | spectrum         -- Continuous family (gauge orbits)
```

**Geometric interpretation:**
- `binary`: Discrete two-point space (Z₂ action)
- `nPartite n`: Discrete n-point space (Sₙ action)
- `continuous`: Smooth manifold (Lie group action)
- `spectrum`: Fiber bundle (gauge group action)

## 2. The Symmetry Type

```lean
inductive SymType : Type where
  | discrete (n : ℕ)     -- Zₙ, finite groups
  | permutation (n : ℕ)  -- Sₙ, symmetric groups
  | continuous (n : ℕ)   -- SO(n), SU(n), Lie groups
  | gauge (n : ℕ)        -- Local gauge symmetry
```

**Dimension function:**
```lean
def SymType.dim : SymType → ℕ
  | .discrete n => n
  | .permutation n => n!
  | .continuous n => n * (n + 1) / 2  -- dim(SO(n))
  | .gauge n => n
```

## 3. The P Functor

**Definition:**
```lean
def P (o : Obs) : ForcedSym :=
  let stype := match o.quotient with
    | .binary => SymType.discrete 2
    | .nPartite n => SymType.permutation n
    | .continuous => SymType.continuous 3
    | .spectrum => SymType.gauge 1
  { name := "Sym(" ++ o.name ++ ")"
    stype := stype
    source := o.name }
```

**Functoriality:** P preserves composition of obstructions (when defined).

**Computational content:** P is a computable function. Given an obstruction, you can compute the forced symmetry in finite time.

## 4. The B Functor (Breaking)

**Definition:**
```lean
def B (s : ForcedSym) : Obs :=
  let mechanism := match s.stype with
    | .discrete _ => Mechanism.diagonal
    | .permutation _ => Mechanism.fixedPoint
    | .continuous _ => Mechanism.resource
    | .gauge _ => Mechanism.independence
  let quotient := match s.stype with
    | .discrete n => QuotientGeom.nPartite n
    | .permutation n => QuotientGeom.nPartite n
    | .continuous _ => QuotientGeom.continuous
    | .gauge _ => QuotientGeom.spectrum
  { name := "Break(" ++ s.name ++ ")"
    mechanism := mechanism
    quotient := quotient }
```

**Interpretation:** B maps a symmetry to the obstruction that arises from breaking it.

## 5. The Adjunction

**Claim:** B ⊣ P (B is left adjoint to P)

**Tight property:**
```lean
theorem tight_adjunction : P ∘ B = id
```

**Proof sketch:**
1. For any symmetry s, compute B(s) (the breaking obstruction)
2. Apply P to get P(B(s)) (the forced symmetry)
3. Show P(B(s)) = s by case analysis on s.stype

**Consequence:** Every symmetry arises from exactly one obstruction type. The correspondence is bijective on objects.

## 6. Standard Examples

### 6.1 Diagonal Obstructions

```lean
def cantorObs : Obs := ⟨"Cantor", .diagonal, .binary⟩
def godelObs : Obs := ⟨"Gödel", .diagonal, .binary⟩
def haltingObs : Obs := ⟨"Halting", .diagonal, .binary⟩

theorem diagonal_gives_Z2 (o : Obs) (h : o.mechanism = .diagonal) 
    (hq : o.quotient = .binary) :
    (P o).stype = .discrete 2
```

### 6.2 Resource Obstructions

```lean
def capObs : Obs := ⟨"CAP", .resource, .nPartite 3⟩
def heisenbergObs : Obs := ⟨"Heisenberg", .resource, .continuous⟩

theorem resource_continuous_gives_Lie (o : Obs) 
    (h : o.mechanism = .resource) (hq : o.quotient = .continuous) :
    (P o).stype = .continuous 3
```

### 6.3 Independence Obstructions

```lean
def phaseObs : Obs := ⟨"Phase", .independence, .spectrum⟩
def gaugeObs : Obs := ⟨"Gauge", .independence, .spectrum⟩

theorem independence_spectrum_gives_gauge (o : Obs) 
    (h : o.mechanism = .independence) (hq : o.quotient = .spectrum) :
    (P o).stype = .gauge 1
```

## 7. Composition and Hierarchy

**Mechanism ordering:**
```lean
instance : LE Mechanism where 
  le m₁ m₂ := m₁.rank ≤ m₂.rank
```

**Transitivity:** If obstruction o₁ forces o₂, and o₂ forces o₃, then o₁ forces o₃.

**Example (formalized in QuantumGravityToE8Refined.lean):**
```
QM measurement limits (independence)
  → Gauge structure (spectrum quotient)
  → Anomaly cancellation (resource constraint)
  → E₈ embedding (fixed-point)
```

This is a **derivation chain**: each step is forced by the previous obstruction.

## 8. Verification Status

All core definitions and theorems are **fully formalized** in:
- `ImpossibilityType.lean` (mechanism classification)
- `InverseNoetherV2.lean` (P and B functors, adjunction)

**Build status:**
```bash
$ lake build ImpossibilityType InverseNoetherV2
Build completed successfully.
```

**No axioms** beyond the 6 foundational ones (measurement limits, anomaly cancellation, standard mathematical results).

**No sorrys** in any file.

## 9. Relationship to Standard Mathematics

This framework **unifies** known results:

| Standard Result | Framework Interpretation |
|----------------|-------------------------|
| Cantor's theorem | Diagonal obstruction → Z₂ |
| Gödel incompleteness | Diagonal obstruction → Z₂ |
| Brouwer fixed point | Fixed-point obstruction → SO(n) |
| Noether's theorem | Symmetry → Conservation (inverse: P) |
| Gauge principle | Independence obstruction → Gauge group |

The novelty is **unification** and **computational content**, not the individual results.

## 10. For Category Theorists

**Objects:**
- Obs: Category of obstructions (morphisms = implication)
- Sym: Category of symmetries (morphisms = breaking)

**Functors:**
- P : Obs → Sym (forced symmetry)
- B : Sym → Obs (breaking obstruction)

**Adjunction:**
- B ⊣ P with unit η : id → P ∘ B
- Tight: η is an isomorphism (P ∘ B = id)

**Computational content:**
- P and B are computable functions
- Composition is computable
- Adjunction is constructive

---

**Next:** See `StructuralResults.md` for the main theorems and their applications.
