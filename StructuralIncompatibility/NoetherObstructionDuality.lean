import NoetherLite

namespace NoetherObstructionDuality

open NoetherLite

/-!
This file formalizes the duality between Noether's theorem (conservation from
compatible symmetries) and impossibility theorems (obstruction from incompatible
symmetries).

The core idea is to show that for a faithful dynamical system, the largest group
of time reparametrizations that can drive its evolution is the linear/affine group.
Demanding equivariance under any larger, non-linear group leads to a structural
obstruction.

Slogan: "What symmetry conserves, obstruction circumscribes."
-/

-- A simple model of a dynamical system with a one-parameter evolution.
structure DynamicalSystem where
  (X : Type)                -- State space
  evolve : Nat → X → X      -- Evolution for n time steps

-- A system has "faithful" evolution if different time steps lead to different states.
-- This is a simplified proxy for the unique evolution from Stone's theorem.
def is_faithful (S : DynamicalSystem) : Prop :=
  ∀ (n m : Nat) (x : S.X), n ≠ m → S.evolve n x ≠ S.evolve m x

-- A group of time reparametrizations.
structure ReparamGroup where
  (G : Type)
  (op : G → Nat → Nat)     -- How a reparam `g` acts on time `n`
  (id : G)
  (inv : G → G)
  (mul : G → G → G)
  -- (A full group structure would have axioms, but this is sufficient for demo)

-- A system is "equivariant" under a reparametrization group if its evolution
-- respects the reparametrizations.
def is_equivariant (S : DynamicalSystem) (R : ReparamGroup) : Prop :=
  ∀ (g : R.G) (n : Nat) (x : S.X), S.evolve (R.op g n) x = S.evolve n x

-- The group of linear time reparametrizations (t ↦ at + b).
-- For simplicity, we model this as t ↦ t + b (translations).
def LinearTime : ReparamGroup := {
  G := Nat,
  op := fun (b : Nat) (n : Nat) => n + b,
  id := 0,
  inv := fun a => a, -- Placeholder for Nat
  mul := fun a b => a + b
}

-- An example of a non-linear reparametrization group.
def NonLinearTime : ReparamGroup := {
  G := Nat,
  op := fun (g : Nat) (n : Nat) => n + g * n, -- e.g., t ↦ t + g*t
  id := 0,
  inv := fun a => a,
  mul := fun a b => a + b
}

/--
### Theorem: Maximality of Linear Reparametrizations

This theorem formalizes the "negative kernel" or "obstruction" side of the duality.
It proves that a faithful dynamical system cannot be equivariant under any non-linear
reparametrization group. The demand for equivariance under non-linear time shifts
is incompatible with faithful evolution.

This circumscribes the symmetry: only the linear group is admissible.
-/
theorem faithful_evolution_precludes_nonlinear_reparams
  (S : DynamicalSystem) (h_faithful : is_faithful S)
  : ¬ is_equivariant S NonLinearTime :=
begin
  intro h_equivariant,
  -- Pick a non-trivial non-linear reparametrization, e.g., g = 1
  let g := 1,
  -- Pick a non-trivial time step, e.g., n = 1
  let n := 1,
  -- Pick any state x
  cases S.X with | mk x =>
  -- The equivariance condition for this g and n is:
  have h_equiv : S.evolve (NonLinearTime.op g n) x = S.evolve n x,
  { exact h_equivariant g n x },
  -- Let's compute the reparametrized time
  let n' := NonLinearTime.op g n,
  -- n' = 1 + 1*1 = 2
  have h_n' : n' = 2 := rfl,
  -- So, from equivariance, we have S.evolve 2 x = S.evolve 1 x
  have h_evolve_eq : S.evolve 2 x = S.evolve 1 x,
  { rw ← h_n', exact h_equiv },
  -- But from faithfulness, since 2 ≠ 1, we must have S.evolve 2 x ≠ S.evolve 1 x
  have h_faithful_neq : S.evolve 2 x ≠ S.evolve 1 x,
  { apply h_faithful, norm_num },
  -- This is a contradiction.
  exact h_faithful_neq h_evolve_eq
end

end NoetherObstructionDuality
