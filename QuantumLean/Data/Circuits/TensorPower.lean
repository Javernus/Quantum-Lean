import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Notation
import Mathlib.Data.Complex.Basic

import «QuantumLean».Data.Circuits.Reindex
import «QuantumLean».Data.Matrix.Kronecker

open Matrix
open Complex
open Kronecker
open Circuits

/-
This file contains core definitions and theorems on the tensor power. The tensor power
is defined using the Kronecker product from `mathlib`.

First, there is the `tensor_power` definition that recursively defines a tensor power
based on the `gates` function passed along to it. `gates` is a function that given
(n : ℕ), the gate for that index is given back.

There are two abbreviations for the tensor power definition:

- tensor_power': defines a tensor power of a single gate M. Arguments: (n : ℕ) (M : nGate)
- apply_at: creates a tensor power of identity matrices except at i for M. Arguments: (i : ℕ) (M : nGate)

Then, there are the proven theorems in this file. These prove certain equalities for the
tensor power and can be used in proofs. Assume M, N nGates and c a natural number. The
proofs shown here are shortened for readability.

- tensor_power_zero: `tensor_power 0 gates = !![1]`
- tensor_power_of_one: `tensor_power' n (1 : nGate m) = 1` (and non-prime variant)
- tensor_power_of_natCast: `tensor_power' n (i : nGate m) = ↑(i ^ n)` (and non-prime variant)
- tensor_power_smul: `tensor_power' n (c • M) = c ^ n • tensor_power' n M` (and non-prime variant)
- tensor_power_mul: `tensor_power n M * tensor_power n N = tensor_power n (λ i => M i * N i)`

Furthermore, there are three theorems which are not proven yet. These correspond to the
theorems suggested in the "A Foundation to Formalise Quantum Algorithms in Lean" thesis
by Jake Jongejans.

- tensor_power_one: `reindex₂ (tensor_power 1 gates) = gates 1`
- tensor_power_slice: `tensor_power (n + o) gates = tensor_power n gates ⊗ₖ tensor_power o (fun i => gates (n + i))`
  - Allow for slicing a tensor power in two parts.
- tensor_power_of_tensor_power: `tensor_power' (n * o) M = tensor_power' o (tensor_power' n M)`
  - Prove a tensor_power' is equivalent to a tensor_power' of a tensor_power' for n, o ∈ ℕ.
-/

namespace Circuits
section TensorPower

variable {m m' n n' o : ℕ}


@[simp]
def tensor_power (n : ℕ) (gates : ℕ -> nGate' m m') : nGate' (m * n) (m' * n) :=
  match n with
    | 0 => !![1]
    | (n + 1) => reindex₃ (tensor_power n gates ⊗ₖ gates (n + 1))


@[simp]
abbrev tensor_power' (n : ℕ) (M : nGate' m m') := tensor_power n (fun _ => M)


-- Only functions properly for 1 qubit gates
abbrev apply_at (n i : ℕ) (M : nGate m) := tensor_power n (fun j => if i == j then M else 1)


theorem tensor_power_zero { gates : ℕ -> nGate' m m' } : tensor_power 0 gates = !![1] := by
  simp [tensor_power]


theorem one_eq' : !![1] = (1 :  nGate' (m * Nat.zero) (m * Nat.zero)) := by
  ext i j
  fin_cases i; fin_cases j; rfl


theorem tensor_power_of_one : tensor_power n (fun _ => (1 : nGate m)) = 1 := by
  induction n with
    | zero =>
      simp [tensor_power]
      exact one_eq'
    | succ n ih =>
      rw [tensor_power]
      rw [ih]
      rw [one_kronecker_one, reindex₃_one]


theorem tensor_power'_of_one : tensor_power' n (1 : nGate m) = 1 := by
  rw [tensor_power', tensor_power_of_one]


theorem tensor_power_of_natCast { i : ℕ } : tensor_power n (fun _ => (i : nGate m)) = ↑(i ^ n) := by
  induction n with
    | zero => rw [tensor_power_zero]; rw [Nat.pow_zero i, Nat.cast_one]; exact one_eq
    | succ n ih => rw [tensor_power, ih, kronecker_natCast_natCast, reindex₃_natCast, ← Nat.pow_succ]


theorem tensor_power'_of_natCast { i : ℕ } : tensor_power' n (i : nGate m) = ↑(i ^ n) := by
  rw [tensor_power', tensor_power_of_natCast]


theorem tensor_power_smul (M : nGate m) (c : ℕ)
  : tensor_power n (fun _ => c • M) = c ^ n • tensor_power n (fun _ => M) := by
  induction n with
    | zero => simp [tensor_power]
    | succ n ih =>
      rw [tensor_power, tensor_power, ih, smul_kronecker, kronecker_smul, ← smul_assoc, smul_reindex₃]
      rw [Nat.pow_succ, smul_eq_mul]


theorem tensor_power'_smul (M : nGate m) (c : ℕ)
  : tensor_power' n (c • M) = c ^ n • tensor_power' n M := by
  rw [tensor_power', tensor_power_smul]


theorem tensor_power_mul (M : ℕ -> nGate' m m') (N : ℕ -> nGate' m' o)
  : tensor_power n M * tensor_power n N = tensor_power n (λ i => M i * N i) := by
  induction n with
    | zero => simp [tensor_power]
    | succ m ih =>
      rw [tensor_power]
      rw [tensor_power]
      rw [tensor_power]
      rw [← reindex₃_mul]
      rw [← mul_kronecker_mul]
      rw [ih]


-- tensor_power 1 of any gate is equivalent to that gate
theorem tensor_power_one {m m' : ℕ} { gates : ℕ -> nGate' m m' } :
    reindex₂ (tensor_power 1 gates) = gates 1 := by
  sorry


-- Slice a tensor power in two pieces
theorem tensor_power_slice (gates : ℕ -> nGate' m m') :
    tensor_power (n + o) gates =
    reindex₅ (tensor_power n gates ⊗ₖ tensor_power o (fun i => gates (n + i))) :=  by
  sorry


-- Turn a single tensor_power' into a tensor_power' of a tensor_power'
theorem tensor_power_of_tensor_power (M : nGate' m m') :
    tensor_power' (n * o) M = reindex₄ (tensor_power' o (tensor_power' n M)) := by
  sorry


end TensorPower
end Circuits
