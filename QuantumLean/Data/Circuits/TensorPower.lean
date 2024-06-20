import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Notation
import Mathlib.Data.Complex.Basic

import «QuantumLean».Data.Circuits.Reindex
import «QuantumLean».Data.Matrix.Kronecker

open Matrix
open Complex
open Kronecker
open Circuits


namespace Circuits
section TensorPower

variable {m m' n n' o : ℕ}


@[simp]
def tensor_power (n : ℕ) (gates : ℕ -> nMatrix' m m') : nMatrix' (m * n) (m' * n) :=
  match n with
    | 0 => !![1]
    | (n + 1) => reindex₃ (tensor_power n gates ⊗ₖ gates (n + 1))


abbrev tensor_power' (n : ℕ) (M : nMatrix' m m') := tensor_power n (fun _ => M)


-- Only functions properly for 1 qubit gates
abbrev apply_at (n i : ℕ) (M : nMatrix m) := tensor_power n (fun j => if i == j then M else 1)


theorem tensor_power_zero { gates : ℕ -> nMatrix' m m' } : tensor_power 0 gates = !![1] := by
  simp [tensor_power]


theorem one_eq' : !![1] = (1 :  nMatrix' (m * Nat.zero) (m * Nat.zero)) := by
  ext i j
  fin_cases i; fin_cases j; rfl


theorem tensor_power_of_one : tensor_power n (fun _ => (1 : nMatrix m)) = 1 := by
  induction n with
    | zero =>
      simp [tensor_power]
      exact one_eq'
    | succ n ih =>
      rw [tensor_power]
      rw [ih]
      rw [one_kronecker_one, reindex₃_one]


theorem tensor_power_of_natCast { i : ℕ } : tensor_power n (fun _ => (i : nMatrix m)) = ↑(i ^ n) := by
  induction n with
    | zero => rw [tensor_power_zero]; rw [Nat.pow_zero i, Nat.cast_one]; exact one_eq
    | succ n ih => rw [tensor_power, ih, kronecker_natCast_natCast, reindex₃_natCast, ← Nat.pow_succ]


theorem tensor_power_smul (M : nMatrix m) (c : ℕ)
  : tensor_power n (fun _ => c • M) = c ^ n • tensor_power n (fun _ => M) := by
  induction n with
    | zero => simp [tensor_power]
    | succ n ih =>
      rw [tensor_power, tensor_power, ih, smul_kronecker, kronecker_smul, ← smul_assoc, smul_reindex₃]
      rw [Nat.pow_succ, smul_eq_mul]


theorem tensor_power_mul (M : ℕ -> nMatrix' m m') (N : ℕ -> nMatrix' m' o)
  : tensor_power n M * tensor_power n N = tensor_power (n) (λ i => M i * N i) := by
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
theorem tensor_power_one {m m' : ℕ} { gates : ℕ -> nMatrix' m m' } :
    reindex₂ (tensor_power 1 gates) = gates 1 := by
  sorry


-- Slice a tensor power in two pieces
theorem tensor_power_slice (gates : ℕ -> nMatrix' m m') :
    tensor_power (n + o) gates =
    reindex₅ (tensor_power n gates ⊗ₖ tensor_power o (fun i => gates (n + i))) :=  by
  sorry


-- Turn a single tensor_power' into a tensor_power' of a tensor_power'
theorem tensor_power_of_tensor_power (M : nMatrix' m m') :
    tensor_power' (n * o) M = reindex₄ (tensor_power' o (tensor_power' n M)) := by
  sorry


end TensorPower
end Circuits
