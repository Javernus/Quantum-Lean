-- import Lean.Meta.Tactic.LibrarySearch
-- import Aesop.Main

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Notation
import Mathlib.Data.Complex.Basic

-- Import the gates
import «QuantumLean».Data.Circuits.Basic
import «QuantumLean».Data.Matrix.Kronecker

open Matrix
open Complex
open Kronecker
open Circuits


variable {m n : Type*} {R : Type*} [Semiring R]


@[simp]
def tensor_power {m m' : ℕ} (n : ℕ) (gates : ℕ -> nMatrix' m m') : nMatrix' (m * n) (m' * n) :=
  match n with
    | 0 => !![1]
    | (n + 1) => reindex₃ (tensor_power n gates ⊗ₖ gates (n + 1))


abbrev tensor_power' {m : ℕ} (n : ℕ) (M : nMatrix m) : nMatrix (m * n) := tensor_power n (fun _ => M)


theorem tensor_power_zero {m m' : ℕ} { gates : ℕ -> nMatrix' m m' } : tensor_power 0 gates = !![1] := by
  simp [tensor_power]


theorem tensor_power_mul { m n : ℕ } (M N : ℕ -> nMatrix m)
  : tensor_power n (M * N) = tensor_power n M * tensor_power n N := by
  induction n with
    | zero => simp
    | succ n ih =>
      rw [tensor_power]
      rw [tensor_power]
      rw [tensor_power]
      rw [← reindex₃_mul]
      rw [← mul_kronecker_mul]
      rw [ih]
      rw [@Pi.mul_apply]


theorem one_eq { m : ℕ } : !![1] = (1 :  nMatrix' (m * Nat.zero) (m * Nat.zero)) := by
  ext i j
  fin_cases i; fin_cases j; rfl


theorem tensor_power_of_one { m n : ℕ } : tensor_power n (fun _ => (1 : nMatrix m)) = 1 := by
  induction n with
    | zero =>
      simp [tensor_power]
      exact one_eq
    | succ n ih =>
      rw [tensor_power]
      rw [ih]
      rw [one_kronecker_one, reindex₃_one]


theorem tensor_power_of_natCast { i m n : ℕ } : tensor_power n (fun _ => (i : nMatrix m)) = ↑(i ^ n) := by
  induction n with
    | zero => rw [tensor_power_zero]; rw [Nat.pow_zero i, Nat.cast_one]; exact one_eq
    | succ n ih => rw [tensor_power, ih, kronecker_natCast_natCast, reindex₃_natCast, ← Nat.pow_succ]


theorem tensor_power_smul { m n : ℕ } (M : nMatrix m) (c : ℕ)
  : tensor_power n (fun _ => c • M) = c ^ n • tensor_power n (fun _ => M) := by
  induction n with
    | zero => simp [tensor_power]
    | succ n ih =>
      rw [tensor_power, tensor_power, ih, smul_kronecker, kronecker_smul, ← smul_assoc, smul_reindex₃]
      rw [Nat.pow_succ, smul_eq_mul]


theorem tensor_power_mul_tensor_power { m n : ℕ } (M N : ℕ -> nMatrix m)
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
