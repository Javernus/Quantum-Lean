-- import Lean.Meta.Tactic.LibrarySearch
-- import Aesop.Main

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Notation
import Mathlib.Data.Complex.Basic

-- Import the gates
import «QuantumLean».Data.Circuits.Basic
import «QuantumLean».Data.Matrix.Kronecker
import «QuantumLean».Data.Complex.Representation

open Matrix
open Complex
open Kronecker
open Circuits


variable {m n : Type*} {R : Type*} [Semiring R]


def reindexₖ (A : Matrix m n R) : Matrix (Fin 1 → m) (Fin 1 → n) R :=
  reindex (Equiv.funUnique (Fin 1) m).symm (Equiv.funUnique (Fin 1) n).symm A


def powKronecker (k : ℕ) (A : Matrix m n R) :
    Matrix (Fin k → m) (Fin k → n) R :=
  fun fm fn => ((List.finRange k).map fun i => A (fm i) (fn i)).prod


-- theorem powKronecker_one { A : Matrix m n R } : (powKronecker 1 A) = reindexₖ A := by
--   apply?
--   rw [kronecker_natOne i, one_kronecker_one, smul_reindex, reindex_one]
--   norm_num


@[simp]
def tensor_power {m : ℕ} (n : ℕ) (gates : ℕ -> nMatrix m) : nMatrix (m * n) :=
  match n with
    | 0 => 1
    | (n + 1) => reindex₃ (tensor_power n gates ⊗ₖ gates n)


abbrev tensor_power' {m : ℕ} (n : ℕ) (M : nMatrix m) : nMatrix (m * n) := tensor_power n (fun _ => M)

theorem tensor_power_zero {n : ℕ} { gates : ℕ -> nMatrix n } : tensor_power 0 gates = 1 := by
  simp [tensor_power]


theorem tensor_power_one { i n : ℕ } : tensor_power 1 (fun _ => (i : nMatrix n)) = i := by
  rw [tensor_power, tensor_power_zero]
  rw [kronecker_natCast, one_kronecker_one, smul_reindex₃, reindex₃_one]
  norm_num


theorem tensor_power_mul { m n : ℕ } (M N : ℕ -> nMatrix m) : tensor_power n (M * N) = tensor_power n M * tensor_power n N := by
  induction n with
    | zero => simp
    | succ n ih =>
      rw [tensor_power]
      rw [tensor_power]
      rw [tensor_power]
      rw [← reindex₃_mul]
      rw [← mul_kronecker_mul]
      rw [ih]
      rfl


theorem tensor_power_of_one { m n : ℕ } : tensor_power n (fun _ => (1 : nMatrix m)) = 1 := by
  induction n with
    | zero => simp [tensor_power']
    | succ n ih =>
      rw [tensor_power]
      rw [ih]
      rw [one_kronecker_one, reindex₃_one]


theorem tensor_power_of_natCast { i m n : ℕ } : tensor_power n (fun _ => (i : nMatrix m)) = ↑(i ^ n) := by
  induction n with
    | zero => rw [tensor_power_zero]; rw [Nat.pow_zero i, Nat.cast_one]
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
