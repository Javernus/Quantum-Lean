import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Notation
import Mathlib.Data.Matrix.Kronecker
import Mathlib.Data.Complex.Basic

import «QuantumLean».Data.Circuits.Basic
import «QuantumLean».Data.Matrix.Kronecker

open Matrix
open Kronecker
open Circuits


section Hadamard
variable { n : ℕ }


theorem hadamard_Identity : (!![1, 1; 1, -1]) * (!![1, 1; 1, -1]) = ((2 : ℕ) : Matrix (Fin 2) (Fin 2) ℂ) := by
  simp [mul_apply, ofNat_fin_two]
  norm_num


def Hadamard : (n : ℕ) -> Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ
  | 0 => 1
  | (n + 1) => reindex (Hadamard n ⊗ₖ !![1, 1; 1, -1])


-- In general, I am trying to prove H * H = I (× a constant) for Hadamard matrices
theorem H_mul_H : Hadamard n * Hadamard n = (2 ^ n : ℕ) := by
  induction n with
    | zero => simp [Hadamard]
    | succ n ih =>
      rw [Hadamard, ← reindex_mul, ← mul_kronecker_mul, ih]
      rw [hadamard_Identity]
      rw [kronecker_natCast_natCast, reindex_natCast]
      rfl

end Hadamard


-- Mathlib Data Finset Prod
-- Cartesian Product? In type def of Hadamard for size of matrix
-- Theorem that proves ⊗ₖ indices can be reindexed without any change to the matrix
