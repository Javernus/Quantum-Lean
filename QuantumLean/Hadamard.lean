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


theorem hadamard_Identity : (!![1, 1; 1, -1]) * (!![1, 1; 1, -1]) = ((2 : ℕ) : nMatrix 1) := by
  simp [mul_apply, ofNat_fin_two]
  norm_num


def Hadamard : (n : ℕ) -> nMatrix n
  | 0 => 1
  | (n + 1) => reindex (Hadamard n ⊗ₖ !![1, 1; 1, -1])


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
