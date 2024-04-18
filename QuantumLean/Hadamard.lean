import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Notation
import Mathlib.Data.Matrix.Kronecker
import Mathlib.Data.Complex.Basic

import «QuantumLean».Data.Circuits.Basic
import «QuantumLean».Data.Circuits.VariableDimensions
import «QuantumLean».Data.Matrix.Kronecker

open Matrix
open Kronecker
open Circuits


section Hadamard
variable { n : ℕ }


def H : nMatrix 1 := !![1, 1; 1, -1]
def Hadamard (n : ℕ) := pow_kronecker n (H)


theorem hadamard_Identity : H * H = (2 : ℕ) := by
  simp [H, mul_apply, ofNat_fin_two]
  norm_num


theorem H_mul_H : Hadamard n * Hadamard n = (2 ^ n : ℕ) := by
      rw [Hadamard, ← pow_kronecker_mul, hadamard_Identity, pow_kronecker_of_natCast]

end Hadamard


-- Mathlib Data Finset Prod
