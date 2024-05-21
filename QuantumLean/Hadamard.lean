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
def Hₙ (n : ℕ) := tensor_power' n H


theorem H_Identity : H * H = (2 : ℕ) := by
  simp [H, mul_apply, ofNat_fin_two]
  norm_num


theorem H_mul_H : Hₙ n * Hₙ n = (2 ^ n : ℕ) := by
  rw [Hₙ, ← tensor_power_mul, @Pi.mul_def, H_Identity, tensor_power_of_natCast]

end Hadamard


-- Mathlib Data Finset Prod
