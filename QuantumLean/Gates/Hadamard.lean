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
def H₁ : nMatrix 2 := !![1, 0, 1, 0; 0, 1, 0, 1; 1, 0, -1, 0; 0, 1, 0, -1]
def IH : nMatrix 2 := !![1, 1, 0, 0; 1, -1, 0, 0; 0, 0, 1, 1; 0, 0, 1, -1]
def H₂ : nMatrix 2 := !![1, 1, 1, 1; 1, -1, 1, -1; 1, 1, -1, -1; 1, -1, -1, 1]
def Hₙ (n : ℕ) := tensor_power' n H
def Hᵢ (n i : ℕ) := apply_at n i H


theorem H_Identity : H * H = (2 : ℕ) := by
  norm_num [H]
  simp only [ofNat_fin_two]

theorem H_mul_H : Hₙ n * Hₙ n = (2 ^ n : ℕ) := by
  rw [Hₙ, tensor_power_mul, H_Identity, tensor_power_of_natCast]

end Hadamard


-- Mathlib Data Finset Prod
