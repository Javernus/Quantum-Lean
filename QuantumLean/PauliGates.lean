import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Notation
import Mathlib.Data.Matrix.Kronecker
import Mathlib.Data.Complex.Basic

import «QuantumLean».Data.Circuits.Basic
import «QuantumLean».Data.Circuits.VariableDimensions
import «QuantumLean».Data.Matrix.Kronecker
import «QuantumLean».Data.Complex.Representation

open Matrix
open Kronecker
open Complex
open Circuits

section Pauli
variable { n : ℕ }

section Xₙ

def X : nMatrix 1 := !![0, 1; 1, 0]
def Xₙ (n : ℕ) := tensor_power' n X


theorem X_Identity : (X * X) = (1 : ℕ) := by
  simp [X, mul_apply, Circuits.one_fin_two]


theorem X_mul_X : (Xₙ n) * (Xₙ n) = (1 : ℕ) := by
  rw [Xₙ, ← tensor_power_mul, @Pi.mul_def, X_Identity, tensor_power_of_natCast, one_pow]


end Xₙ
section Yₙ


def Y : nMatrix 1 := !![0, -I; I, 0]
def Yₙ (n : ℕ) := tensor_power' n Y


theorem Y_Identity : (Y * Y) = (1 : ℕ) := by
  simp [Y, mul_apply, Circuits.one_fin_two]


theorem Y_mul_Y : (Yₙ n) * (Yₙ n) = (1 : ℕ) := by
  rw [Yₙ, ← tensor_power_mul, @Pi.mul_def, Y_Identity, tensor_power_of_natCast, one_pow]


end Yₙ
section Zₙ


def Z : nMatrix 1 := !![1, 0; 0, -1]
def Zₙ (n : ℕ) := tensor_power' n Z


theorem Z_Identity : (Z * Z) = (1 : ℕ) := by
  simp [Z, mul_apply, Circuits.one_fin_two]


theorem Z_mul_Z : (Zₙ n) * (Zₙ n) = (1 : ℕ) := by
  rw [Zₙ, ← tensor_power_mul, @Pi.mul_def, Z_Identity, tensor_power_of_natCast, one_pow]

end Zₙ
end Pauli
