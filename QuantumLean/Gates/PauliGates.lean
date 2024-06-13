import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Notation
import Mathlib.Data.Matrix.Kronecker
import Mathlib.Data.Complex.Basic

import «QuantumLean».Data.Circuits.Basic
import «QuantumLean».Data.Circuits.VariableDimensions
import «QuantumLean».Data.Matrix.Kronecker
import «QuantumLean».Gates.Hadamard

open Matrix
open Kronecker
open Complex
open Circuits

section Pauli
variable { n : ℕ }

section Xₙ

def X : nMatrix 1 := !![0, 1; 1, 0]
def X₂ : nMatrix 2 := !![0, 0, 0, 1; 0, 0, 1, 0; 0, 1, 0, 0; 1, 0, 0, 0]
def Xₙ (n : ℕ) := tensor_power' n X
def Xᵢ (n i : ℕ) := apply_at n i X


theorem X_Identity : (X * X) = (1 : ℕ) := by
  norm_num [X]
  simp only [Circuits.one_fin_two]


theorem X_mul_X : (Xₙ n) * (Xₙ n) = (1 : ℕ) := by
  rw [Xₙ, ← tensor_power_mul, @Pi.mul_def, X_Identity, tensor_power_of_natCast, one_pow]


end Xₙ
section Yₙ


def Y : nMatrix 1 := !![0, -I; I, 0]
def Yₙ (n : ℕ) := tensor_power' n Y
def Yᵢ (n i : ℕ) := apply_at n i Y


theorem Y_Identity : (Y * Y) = (1 : ℕ) := by
  norm_num [Y]
  simp only [Circuits.one_fin_two]


theorem Y_mul_Y : (Yₙ n) * (Yₙ n) = (1 : ℕ) := by
  rw [Yₙ, ← tensor_power_mul, @Pi.mul_def, Y_Identity, tensor_power_of_natCast, one_pow]


end Yₙ
section Zₙ


def Z : nMatrix 1 := !![1, 0; 0, -1]
def Zₙ (n : ℕ) := tensor_power' n Z
def Zᵢ (n i : ℕ) := apply_at n i Z


theorem Z_Identity : (Z * Z) = (1 : ℕ) := by
  norm_num [Z]
  simp only [Circuits.one_fin_two]


theorem Z_mul_Z : (Zₙ n) * (Zₙ n) = (1 : ℕ) := by
  rw [Zₙ, ← tensor_power_mul, @Pi.mul_def, Z_Identity, tensor_power_of_natCast, one_pow]

end Zₙ
end Pauli

section CircuitLemmas
variable { n : ℕ }


theorem HXHeqZ' : H * X * H = 2 • Z := by
  rw [H, X, Z]
  norm_num


theorem HXHeqZ : Hₙ n * Xₙ n * Hₙ n = (2 ^ n : ℕ) • Zₙ n := by
  rw [Hₙ, Xₙ, ← tensor_power_mul, ← tensor_power_mul]
  nth_rw 2 [@Pi.mul_def]
  rw [@Pi.mul_def, HXHeqZ', tensor_power_smul, Zₙ]


theorem HZH_eq_X' : H * Z * H = 2 • X := by
  rw [H, Z, X]
  norm_num


theorem HZH_eq_X : Hₙ n * Zₙ n * Hₙ n = (2 ^ n : ℕ) • Xₙ n := by
  rw [Hₙ, Zₙ, ← tensor_power_mul, ← tensor_power_mul]
  nth_rw 2 [@Pi.mul_def]
  rw [@Pi.mul_def, HZH_eq_X', tensor_power_smul, Xₙ]


end CircuitLemmas
