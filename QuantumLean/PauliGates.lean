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

section XGate

def X : nMatrix 1 := !![0, 1; 1, 0]
def XGate (n : ℕ) := pow_kronecker n X


theorem XGate_Identity : (X * X) = (1 : ℕ) := by
  simp [X, mul_apply, Circuits.one_fin_two]


theorem X_mul_X : (XGate n) * (XGate n) = (1 : ℕ) := by
  rw [XGate, ← pow_kronecker_mul, XGate_Identity, pow_kronecker_of_natCast, one_pow]


end XGate
section YGate


def Y : nMatrix 1 := !![0, -I; I, 0]
def YGate (n : ℕ) := pow_kronecker n Y


theorem YGate_Identity : (Y * Y) = (1 : ℕ) := by
  simp [Y, mul_apply, Circuits.one_fin_two]


theorem Y_mul_Y : (YGate n) * (YGate n) = (1 : ℕ) := by
  rw [YGate, ← pow_kronecker_mul, YGate_Identity, pow_kronecker_of_natCast, one_pow]


end YGate
section ZGate


def Z : nMatrix 1 := !![1, 0; 0, -1]
def ZGate (n : ℕ) := pow_kronecker n Z


theorem ZGate_Identity : (Z * Z) = (1 : ℕ) := by
  simp [Z, mul_apply, Circuits.one_fin_two]


theorem Z_mul_Z : (ZGate n) * (ZGate n) = (1 : ℕ) := by
  rw [ZGate, ← pow_kronecker_mul, ZGate_Identity, pow_kronecker_of_natCast, one_pow]

end ZGate
end Pauli
