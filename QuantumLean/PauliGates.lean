import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Notation
import Mathlib.Data.Matrix.Kronecker
import Mathlib.Data.Complex.Basic

import «QuantumLean».Data.Circuits.Basic
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
def XGate : (n : ℕ) -> nMatrix n
  | 0 => 1
  | (n + 1) => reindex (XGate n ⊗ₖ X)


theorem XGate_Identity : (X * X) = (1 : ℕ) := by
  simp [X, mul_apply, Circuits.one_fin_two]


theorem X_mul_X : (XGate n) * (XGate n) = (1 : ℕ) := by
  induction n with
    | zero => simp [XGate]
    | succ n ih =>
      rw [XGate, ← reindex_mul, ← mul_kronecker_mul, ih]
      rw [XGate_Identity]
      rw [kronecker_natCast_natCast, reindex_natCast]


#eval XGate 1

end XGate
section YGate


def Y : nMatrix 1 := !![0, -I; I, 0]
def YGate : (n : ℕ) -> nMatrix n
  | 0 => 1
  | (n + 1) => reindex (YGate n ⊗ₖ Y)


theorem YGate_Identity : (Y * Y) = (1 : ℕ) := by
  simp [Y, mul_apply, Circuits.one_fin_two]


theorem Y_mul_Y : (YGate n) * (YGate n) = (1 : ℕ) := by
  induction n with
    | zero => simp [YGate]
    | succ n ih =>
      rw [YGate, ← reindex_mul, ← mul_kronecker_mul, ih]
      rw [YGate_Identity]
      rw [kronecker_natCast_natCast, reindex_natCast]


end YGate
section ZGate


def Z : nMatrix 1 := !![1, 0; 0, -1]
def ZGate : (n : ℕ) -> nMatrix n
  | 0 => 1
  | (n + 1) => reindex (ZGate n ⊗ₖ Z)


theorem ZGate_Identity : (Z * Z) = (1 : ℕ) := by
  simp [Z, mul_apply, Circuits.one_fin_two]


theorem Z_mul_Z : (ZGate n) * (ZGate n) = (1 : ℕ) := by
  induction n with
    | zero => simp [ZGate]
    | succ n ih =>
      rw [ZGate, ← reindex_mul, ← mul_kronecker_mul, ih]
      rw [ZGate_Identity]
      rw [kronecker_natCast_natCast, reindex_natCast]

end ZGate
end Pauli
