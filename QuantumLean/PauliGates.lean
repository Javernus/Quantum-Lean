import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Notation
import Mathlib.Data.Matrix.Kronecker
import Mathlib.Data.Complex.Basic

import «QuantumLean».Data.Circuits.Basic
import «QuantumLean».Data.Matrix.Kronecker

open Matrix
open Kronecker
open Complex
open Circuits

section Pauli
variable { n : ℕ }

section XGate


def XGate : (n : ℕ) -> Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ
  | 0 => 1
  | (n + 1) => reindex (XGate n ⊗ₖ !![0, 1; 1, 0])


theorem XGate_Identity : (!![0, 1; 1, 0] * !![0, 1; 1, 0]) = ((1 : ℕ) : Matrix (Fin 2) (Fin 2) ℂ) := by
  simp [mul_apply, one_fin_two]


theorem X_mul_X : (XGate n) * (XGate n) = (1 : ℕ) := by
  induction n with
    | zero => simp [XGate]
    | succ n ih =>
      rw [XGate, ← reindex_mul, ← mul_kronecker_mul, ih]
      rw [XGate_Identity]
      rw [kronecker_natCast_natCast, reindex_natCast]


end XGate
section YGate


def YGate : (n : ℕ) -> Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ
  | 0 => 1
  | (n + 1) => reindex (YGate n ⊗ₖ !![0, -I; I, 0])


theorem YGate_Identity : (!![0, -I; I, 0] * !![0, -I; I, 0]) = ((1 : ℕ) : Matrix (Fin 2) (Fin 2) ℂ) := by
  simp [mul_apply, one_fin_two]


theorem Y_mul_Y : (YGate n) * (YGate n) = (1 : ℕ) := by
  induction n with
    | zero => simp [YGate]
    | succ n ih =>
      rw [YGate, ← reindex_mul, ← mul_kronecker_mul, ih]
      rw [YGate_Identity]
      rw [kronecker_natCast_natCast, reindex_natCast]


end YGate
section ZGate


def ZGate : (n : ℕ) -> Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ
  | 0 => 1
  | (n + 1) => reindex (ZGate n ⊗ₖ !![1, 0; 0, -1])


theorem ZGate_Identity : (!![1, 0; 0, -1] * !![1, 0; 0, -1]) = ((1 : ℕ) : Matrix (Fin 2) (Fin 2) ℂ) := by
  simp [mul_apply, one_fin_two]


theorem Z_mul_Z : (ZGate n) * (ZGate n) = (1 : ℕ) := by
  induction n with
    | zero => simp [ZGate]
    | succ n ih =>
      rw [ZGate, ← reindex_mul, ← mul_kronecker_mul, ih]
      rw [ZGate_Identity]
      rw [kronecker_natCast_natCast, reindex_natCast]

end ZGate
end Pauli
