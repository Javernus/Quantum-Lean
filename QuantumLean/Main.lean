-- import Mathlib.Tactic.LibrarySearch

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Notation
import Mathlib.Data.Complex.Basic

-- Import the gates
import «QuantumLean».Hadamard
import «QuantumLean».PauliGates

open Matrix
open Complex


theorem XX : XGate * XGate = 1 := by decide
theorem ZZ : ZGate * ZGate = 1 := by decide

theorem HZHeqX : Hadamard 1 * ZGate * Hadamard 1 = 2 * XGate := by decide
theorem HXHeqZ : Hadamard 1 * XGate * Hadamard 1 = 2 * ZGate := by decide

-- Create the Oracle for the Deutsch Algorithm, i.e. O(a, b) = !![-1^a, 0; 0, 1^b] where a, b ∈ {0, 1}
@[simp]
def Oracle (a b : Bool) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![(-1)^(a.toNat), 0; 0, (-1)^(b.toNat)]


@[simp]
def PlusQbit : Matrix (Fin 1) (Fin 2) ℤ := !![1, 1]


@[simp]
def Measure (q : Matrix (Fin 1) (Fin 2) ℤ) : Bool :=
  (q 0 0) = 0

-- The Deutsch Algorithm
theorem DeutschAlgorithm (a b : Bool) : Measure (PlusQbit * (Oracle a b) * Hadamard 1) = (a != b) :=
  by
    cases a; cases b;
    decide
    decide
    cases b;
    decide
    decide

-- theorem DeutschNew (a b : Bool) : Hadamard 1 * (Oracle a b) * Hadamard 1 = 2 * (-1)^(a.toNat) * XGate^(a.toNat + b.toNat) :=
--   by
--     cases a; cases b;
--     simp [XGate, Oracle, PlusQbit, Hadamard 1, mul_apply]
--     rw [ofNat_fin_two]
--     norm_num
--     simp [XGate, Oracle, PlusQbit, Hadamard 1, mul_apply]
--     rw [ofNat_fin_two]
--     norm_num
--     cases b;
--     simp [XGate, Oracle, PlusQbit, Hadamard 1, mul_apply]
--     rw [ofNat_fin_two]
--     norm_num
--     simp [XGate, Oracle, PlusQbit, Hadamard 1, mul_apply]
--     rw [ofNat_fin_two]
--     norm_num


-- Create a theorem with inputs a and b which are either 0 or 1 (Natural number type)
