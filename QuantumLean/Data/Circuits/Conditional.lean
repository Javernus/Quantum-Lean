import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Notation
import Mathlib.Data.Matrix.Kronecker

import «QuantumLean».Data.Circuits.Basic
import «QuantumLean».Data.Circuits.VariableDimensions

open Matrix
open Kronecker
open Circuits

section CNOT

def CX : nMatrix 2 := !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0]
def CNOT (n : ℕ) := pow_kronecker n CX


theorem CNOT_Identity : (CX * CX) = (1 : ℕ) := by
  simp [CX]

  -- rw [← @diagonal_one]
  ext i j
  fin_cases i <;> fin_cases j <;> rfl


theorem CX_mul_CX : (CNOT n) * (CNOT n) = (1 : ℕ) := by
  rw [CNOT, ← pow_kronecker_mul, CNOT_Identity, pow_kronecker_of_natCast, one_pow]


end CNOT
