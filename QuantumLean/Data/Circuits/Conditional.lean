import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Notation
import Mathlib.Data.Matrix.Kronecker

import «QuantumLean».Data.Circuits.Basic
import «QuantumLean».Data.Circuits.VariableDimensions

open Matrix
open Kronecker
open Circuits

section CNOT

-- Make it n-qubit with props for control qubit and affected qubit(s?)
def CX : nMatrix 2 := !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0]
def XC : nMatrix 2 := !![1, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0; 0, 1, 0, 0]
def CXₙ (n : ℕ) := pow_kronecker n CX


theorem CXₙ_Identity : (CX * CX) = (1 : ℕ) := by
  simp [CX]

  -- rw [← @diagonal_one]
  ext i j
  fin_cases i <;> fin_cases j <;> rfl


theorem XCₙ_Identity : (XC * XC) = (1 : ℕ) := by
  simp [XC]

  -- rw [← @diagonal_one]
  ext i j
  fin_cases i <;> fin_cases j <;> rfl


theorem CX_mul_CX : (CXₙ n) * (CXₙ n) = (1 : ℕ) := by
  rw [CXₙ, ← pow_kronecker_mul, CXₙ_Identity, pow_kronecker_of_natCast, one_pow]


def SWAP : nMatrix 2 := CX * XC * CX


theorem SWAP_mul_SWAP : SWAP * SWAP = (1 : ℕ) := by
  simp [SWAP, CX, XC]
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

end CNOT
