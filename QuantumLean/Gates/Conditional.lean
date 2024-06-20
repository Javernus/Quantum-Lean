import «QuantumLean».Data.Circuits.Reindex
import «QuantumLean».Data.Circuits.TensorPower
import «QuantumLean».Gates.Hadamard

open Kronecker
open Circuits

/-
Controlled gates. This file contains a set of definitions regarding controlled gates:

- CX/XC: the controlled NOT gate, and reversed controlled NOT gate.
- CZ: the controlled Z gate.
- CXₙ/CZₙ: the tensor power of CX/CZ.
- SWAP: a circuit applying CX and XC to swap the values of two qubits.

This file also contains identity theorems.

- CX/XC/CZ_Identity: the identity for square of the gates.
- CX_mul_CX/CZ_mul_CZ: the identity for the CXₙ/CZₙ definitions.
- SWAP_mul_SWAP: the identity for SWAP multiplied by itself.
-/

namespace Gates
section CNOT


-- Make it n-qubit with props for control qubit and affected qubit(s?)
def CX : nGate 2 := !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0]
def XC : nGate 2 := !![1, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0; 0, 1, 0, 0]
def CXₙ (n : ℕ) := tensor_power' n CX


theorem CX_Identity : (CX * CX) = (1 : ℕ) := by
  simp [CX]

  -- rw [← @diagonal_one]
  ext i j
  fin_cases i <;> fin_cases j <;> rfl


theorem XC_Identity : (XC * XC) = (1 : ℕ) := by
  simp [XC]

  -- rw [← @diagonal_one]
  ext i j
  fin_cases i <;> fin_cases j <;> rfl


theorem CX_mul_CX : (CXₙ n) * (CXₙ n) = (1 : ℕ) := by
  rw [CXₙ, tensor_power_mul, CX_Identity, tensor_power_of_natCast, one_pow]


-- Make it n-qubit with props for control qubit and affected qubit(s?)
def CZ : nGate 2 := !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, -1]
def CZₙ (n : ℕ) := tensor_power' n CZ


theorem CZ_Identity : (CZ * CZ) = (1 : ℕ) := by
  simp [CZ]

  -- rw [← @diagonal_one]
  ext i j
  fin_cases i <;> fin_cases j <;> rfl


theorem CZ_mul_CZ : (CZₙ n) * (CZₙ n) = (1 : ℕ) := by
  rw [CZₙ, tensor_power_mul, CZ_Identity, tensor_power_of_natCast, one_pow]


def SWAP : nGate 2 := CX * XC * CX


theorem SWAP_mul_SWAP : SWAP * SWAP = (1 : ℕ) := by
  simp [SWAP, CX, XC]
  ext i j
  fin_cases i <;> fin_cases j <;> rfl


end CNOT
end Gates
