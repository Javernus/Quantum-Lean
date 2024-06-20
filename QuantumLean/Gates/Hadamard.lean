import «QuantumLean».Data.Circuits.Reindex
import «QuantumLean».Data.Circuits.TensorPower
import «QuantumLean».Data.Matrix.Kronecker

open Kronecker
open Circuits

/-
The Hadamard gate. This file contains a set of definitions regarding the Hadamard gate:

- H: the single qubit Hadamard gate. Non-normalised.
- HI: the H ⊗ₖ I gate for two qubits.
- IH: the I ⊗ₖ H gate for two qubits.
- HH: the H ⊗ₖ H gate for two qubits.
- Hₙ: the n-qubit tensor power of H.
- Hᵢ: H applied only to qubit i.

This file also contains the identity theorem for Hadamard: H * H = I.

- H_Identity: the identity for the H definition.
- H_mul_H: the identity for the Hₙ definition.
-/

namespace Gates
section Hadamard

variable { n : ℕ }


def H : nGate 1 := !![1, 1; 1, -1]
def HI : nGate 2 := !![1, 0, 1, 0; 0, 1, 0, 1; 1, 0, -1, 0; 0, 1, 0, -1]
def IH : nGate 2 := !![1, 1, 0, 0; 1, -1, 0, 0; 0, 0, 1, 1; 0, 0, 1, -1]
def HH : nGate 2 := !![1, 1, 1, 1; 1, -1, 1, -1; 1, 1, -1, -1; 1, -1, -1, 1]

def Hₙ (n : ℕ) := tensor_power' n H
def Hᵢ (n i : ℕ) := apply_at n i H


theorem H_Identity : H * H = (2 : ℕ) := by
  norm_num [H]
  simp only [Matrix.ofNat_fin_two]

theorem H_mul_H : Hₙ n * Hₙ n = (2 ^ n : ℕ) := by
  rw [Hₙ, tensor_power_mul, H_Identity, tensor_power_of_natCast]


end Hadamard
end Gates
