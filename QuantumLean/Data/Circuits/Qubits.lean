import «QuantumLean».Data.Circuits.Types
import «QuantumLean».Data.Circuits.TensorPower

open Matrix
open Circuits

/-
This file defines the qubit definitions used in Quantum Lean. These are used in
proofs to define qubits.

- Q: a definition taking in (s : QCount n -> ℂ) and turning it into a qubit.
- QZero: the zero qubit |0>.
- QZero₂: a shorthand for |0> ⊗ₖ |0>.
- QZeroₙ: the zero qubit tensor power. (n : ℕ) as argument.
-/

namespace Circuits
section Qubits

/-- A vector with values of s n -/
def Q {n : ℕ} (s : QCount n -> ℂ) : nQubit n := of fun _ i => s i

def QZero : nQubit 1 := !![1, 0]
def QZero₂ : nQubit 2 := !![1, 0, 0, 0]
def QZeroₙ (n : ℕ) := tensor_power' n QZero

end Qubits
end Circuits
