import «QuantumLean».Data.Circuits.Abbreviations
import «QuantumLean».Data.Circuits.TensorPower

open Matrix
open Circuits


namespace Circuits
section Qubits

/-- A vector with values of s n -/
def Q {n : ℕ} (s : QCount n -> ℂ) : Qubit n := of fun _ i => s i
def Q' (n : ℕ) (s : ℂ) : Qubit n := of fun _ _ => s

def QZero : Qubit 1 := !![1, 0]
def QZeroₙ (n : ℕ) := tensor_power' n QZero
def Q₀ : Qubit 2 := !![1, 0, 0, 0]

end Qubits
end Circuits
