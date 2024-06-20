import «QuantumLean».Data.Circuits.Qubits
import «QuantumLean».Gates.Hadamard

open Circuits
open Gates

namespace Deutsch


def Oₛ (a b : Bool) : nMatrix 1 := !![(-1) ^ a.toNat, 0; 0, (-1) ^ b.toNat]
def Outcome (a b : Bool): Qubit 1 := !![(-1) ^ a.toNat + (-1) ^ b.toNat, (-1) ^ a.toNat - (-1) ^ b.toNat]


theorem DeutschAlgorithm (a b : Bool) : QZero * H * (Oₛ a b) * H = Outcome a b := by
  rw [QZero, H, Oₛ, Outcome]
  fin_cases a <;> fin_cases b <;> norm_num


end Deutsch
