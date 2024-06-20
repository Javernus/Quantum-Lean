import «QuantumLean».Data.Circuits.Qubits
import «QuantumLean».Gates.Hadamard

open Circuits
open Gates

/-
The Deutsch algorithm is a simple one-qubit algorithm that attempts to find the XOR of f(0) and f(1). Its oracle has the following specifications:

- Secret input:     s ∈ {0, 1}^2
- Function mapping: {0, 1} ↦ {0, 1}
- Function:         f(t) = s_{t}

Its oracle, as can be seen below, is defined as
!![(-1)^(s_0),          0
            0, (-1)^(s_1)]

The Deutsch algorithm can determine f(0) ⊕ f(1) with a single access to the oracle. Its circuit is as follows:

H * Oₛ * H

We then measure, which we do in Lean by equating it to the qubit that defines the outcome based on s.
-/

namespace Deutsch


def Oₛ (a b : Bool) : nGate 1 :=
  !![(-1) ^ a.toNat,              0;
                  0, (-1) ^ b.toNat]

def Outcome (a b : Bool): nQubit 1 :=
  !![(-1) ^ a.toNat + (-1) ^ b.toNat,
     (-1) ^ a.toNat - (-1) ^ b.toNat]


theorem DeutschAlgorithm (a b : Bool) : QZero * H * (Oₛ a b) * H = Outcome a b := by
  rw [QZero, H, Oₛ, Outcome]
  fin_cases a <;> fin_cases b <;> norm_num


end Deutsch
