import «QuantumLean».Data.Circuits.Qubits
import «QuantumLean».Gates.Conditional
import «QuantumLean».Gates.Hadamard
import «QuantumLean».Gates.Pauli

open Kronecker
open Circuits
open Gates

/-
The one-out-of-four Grover algorithm is a two-qubit algorithm that deterimines s using a single application of the oracle. Its oracle has the following specifications:

- Secret input:     s ∈ {0, 1}^2
- Function mapping: {0, 1}^2 ↦ {0, 1}
- Function:         f(t) = (t == s)

Its oracle, as can be seen below, is defined as
!![(-1)^(f(00)),            0,            0,            0,
              0, (-1)^(f(01)),            0,            0,
              0             0, (-1)^(f(10)),            0,
              0             0             0, (-1)^(f(11))]

Its circuit is as follows:

H⊗H * Oₛ * X⊗X * H⊗I * CX * H⊗I

We then measure, which we do in Lean by equating it to the qubit that defines the outcome based on s.
-/

section OneOfFourGrover

abbrev sType := Fin 4


def Oracle (s n : sType) : ℂ := (-1) ^ ((s == n).toNat)

/-- s is a number from 1 to 4 -/
def Oracleₛ (s : sType) : nGate 2 :=
  !![Oracle s 0,          0,          0,          0;
              0, Oracle s 1,          0,          0;
              0,          0, Oracle s 2,          0;
              0,          0,          0, Oracle s 3]


def Outcomeᵢ (s n : sType) : ℂ := 4 • (s == n).toNat
def Outcome (s : sType) : nQubit 2 := !![Outcomeᵢ s 0, Outcomeᵢ s 1, Outcomeᵢ s 2, Outcomeᵢ s 3]


theorem OneOfFourGrover (s : sType) : QZero₂ * HH * Oracleₛ s * XX * HI * CX * HI = Outcome s := by
  rw [QZero₂, HH, Oracleₛ, XX, HI, CX, Outcome]
  norm_num [Oracle]
  fin_cases s <;> {
    -- Turn the finite case objects into its natural number values
    simp only [Fin.reduceFinMk, Fin.isValue, Fin.reduceBEq, Bool.toNat_false, pow_zero, beq_self_eq_true, Bool.toNat_true, pow_one, add_left_neg, add_right_neg, add_zero, neg_neg, Outcomeᵢ]
    norm_num
  }


end OneOfFourGrover
