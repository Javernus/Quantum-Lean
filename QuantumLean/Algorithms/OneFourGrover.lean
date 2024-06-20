import «QuantumLean».Data.Circuits.Qubits
import «QuantumLean».Gates.Conditional
import «QuantumLean».Gates.Hadamard
import «QuantumLean».Gates.Pauli

open Kronecker
open Circuits
open Gates

section OneOfFourGrover

abbrev sType := Fin 4


def Oracle (s : sType) : sType -> ℂ := fun n => (-1) ^ ((s == n).toNat)

/-- s is a number from 1 to 4 -/
def Oracleₛ (s : sType) : nMatrix 2 :=
  !![Oracle s 0,          0,          0,          0;
              0, Oracle s 1,          0,          0;
              0,          0, Oracle s 2,          0;
              0,          0,          0, Oracle s 3]


def Outcomeᵢ (s n : sType) : ℂ := 4 • (s == n).toNat
def Outcome (s : sType) : Qubit 2 := !![Outcomeᵢ s 0, Outcomeᵢ s 1, Outcomeᵢ s 2, Outcomeᵢ s 3]


theorem OneOfFourGrover (s : sType) : Q₀ * H₂ * Oracleₛ s * X₂ * H₁ * CX * H₁ = Outcome s := by
  rw [Q₀, H₂, Oracleₛ, X₂, H₁, CX, Outcome]
  norm_num [Oracle]
  fin_cases s <;> {
    -- Turn the finite case objects into its natural number values
    simp only [Fin.reduceFinMk, Fin.isValue, Fin.reduceBEq, Bool.toNat_false, pow_zero, beq_self_eq_true, Bool.toNat_true, pow_one, add_left_neg, add_right_neg, add_zero, neg_neg, Outcomeᵢ]
    norm_num
  }

end OneOfFourGrover
