-- import Lean.Meta.Tactic.LibrarySearch
-- import Aesop.Main

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Notation
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Complex.Exponential

-- Import the gates
import «QuantumLean».Data.Circuits.Basic
import «QuantumLean».Data.Circuits.Qubits
import «QuantumLean».Data.Matrix.Kronecker
import «QuantumLean».Gates.Conditional
import «QuantumLean».Gates.Hadamard
import «QuantumLean».Gates.PauliGates

open Matrix
open Complex
open Kronecker
open Circuits


namespace Deutsch


def Oₛ (a b : Bool) : nMatrix 1 := !![(-1) ^ a.toNat, 0; 0, (-1) ^ b.toNat]
def Outcome (a b : Bool): Qubit 1 := !![(-1) ^ a.toNat + (-1) ^ b.toNat, (-1) ^ a.toNat - (-1) ^ b.toNat]


theorem DeutschAlgorithm (a b : Bool) : QZero * H * (Oₛ a b) * H = Outcome a b := by
  rw [QZero, H, Oₛ, Outcome]
  fin_cases a <;> fin_cases b <;> norm_num


end Deutsch
namespace BernsteinVazirani


def Oracle (sᵢ : Bool) : nMatrix 1 := Z ^ sᵢ.toNat
def Oracleₛ (s : ℕ -> Bool) : (i : ℕ) -> nMatrix 1 := fun i => Oracle (s i)
def Outcome (s : ℕ -> Bool) : (i : ℕ) -> Qubit 1 := fun i => QZero * 2 • X ^ (s i).toNat


theorem sᵢ_eq_zero : H * Z ^ Bool.toNat false * H = 2 • X ^ Bool.toNat false := by
  rw [Bool.toNat_false, pow_zero, mul_one, H_Identity, pow_zero, @nsmul_one]


theorem sᵢ_eq_one : (H * Z ^ Bool.toNat true * H) = 2 • X ^ Bool.toNat true := by
  rw [Bool.toNat_true]
  simp only [pow_one]
  exact HZHeqX'


theorem BernsteinVaziraniAlgorithm (s : ℕ -> Bool) : QZeroₙ n * (Hₙ n * (tensor_power n (Oracleₛ s)) * Hₙ n) = tensor_power n (Outcome s) := by
  rw [QZeroₙ, Hₙ, tensor_power_mul, tensor_power_mul, tensor_power_mul]
  induction n with
    | zero => rw [Nat.zero_eq, tensor_power, tensor_power]
    | succ n ih =>
      -- ih : (tensor_power n fun i ↦ QZero * (H * Oracleₛ s i * H)) = tensor_power n (Outcome s)
      rw [tensor_power, tensor_power]
      -- (tensor_power n fun i ↦ QZero * (H * Oracleₛ s i * H)) ⊗ₖ (Oracleₛ s i * H)
      -- = (tensor_power n (Outcome s)) ⊗ₖ (Outcome s (n + 1))
      rw [Oracleₛ, Oracle, Outcome]
      cases (s (n + 1));
      rw [ih, sᵢ_eq_zero]
      rw [ih, sᵢ_eq_one]

end BernsteinVazirani


-- Matrix def with vector support
-- Prove BV on |0>
-- 1 out of 4 Grover's
  -- CX, CZ, CCX?



-- Oracle:
-- diagonal 1, 1, 1, -1 (- in any position based on s)
-- Make sure s can only give a single number

-- After Oracle:
-- X-H-C-H
-- X-I-X-I

section OneOfFourGrover

abbrev sType := Fin 4


@[simp]
def Oracle (s : sType) : sType -> ℂ := fun n => (-1) ^ ((s == n).toNat)

/-- s is a number from 1 to 4 -/
def Oracleₛ (s : sType) : nMatrix 2 := !![Oracle s 0, 0, 0, 0; 0, Oracle s 1, 0, 0; 0, 0, Oracle s 2, 0; 0, 0, 0, Oracle s 3]

@[simp]
def O_final (s n : sType) : ℂ := 4 • (s == n).toNat


@[simp]
def Oracle_final (s : sType) : Qubit 2 := !![O_final s 0, O_final s 1, O_final s 2, O_final s 3]
def Oracle_final' (s : sType) : Qubit 2 := Q (O_final s)


theorem O_eq_O {s : sType} : Oracle_final s = Oracle_final' s := by
  simp [Oracle_final, Oracle_final']
  ext i j
  fin_cases i; fin_cases j <;> simp [Q]


theorem OneOfFourGrover (s : sType) : Q₀ * H₂ * Oracleₛ s * X₂ * H₁ * CX * H₁ = Oracle_final' s := by
  rw [Q₀, H₂, X₂, Oracleₛ, H₁, CX, ← O_eq_O, Oracle_final]
  simp only [QCount, Nat.pow_zero, nMatrix, nMatrix', Oracle, Fin.isValue, cons_mul, vecMul_cons,
    head_cons, one_smul, tail_cons, empty_vecMul, add_zero, add_cons, zero_add, empty_add_empty,
    neg_smul, neg_cons, neg_zero, neg_empty, empty_mul, Equiv.symm_apply_apply, smul_cons,
    smul_eq_mul, mul_zero, mul_one, smul_empty, mul_neg, neg_neg, neg_add_rev, O_final,
    Fin.reduceBEq, Bool.toNat_false, CharP.cast_eq_zero, beq_self_eq_true, Bool.toNat_true,
    Nat.cast_ofNat]
  -- norm_num
  fin_cases s <;> simp <;> norm_num


def F2F2_eq_F4 : ((Fin 2) × (Fin 2)) ≃ Fin 4 := by
  exact @finProdFinEquiv 2 2


def rei (A : Matrix ((Fin 2) × (Fin 2)) ((Fin 2) × (Fin 2)) ℤ) : Matrix (Fin 4) (Fin 4) ℤ :=
  Matrix.reindex F2F2_eq_F4 F2F2_eq_F4 A

def nI : Matrix (Fin 2) (Fin 2) ℤ := !![1, 0; 0, 1]
def nX : Matrix (Fin 2) (Fin 2) ℤ := !![0, 1; 1, 0]
def nH : Matrix (Fin 2) (Fin 2) ℤ := !![1, 1; 1, -1]
def nCX : Matrix (Fin 4) (Fin 4) ℤ := !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0]
def nCZ : Matrix (Fin 4) (Fin 4) ℤ := !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, -1]
def Q0 : Matrix (Fin 4) (Fin 1) ℤ := !![1; 0; 0; 0]
def Q0' : Matrix (Fin 1) (Fin 4) ℤ := !![1, 0, 0, 0]

#eval Q0' * rei (nH ⊗ₖ nH) * rei (nX ⊗ₖ nX) * nCZ * rei (nX ⊗ₖ nX) * rei (nX ⊗ₖ nX) * rei (nH ⊗ₖ nI) * nCX * rei (nH ⊗ₖ nI)
#eval rei (nH ⊗ₖ nI) * nCX * rei (nH ⊗ₖ nI) * rei (nX ⊗ₖ nX) * rei (nX ⊗ₖ nX) * nCZ * rei (nX ⊗ₖ nX) * rei (nH ⊗ₖ nH) * Q0
#eval rei (nX ⊗ₖ nX) * nCZ * rei (nX ⊗ₖ nX)
#eval rei (nH ⊗ₖ nI)

  -- fin_cases s <;> norm_num



end OneOfFourGrover
