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


section CircuitLemmas
variable { n : ℕ }


theorem HZH_eq_X' : H * Z * H = 2 • X := by
  rw [H, Z, X]
  norm_num


theorem HZH_eq_X : Hₙ n * Zₙ n * Hₙ n = (2 ^ n : ℕ) • Xₙ n := by
  rw [Hₙ, Zₙ, ← tensor_power_mul, ← tensor_power_mul]
  nth_rw 2 [@Pi.mul_def]
  rw [@Pi.mul_def, HZH_eq_X', tensor_power_smul, Xₙ]


theorem HXHeqZ' : H * X * H = 2 • Z := by
  rw [H, X, Z]
  norm_num


theorem HXHeqZ : Hₙ n * Xₙ n * Hₙ n = (2 ^ n : ℕ) • Zₙ n := by
  rw [Hₙ, Xₙ, ← tensor_power_mul, ← tensor_power_mul]
  nth_rw 2 [@Pi.mul_def]
  rw [@Pi.mul_def, HXHeqZ', tensor_power_smul, Zₙ]

end CircuitLemmas


namespace Deutsch


def Oracle (a b : Bool) : nMatrix 1 := !![a.toNat, 0; 0, b.toNat]
def Bool_eq (a b : Bool) : ℕ := (a == b).toNat
def D_final (a b : Bool) : nMatrix 1 := !![a.toNat + b.toNat, a.toNat - b.toNat; a.toNat - b.toNat, a.toNat + b.toNat]


theorem DeutschAlgorithm (a b : Bool) : H * (Oracle a b) * H = D_final a b := by
  rw [H, Oracle, D_final]
  norm_num
  rfl


end Deutsch
namespace BernsteinVazirani


def Oracle (s : Bool) : nMatrix 1 := Z ^ s.toNat
def Oracle_s (s : ℕ -> Bool) : (n : ℕ) -> nMatrix 1 := fun n => Oracle (s n)
def BV_final (s : ℕ -> Bool) : (n : ℕ) -> nMatrix 1 := fun n => 2 * X ^ (s n).toNat


theorem BernsteinVaziraniAlgorithm (s : ℕ -> Bool) : Hₙ n * (tensor_power n (Oracle_s s)) * Hₙ n = tensor_power n (BV_final s) := by
  rw [Hₙ, tensor_power_mul_tensor_power, tensor_power_mul_tensor_power]
  induction n with
    | zero => simp [tensor_power, Oracle_s, BV_final]
    | succ n ih =>
      rw [tensor_power, Oracle_s, Oracle, tensor_power, BV_final]
      cases (s (n + 1));
      rw [ih, Bool.toNat_false, pow_zero, pow_zero, mul_one, mul_one, H_Identity, Nat.cast_two]
      rw [ih, Bool.toNat_true]
      simp only [pow_one] -- rw denies using pow_one
      rw [HZH_eq_X']
      simp only [nsmul_eq_mul, Nat.cast_ofNat, smul_eq_mul]

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
def O_final (s n : sType) : ℕ := 4 • (s == n).toNat

/-- Order of 0, 2, 1, 3 because of tensor:
    |0⟩|0⟩ = |00⟩ = (1, 0) ⊗ₖ (1, 0) = (1, 0, 0, 0)
    |0⟩|1⟩ = |01⟩ = (1, 0) ⊗ₖ (0, 1) = (0, 1, 0, 0)
    |1⟩|0⟩ = |10⟩ = (0, 1) ⊗ₖ (1, 0) = (0, 0, 1, 0)
    |1⟩|1⟩ = |11⟩ = (0, 1) ⊗ₖ (0, 1) = (0, 0, 0, 1) -/
@[simp]
def Oracle_final (s : sType) : Qubit 2 := !![O_final s 0, O_final s 1, O_final s 2, O_final s 3]


theorem OneOfFourGrover (s : sType) : Q₁ * H₂ * Oracleₛ s * X₂ * H₁ * CX * H₁ = Oracle_final s := by
  rw [Q₁, H₂, X₂, Oracleₛ, H₁, CX, Oracle_final]
  simp only [QCount, Nat.pow_zero, nMatrix, nMatrix', Oracle, Fin.isValue, cons_mul, vecMul_cons,
    head_cons, one_smul, tail_cons, empty_vecMul, add_zero, add_cons, zero_add, empty_add_empty,
    neg_smul, neg_cons, neg_zero, neg_empty, empty_mul, Equiv.symm_apply_apply, smul_cons,
    smul_eq_mul, mul_zero, mul_one, smul_empty, mul_neg, neg_neg, neg_add_rev, O_final,
    Fin.reduceBEq, Bool.toNat_false, CharP.cast_eq_zero, beq_self_eq_true, Bool.toNat_true,
    Nat.cast_ofNat]
  -- norm_num
  fin_cases s <;> simp <;> norm_num


end OneOfFourGrover
