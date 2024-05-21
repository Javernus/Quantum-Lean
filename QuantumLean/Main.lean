-- import Lean.Meta.Tactic.LibrarySearch
-- import Aesop.Main

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Notation
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Complex.Exponential

-- Import the gates
import «QuantumLean».Data.Circuits.Basic
import «QuantumLean».Data.Matrix.Kronecker
import «QuantumLean».Hadamard
import «QuantumLean».PauliGates

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
      cases (s n);
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
-- X-I-X-H
