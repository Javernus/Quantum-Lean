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


theorem HZH_eq_X_1 : H * Z * H = 2 • X := by
  rw [H, Z, X]
  norm_num


theorem HZH_eq_X : Hadamard n * ZGate n * Hadamard n = (2 ^ n : ℕ) • XGate n := by
  rw [Hadamard, ZGate, ← pow_kronecker_mul, ← pow_kronecker_mul, HZH_eq_X_1, pow_kronecker_smul, ← XGate]


theorem HXHeqZ_1 : H * X * H = 2 • Z := by
  rw [H, X, Z]
  norm_num


theorem HXHeqZ : Hadamard n * XGate n * Hadamard n = (2 ^ n : ℕ) • ZGate n := by
  rw [Hadamard, XGate, ← pow_kronecker_mul, ← pow_kronecker_mul, HXHeqZ_1, pow_kronecker_smul, ← ZGate]

-- Create the Oracle for the Deutsch Algorithm, i.e. O(a, b) = !![-1^a, 0; 0, 1^b] where a, b ∈ {0, 1}
-- @[simp]
-- def Oracle (a b : Bool) : Matrix (Fin (2 ^ 1)) (Fin (2 ^ 1)) ℂ :=
--   !![(-1)^(a.toNat), 0; 0, (-1)^(b.toNat)]


-- def PlusQbit : Matrix (Fin 1) (Fin (2 ^ 1)) ℂ := !![1, 1]
-- def ZeroQbit : Matrix (Fin 1) (Fin (2 ^ 1)) ℂ := !![1, 0]
-- def OneQbit : Matrix (Fin 1) (Fin (2 ^ 1)) ℂ := !![0, 1]


-- def DeutschOutcome (a b : Bool) : Matrix (Fin 1) (Fin (2 ^ 1)) ℂ :=
--   !![(a == b).toNat, (a != b).toNat]


--
-- The Bernstein-Vazirani Algorithm
--

namespace BernsteinVazirani

def s : ℕ -> Bool
  | 0 => false
  | 1 => true
  | 2 => false
  | 3 => true
  | 4 => false
  | 5 => true
  | 6 => false
  | 7 => true
  | _ => false


def Oracle (s : Bool) : nMatrix 1 := Z ^ s.toNat


def Oracle_s (s : ℕ -> Bool) : (n : ℕ) -> nMatrix 1 :=
  fun n => Oracle (s n)


def BV_final (s : ℕ -> Bool) : (n : ℕ) -> nMatrix 1 :=
  fun n => 2 * X ^ (s n).toNat


theorem Bernstein_Vazirani (s : ℕ -> Bool) : Hadamard n * (stack_gates n (Oracle_s s)) * Hadamard n = stack_gates n (BV_final s) := by
  rw [Hadamard, pow_kronecker_mul_stack_gates, stack_gates_mul_pow_kronecker]
  induction n with
    | zero => simp [stack_gates, Oracle_s, BV_final]
    | succ n ih =>
      rw [stack_gates, Oracle_s, Oracle, stack_gates, BV_final]
      cases (s n);
      rw [ih, Bool.toNat_false, pow_zero, pow_zero, mul_one, mul_one, H_mul_H_1, Nat.cast_two]
      rw [ih, Bool.toNat_true]
      simp only [pow_one] -- rw denies using pow_one
      rw [HZH_eq_X_1]
      simp only [nsmul_eq_mul, Nat.cast_ofNat, smul_eq_mul]

end BernsteinVazirani

end CircuitLemmas


-- The Deutsch Algorithm
-- theorem DeutschAlgorithm (a b : Bool) : PlusQbit * (Oracle a b) * Hadamard 1 = DeutschOutcome a b :=
--   by
--     simp [PlusQbit, Oracle, Hadamard, DeutschOutcome]

-- theorem DeutschNew (a b : Bool) : Hadamard 1 * (Oracle a b) * Hadamard 1 = 2 * (-1)^(a.toNat) * XGate^(a.toNat + b.toNat) :=
--   by
--     cases a; cases b;
--     rw [IeqI, mul_one, HxH]
--     norm_num
--     -- Failing from here
--     simp [mul_apply, ofNat_fin_two]
--     norm_num
--     cases b;
--     simp [mul_apply, ofNat_fin_two]
--     norm_num
--     simp [mul_apply, ofNat_fin_two]
--     norm_num


-- stack_gates -> tensor_power
-- CNOT & SWAP
-- Hadamard -> H?
-- Act in ℂ^p (or ℂ^{0,...,p-1} ≃ ℂ^(Fₚ))
-- X gate adds one to qubit
-- Z × qubit a is root of unity to power of a (ωₚ = exp(2πi/p))





-- Matrix def with vector support
-- Prove BV on |0>
-- 1 out of 4 Grover's
  -- CX, CZ, CCX?
