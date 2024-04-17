import Lean.Meta.Tactic.LibrarySearch
import Aesop.Main

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Notation
import Mathlib.Data.Complex.Basic

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

theorem HZHeqX : Hadamard n * ZGate n * Hadamard n = (2 ^ n : ℕ) • XGate n := by
  induction n with
    | zero => simp [Hadamard, ZGate, XGate]
    | succ n ih =>
      rw [Hadamard, ZGate, XGate, ← reindex_mul, ← reindex_mul]
      rw [← mul_kronecker_mul, ← mul_kronecker_mul, ih, smul_kronecker, Z]
      simp only [cons_mul, vecMul_cons, head_cons, one_smul, tail_cons, empty_vecMul, add_zero, add_cons, zero_add, empty_add_empty, neg_smul, neg_cons, neg_zero, neg_neg, neg_empty, empty_mul, Equiv.symm_apply_apply, add_right_neg, one_add_one_eq_two]
      rw [show (!![0, 2; 2, 0] : nMatrix 1) = 2 • !![0, 1; 1, 0] by norm_num]
      rw [kronecker_smul]
      rw [smul_reindex, smul_reindex, ← XGate]
      rw [← smul_assoc]
      rfl


theorem HXHeqZ : Hadamard n * XGate n * Hadamard n = (2 ^ n : ℕ) • ZGate n := by
  induction n with
    | zero => simp [Hadamard, ZGate, XGate]
    | succ n ih =>
      rw [Hadamard, ZGate, XGate, ← reindex_mul, ← reindex_mul]
      rw [← mul_kronecker_mul, ← mul_kronecker_mul, ih, smul_kronecker, X]
      simp only [cons_mul, vecMul_cons, head_cons, one_smul, tail_cons, empty_vecMul, add_zero, add_cons, zero_add, empty_add_empty, neg_smul, neg_cons, neg_zero, neg_empty, empty_mul, Equiv.symm_apply_apply, add_right_neg, add_left_neg, add_neg]
      rw [show (!![1 + 1, 0; 0, -1 + -1] : nMatrix 1) = (2 : ℕ) • !![1, 0; 0, -1] by norm_num]
      rw [kronecker_smul]
      rw [smul_reindex, smul_reindex, ← ZGate]
      rw [← smul_assoc]
      rfl

-- Create the Oracle for the Deutsch Algorithm, i.e. O(a, b) = !![-1^a, 0; 0, 1^b] where a, b ∈ {0, 1}
@[simp]
def Oracle (a b : Bool) : Matrix (Fin (2 ^ 1)) (Fin (2 ^ 1)) ℂ :=
  !![(-1)^(a.toNat), 0; 0, (-1)^(b.toNat)]


def PlusQbit : Matrix (Fin 1) (Fin (2 ^ 1)) ℂ := !![1, 1]
def ZeroQbit : Matrix (Fin 1) (Fin (2 ^ 1)) ℂ := !![1, 0]
def OneQbit : Matrix (Fin 1) (Fin (2 ^ 1)) ℂ := !![0, 1]


def DeutschOutcome (a b : Bool) : Matrix (Fin 1) (Fin (2 ^ 1)) ℂ :=
  !![(a == b).toNat, (a != b).toNat]


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


-- Create a theorem with inputs a and b which are either 0 or 1 (Natural number type)


-- Perhaps create a theorem that shows given a Gate * Gate2 = Gate3, Gate^⊗n * Gate2^⊗n = Gate3^⊗n
