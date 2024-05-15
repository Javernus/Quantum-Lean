-- import Lean.Meta.Tactic.LibrarySearch
-- import Aesop.Main

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Notation
import Mathlib.Data.Complex.Basic

-- Import the gates
import «QuantumLean».Data.Circuits.Basic
import «QuantumLean».Data.Matrix.Kronecker
import «QuantumLean».Data.Complex.Representation

open Matrix
open Complex
open Kronecker
open Circuits


variable {m n : Type*} {R : Type*} [Semiring R]


def reindexₖ (A : Matrix m n R) : Matrix (Fin 1 → m) (Fin 1 → n) R :=
  reindex (Equiv.funUnique (Fin 1) m).symm (Equiv.funUnique (Fin 1) n).symm A


def powKronecker (k : ℕ) (A : Matrix m n R) :
    Matrix (Fin k → m) (Fin k → n) R :=
  fun fm fn => ((List.finRange k).map fun i => A (fm i) (fn i)).prod


-- theorem powKronecker_one { A : Matrix m n R } : (powKronecker 1 A) = reindexₖ A := by
--   apply?
--   rw [kronecker_natOne i, one_kronecker_one, smul_reindex, reindex_one]
--   norm_num

def pow_kronecker {m : ℕ} (n : ℕ) (M : nMatrix m) : nMatrix (m * n) :=
  match n with
    | 0 => (1 : nMatrix 0)
    | (n + 1) => reindex₃ (pow_kronecker n M ⊗ₖ M)


theorem pow_kronecker_zero {n : ℕ} { M : nMatrix n } : pow_kronecker 0 M = 1 := by
  simp [pow_kronecker]


theorem pow_kronecker_one { i n : ℕ } : pow_kronecker 1 (i : nMatrix n) = i := by
  rw [pow_kronecker, pow_kronecker_zero]
  rw [kronecker_natCast, one_kronecker_one, smul_reindex₃, reindex₃_one]
  norm_num


theorem pow_kronecker_mul { m n : ℕ } (M N : nMatrix m) : pow_kronecker n (M * N) = pow_kronecker n M * pow_kronecker n N := by
  induction n with
    | zero => simp [pow_kronecker]
    | succ n ih =>
      rw [pow_kronecker]
      rw [pow_kronecker]
      rw [pow_kronecker]
      rw [← reindex₃_mul]
      rw [← mul_kronecker_mul]
      rw [ih]


theorem pow_kronecker_of_one { m n : ℕ } : pow_kronecker n (1 : nMatrix m) = 1 := by
  induction n with
    | zero => simp [pow_kronecker]
    | succ n ih =>
      rw [pow_kronecker]
      rw [ih]
      rw [one_kronecker_one, reindex₃_one]


theorem pow_kronecker_of_natCast { i m n : ℕ } : pow_kronecker n (i : nMatrix m) = ↑(i ^ n) := by
  induction n with
    | zero => rw [pow_kronecker_zero]; rw [Nat.pow_zero i, Nat.cast_one]
    | succ n ih => rw [pow_kronecker, ih, kronecker_natCast_natCast, reindex₃_natCast, ← Nat.pow_succ]


theorem pow_kronecker_smul { m n : ℕ } (M : nMatrix m) (c : ℕ) : pow_kronecker n (c • M) = c ^ n • pow_kronecker n M := by
  induction n with
    | zero => simp [pow_kronecker]
    | succ n ih =>
      rw [pow_kronecker, pow_kronecker, ih, smul_kronecker, kronecker_smul, ← smul_assoc, smul_reindex₃]
      rw [Nat.pow_succ, smul_eq_mul]


def stack_gates {m : ℕ} (n : ℕ) (gates : ℕ -> nMatrix m) : nMatrix (m * n) :=
  match n with
    | 0 => 1
    | (n + 1) => reindex₃ (stack_gates n gates ⊗ₖ gates n)


theorem stack_gates_mul_stack_gates { m n : ℕ } (M N : ℕ -> nMatrix m) : stack_gates n M * stack_gates n N = stack_gates (n) (λ i => M i * N i) := by
  induction n with
    | zero => simp [stack_gates]
    | succ m ih =>
      rw [stack_gates]
      rw [stack_gates]
      rw [stack_gates]
      rw [← reindex₃_mul]
      rw [← mul_kronecker_mul]
      rw [ih]


theorem pow_kronecker_mul_stack_gates { m n : ℕ } (N : nMatrix m) (gates : ℕ -> nMatrix m) : pow_kronecker n N * stack_gates n gates = stack_gates n (λ i => N * gates i) := by
  induction n with
    | zero => simp only [Nat.zero_eq, Nat.pow_zero, pow_kronecker, stack_gates, mul_one]
    | succ m ih =>
      rw [pow_kronecker, stack_gates]
      rw [← reindex₃_mul]
      rw [← mul_kronecker_mul]
      rw [ih, ← stack_gates]


theorem stack_gates_mul_pow_kronecker { m n : ℕ } (N : nMatrix m) (gates : ℕ -> nMatrix m) : stack_gates n gates * pow_kronecker n N = stack_gates n (λ i => gates i * N) := by
  induction n with
    | zero => simp only [Nat.zero_eq, Nat.pow_zero, pow_kronecker, stack_gates, one_mul]
    | succ m ih =>
      rw [pow_kronecker, stack_gates]
      rw [← reindex₃_mul]
      rw [← mul_kronecker_mul]
      rw [ih, ← stack_gates]
