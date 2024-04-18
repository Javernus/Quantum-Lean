import Lean.Meta.Tactic.LibrarySearch
import Aesop.Main

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


def pow_kronecker (n : ℕ) (M : nMatrix 1) : nMatrix n :=
  match n with
    | 0 => 1
    | (n + 1) => reindex (pow_kronecker n M ⊗ₖ M)



theorem pow_kronecker_zero { M : nMatrix 1 } : pow_kronecker 0 M = 1 := by
  simp [pow_kronecker]


theorem pow_kronecker_one { i : ℕ } : pow_kronecker 1 i = i := by
  rw [pow_kronecker, pow_kronecker_zero]
  rw [kronecker_natCast, one_kronecker_one, smul_reindex, reindex_one]
  norm_num



theorem pow_kronecker_mul { n : ℕ } (M N : nMatrix 1) : pow_kronecker n (M * N) = pow_kronecker n M * pow_kronecker n N := by
  induction n with
    | zero => simp [pow_kronecker]
    | succ n ih =>
      rw [pow_kronecker]
      rw [pow_kronecker]
      rw [pow_kronecker]
      rw [← reindex_mul]
      rw [← mul_kronecker_mul]
      rw [ih]


theorem pow_kronecker_of_one { n : ℕ } : pow_kronecker n 1 = 1 := by
  induction n with
    | zero => simp [pow_kronecker]
    | succ n ih =>
      rw [pow_kronecker]
      rw [ih]
      rw [one_kronecker_one, reindex_one]


theorem pow_kronecker_of_natCast { i n : ℕ } : pow_kronecker n i = ↑(i ^ n) := by
  induction n with
    | zero => rw [pow_kronecker_zero]; rw [Nat.pow_zero i, Nat.cast_one]
    | succ n ih => rw [pow_kronecker, ih, kronecker_natCast_natCast, reindex_natCast, ← Nat.pow_succ]


def stack_gates (n : ℕ) (gates : ℕ -> nMatrix 1) : nMatrix n :=
  match n with
    | 0 => 1
    | (n + 1) => reindex (stack_gates n gates ⊗ₖ gates n)


theorem pow_kronecker_mul' { n : ℕ } (M N : ℕ -> nMatrix 1) : stack_gates n M * stack_gates n N = stack_gates (n) (λ i => M i * N i) := by
  induction n with
    | zero => simp [stack_gates]
    | succ m ih =>
      rw [stack_gates]
      rw [stack_gates]
      rw [stack_gates]
      rw [← reindex_mul]
      rw [← mul_kronecker_mul]
      rw [ih]
