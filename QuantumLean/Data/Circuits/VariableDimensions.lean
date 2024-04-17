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


def H : nMatrix 1 := !![1, 1; 1, -1]
def cnum : ℂ := ⟨1, 0⟩
#eval H


def pow_kronecker (n : ℕ) (M : nMatrix 1) : nMatrix n :=
  match n with
    | 0 => 1
    | (n + 1) => reindex (pow_kronecker n M ⊗ₖ M)


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
