import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Notation
import Mathlib.Data.Matrix.Kronecker

import «QuantumLean».Data.Circuits.Basic
import «QuantumLean».Data.Circuits.VariableDimensions

open Matrix
open Kronecker
open Circuits

def i_apply_1 (n : ℕ) (f : ℕ -> Bool) (M : nMatrix 1) : nMatrix n :=
  match n with
    | 0 => 1
    | (n + 1) =>
      match (f n) with
       | true  => Circuits.reindex ((i_apply_1 n f M) ⊗ₖ M)
       | false => Circuits.reindex ((i_apply_1 n f M) ⊗ₖ 1)


def false_function (_n : ℕ) : Bool := false

theorem i_apply_false_function_eq_I { n : ℕ } { M : nMatrix 1 } : i_apply_1 n false_function M = 1 := by
  induction n with
    | zero => simp [i_apply_1, false_function]
    | succ n ih =>
      rw [i_apply_1, false_function]
      simp
      rw [ih, one_kronecker_one, reindex_one]


-- def i_apply


-- def i_apply { m : ℕ+ } (n : ℕ) (f : ℕ -> bool) (M : nMatrix m) : nMatrix (n + m - 1) :=
  -- induction (n - m + 1) with
    -- | 0 => 1
    -- |
