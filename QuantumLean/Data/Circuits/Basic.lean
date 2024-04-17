import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Notation
import Mathlib.Data.Matrix.Kronecker
import Mathlib.Data.Complex.Basic

open Matrix
open Kronecker

namespace Circuits

section Reindex
variable { m n : ℕ }


-- Num of qubits
abbrev QCount (n : ℕ) := Fin (2 ^ n)
abbrev nMatrix (n : ℕ) := Matrix (QCount n) (QCount n) ℂ
abbrev mnMatrix (m n : ℕ) := Matrix (QCount m × QCount n) (QCount m × QCount n) ℂ
abbrev oneMatrix := Matrix (QCount 0) (QCount 0) ℂ


theorem one_fin_two : (1 : nMatrix 1) = !![1, 0; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl


def QCount_mul_QCount { m n : ℕ } : (QCount m × QCount n) ≃ QCount (m + n) := by
  simp [QCount]
  rw [Nat.pow_add]
  exact @finProdFinEquiv (2 ^ m) (2 ^ n)


/-- Reindex a circuit matrix to Fin 2 ^ n × Fin 2 ^ n dimensions -/
def reindex (A : mnMatrix m n) : nMatrix (m + n) :=
  Matrix.reindex QCount_mul_QCount QCount_mul_QCount A


/-- Prove linearity in multiplication -/
theorem reindex_mul (A B : mnMatrix m n) : reindex (A * B) = reindex A * reindex B :=
  Matrix.submatrix_mul _ _ _ _ _ (QCount_mul_QCount.symm.bijective)


theorem smul_reindex (c : ℕ) (A : mnMatrix m n) : reindex (c • A) = c • reindex A := by
  simp only [reindex, reindex_apply]
  rw [submatrix_smul]
  rfl


/-- Prove natural number casts to be equivalent under reindexation -/
theorem reindex_natCast (m : ℕ) :
    reindex (m : mnMatrix n 1) = m := by
  ext i j
  rw [reindex, reindex_apply, submatrix_apply]
  simp_rw [← diagonal_natCast, diagonal_apply]
  simp_rw [QCount_mul_QCount.symm.injective.eq_iff]

end Reindex
