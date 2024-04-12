import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Notation
import Mathlib.Data.Matrix.Kronecker
import Mathlib.Data.Complex.Basic

open Matrix
open Kronecker

namespace Circuits

section Reindex
variable { m n : ℕ }


/-- Reindex a circuit matrix to Fin 2 ^ n × Fin 2 ^ n dimensions -/
def reindex (A : Matrix (Fin (2 ^ n) × Fin 2) (Fin (2 ^ n) × Fin 2) ℂ) : Matrix (Fin (2 ^ (n + 1))) (Fin (2 ^ (n + 1))) ℂ :=
  Matrix.reindex finProdFinEquiv finProdFinEquiv A


theorem identity : (1 : Matrix (Fin (2 ^ 0)) (Fin (2 ^ 0)) ℂ) = (1 : ℕ) := by
  simp

-- /-- Reindex a circuit matrix to Fin 2 ^ n × Fin 2 ^ n dimensions -/
-- Try to make this work for any m and n
-- def reindex' (A : Matrix (Fin (2 ^ m) × Fin (2 ^ n)) (Fin (2 ^ m) × Fin (2 ^ n)) ℂ) : Matrix (Fin (2 ^ (m + n))) (Fin (2 ^ (m + n))) ℂ :=
--   Matrix.reindex finProdFinEquiv finProdFinEquiv A


/-- Prove linearity in multiplication -/
theorem reindex_mul (A B : Matrix (Fin (2 ^ n) × Fin 2) (Fin (2 ^ n) × Fin 2) ℂ) : reindex (A * B) = reindex A * reindex B :=
  Matrix.submatrix_mul _ _ _ _ _ (finProdFinEquiv.symm.bijective)


theorem smul_reindex (c : ℕ) (A : Matrix (Fin (2 ^ n) × Fin 2) (Fin (2 ^ n) × Fin 2) ℂ) : reindex (c • A) = c • reindex A := by
  simp only [reindex, reindex_apply]
  rw [submatrix_smul]
  rfl


/-- Prove natural number casts to be equivalent under reindexation -/
theorem reindex_natCast (m : ℕ) :
    reindex (m : Matrix (Fin (2 ^ n) × Fin 2) (Fin (2 ^ n) × Fin 2) ℂ) = m := by
  ext i j
  rw [reindex, reindex_apply, submatrix_apply]
  simp_rw [← diagonal_natCast, diagonal_apply]
  simp_rw [finProdFinEquiv.symm.injective.eq_iff]

end Reindex
