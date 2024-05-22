import Lean.Meta.Tactic.LibrarySearch
import Aesop.Main
-- import LeanCopilot

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Notation
import Mathlib.Data.Matrix.Kronecker
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.ProdAssoc


open Matrix
open Kronecker

namespace Circuits

section Reindex
variable { m m' n n' o o' : ℕ }


-- Num of qubits
@[simp]
abbrev QCount (n : ℕ) := Fin (2 ^ n)

abbrev nMatrix' (n n' : ℕ) := Matrix (QCount n) (QCount n') ℂ
abbrev mnMatrix' (m m' n n' : ℕ) := Matrix (QCount m × QCount n) (QCount m' × QCount n') ℂ

abbrev nMatrix (n : ℕ) := nMatrix' n n
abbrev mnMatrix (m n : ℕ) := mnMatrix' m m n n

def A : nMatrix 2 := !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, -1]



theorem one_fin_two : (1 : nMatrix 1) = !![1, 0; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl


def QCount_mul_QCount : (QCount m × QCount n) ≃ QCount (m + n) := by
  simp [QCount]
  rw [Nat.pow_add]
  exact @finProdFinEquiv (2 ^ m) (2 ^ n)


def QCount_mul_one : (QCount (m * 1)) ≃ QCount m := by
  simp [QCount]
  rfl


def QCount_mul_succ_n : (QCount (m * n) × QCount m) ≃ QCount (m * (n + 1)) := by
  simp [QCount]
  rw [@mul_add_one, Nat.pow_add]
  exact @finProdFinEquiv (2 ^ (m * n)) (2 ^ m)


/-- Reindex a circuit matrix to Fin 2 ^ n × Fin 2 ^ n dimensions -/
def reindex₁ (A : mnMatrix' m m' n n') : nMatrix' (m + n) (m' + n') :=
  Matrix.reindex QCount_mul_QCount QCount_mul_QCount A


def reindex₂ (A : nMatrix' (m * 1) (m' * 1)) : nMatrix' m m' :=
  Matrix.reindex QCount_mul_one QCount_mul_one A


def reindex₃ (A : mnMatrix' (m * n) (m' * n) m m') : nMatrix' (m * (n + 1)) (m' * (n + 1)) :=
  Matrix.reindex QCount_mul_succ_n QCount_mul_succ_n A


theorem reindex₁_one : reindex₁ (1 : mnMatrix m n) = 1 := by
  ext i j
  rw [reindex₁, reindex_apply, submatrix_apply]
  simp_rw [← diagonal_one, diagonal_apply]
  simp_rw [QCount_mul_QCount.symm.injective.eq_iff]


theorem reindex₂_one : reindex₂ (1 : nMatrix (m * 1)) = 1 := by
  ext i j
  rw [reindex₂, reindex_apply, submatrix_apply]
  simp_rw [← diagonal_one, diagonal_apply]
  simp only [QCount, EmbeddingLike.apply_eq_iff_eq]


theorem reindex₃_one : reindex₃ (1 : mnMatrix (m * n) m) = 1 := by
  ext i j
  rw [reindex₃, reindex_apply, submatrix_apply]
  simp_rw [← diagonal_one, diagonal_apply]
  simp only [QCount, EmbeddingLike.apply_eq_iff_eq]


/-- Prove linearity in multiplication -/
theorem reindex₁_mul (A : mnMatrix' m m' n n') (B : mnMatrix' m' o n' o')
  : reindex₁ (A * B) = reindex₁ A * reindex₁ B :=
  Matrix.submatrix_mul _ _ _ _ _ (QCount_mul_QCount.symm.bijective)


theorem reindex₂_mul (A : nMatrix' (m * 1) (m' * 1)) (B : nMatrix' (m' * 1) (o * 1))
  : reindex₂ (A * B) = reindex₂ A * reindex₂ B :=
  Matrix.submatrix_mul _ _ _ _ _ (QCount_mul_one.symm.bijective)


theorem reindex₃_mul (A : mnMatrix' (m * n) (m' * n) m m') (B : mnMatrix' (m' * n) (o * n) m' o) : reindex₃ (A * B) = reindex₃ A * reindex₃ B :=
  Matrix.submatrix_mul _ _ _ _ _ (QCount_mul_succ_n.symm.bijective)


theorem smul_reindex₁ (c : ℕ) (A : mnMatrix m n) : reindex₁ (c • A) = c • reindex₁ A := by
  simp only [reindex₁, reindex_apply]
  rw [submatrix_smul]
  rfl


theorem smul_reindex₂ (c : ℕ) (A : nMatrix (m * 1)) : reindex₂ (c • A) = c • reindex₂ A := by
  simp only [reindex₂, reindex_apply]
  rw [submatrix_smul]
  rfl


theorem smul_reindex₃ (c : ℕ) (A : mnMatrix (m * n) m) : reindex₃ (c • A) = c • reindex₃ A := by
  simp only [reindex₃, reindex_apply]
  rw [submatrix_smul]
  rfl


theorem reindex₁_natCast { i : ℕ } : reindex₁ (i : mnMatrix m n) = i := by
  nth_rewrite 1 [← mul_one i]
  rw [@Nat.cast_mul, ← @nsmul_eq_mul, smul_reindex₁, @Nat.cast_one, reindex₁_one]
  norm_num


theorem reindex₂_natCast { i : ℕ } : reindex₂ (i : nMatrix (m * 1)) = i := by
  nth_rewrite 1 [← mul_one i]
  rw [@Nat.cast_mul, ← @nsmul_eq_mul, smul_reindex₂, @Nat.cast_one, reindex₂_one]
  norm_num


theorem reindex₃_natCast { i : ℕ } : reindex₃ (i : mnMatrix (m * n) m) = i := by
  nth_rewrite 1 [← mul_one i]
  rw [@Nat.cast_mul, ← @nsmul_eq_mul, smul_reindex₃, @Nat.cast_one, reindex₃_one]
  norm_num

end Reindex
