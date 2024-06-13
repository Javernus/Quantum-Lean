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

@[simp]
abbrev nMatrix' (n n' : ℕ) := Matrix (QCount n) (QCount n') ℂ
@[simp]
abbrev mnMatrix' (m m' n n' : ℕ) := Matrix (QCount m × QCount n) (QCount m' × QCount n') ℂ

@[simp]
abbrev nMatrix (n : ℕ) := nMatrix' n n
@[simp]
abbrev mnMatrix (m n : ℕ) := mnMatrix' m m n n


@[simp]
theorem one_fin_two : (1 : nMatrix 1) = !![1, 0; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl


@[simp]
def QCount_mul_QCount : (QCount m × QCount n) ≃ QCount (m + n) := by
  simp [QCount]
  rw [Nat.pow_add]
  exact @finProdFinEquiv (2 ^ m) (2 ^ n)


@[simp]
def QCount_mul_one : (QCount (m * 1)) ≃ QCount m := by
  simp [QCount]
  rfl


@[simp]
def QCount_mul_succ_n : (QCount (m * n) × QCount m) ≃ QCount (m * (n + 1)) := by
  simp [QCount]
  rw [@mul_add_one, Nat.pow_add]
  exact @finProdFinEquiv (2 ^ (m * n)) (2 ^ m)


@[simp]
def QCount_assoc : (QCount (m * n * o)) ≃ QCount (m * (n * o)) := by
  simp only [QCount]
  rw [@Mathlib.Tactic.RingNF.mul_assoc_rev]


/-- Reindex a circuit matrix to Fin 2 ^ n × Fin 2 ^ n dimensions -/
@[simp]
def reindex₁ (A : mnMatrix' m m' n n') : nMatrix' (m + n) (m' + n') :=
  Matrix.reindex QCount_mul_QCount QCount_mul_QCount A


@[simp]
def reindex₂ (A : nMatrix' (m * 1) (m' * 1)) : nMatrix' m m' :=
  Matrix.reindex QCount_mul_one QCount_mul_one A


@[simp]
def reindex₃ (A : mnMatrix' (m * n) (m' * n) m m') : nMatrix' (m * (n + 1)) (m' * (n + 1)) :=
  Matrix.reindex QCount_mul_succ_n QCount_mul_succ_n A


@[simp]
def reindex₄ (A : nMatrix' (m * n * o) (m' * n * o)) : nMatrix' (m * (n * o)) (m' * (n * o)) :=
  Matrix.reindex QCount_assoc QCount_assoc A


@[simp]
theorem reindex₁_one : reindex₁ (1 : mnMatrix m n) = 1 := by
  ext i j
  rw [reindex₁, reindex_apply, submatrix_apply]
  simp_rw [← diagonal_one, diagonal_apply]
  simp_rw [QCount_mul_QCount.symm.injective.eq_iff]


@[simp]
theorem reindex₂_one : reindex₂ (1 : nMatrix (m * 1)) = 1 := by
  ext i j
  rw [reindex₂, reindex_apply, submatrix_apply]
  simp_rw [← diagonal_one, diagonal_apply]
  simp only [QCount, EmbeddingLike.apply_eq_iff_eq]


@[simp]
theorem reindex₃_one : reindex₃ (1 : mnMatrix (m * n) m) = 1 := by
  ext i j
  rw [reindex₃, reindex_apply, submatrix_apply]
  simp_rw [← diagonal_one, diagonal_apply]
  simp only [QCount, EmbeddingLike.apply_eq_iff_eq]


@[simp]
theorem reindex₄_one : reindex₄ (1 : nMatrix (m * n * o)) = 1 := by
  ext i j
  rw [reindex₄, reindex_apply, submatrix_apply]
  simp_rw [← diagonal_one, diagonal_apply]
  simp only [QCount, EmbeddingLike.apply_eq_iff_eq]


/-- Prove linearity in multiplication -/
@[simp]
theorem reindex₁_mul (A : mnMatrix' m m' n n') (B : mnMatrix' m' o n' o')
  : reindex₁ (A * B) = reindex₁ A * reindex₁ B :=
  Matrix.submatrix_mul _ _ _ _ _ (QCount_mul_QCount.symm.bijective)


@[simp]
theorem reindex₂_mul (A : nMatrix' (m * 1) (m' * 1)) (B : nMatrix' (m' * 1) (o * 1))
  : reindex₂ (A * B) = reindex₂ A * reindex₂ B :=
  Matrix.submatrix_mul _ _ _ _ _ (QCount_mul_one.symm.bijective)


@[simp]
theorem reindex₃_mul (A : mnMatrix' (m * n) (m' * n) m m') (B : mnMatrix' (m' * n) (o * n) m' o) : reindex₃ (A * B) = reindex₃ A * reindex₃ B :=
  Matrix.submatrix_mul _ _ _ _ _ (QCount_mul_succ_n.symm.bijective)


@[simp]
theorem reindex₄_mul (A : mnMatrix' (m * n) (m' * n) m m') (B : mnMatrix' (m' * n) (o * n) m' o) : reindex₃ (A * B) = reindex₃ A * reindex₃ B :=
  Matrix.submatrix_mul _ _ _ _ _ (QCount_mul_succ_n.symm.bijective)


@[simp]
theorem smul_reindex₁ (c : ℕ) (A : mnMatrix m n) : reindex₁ (c • A) = c • reindex₁ A := by
  simp only [reindex₁, reindex_apply]
  rw [submatrix_smul]
  rfl


@[simp]
theorem smul_reindex₂ (c : ℕ) (A : nMatrix (m * 1)) : reindex₂ (c • A) = c • reindex₂ A := by
  simp only [reindex₂, reindex_apply]
  rw [submatrix_smul]
  rfl


@[simp]
theorem smul_reindex₃ (c : ℕ) (A : mnMatrix (m * n) m) : reindex₃ (c • A) = c • reindex₃ A := by
  simp only [reindex₃, reindex_apply]
  rw [submatrix_smul]
  rfl


@[simp]
theorem reindex₁_natCast { i : ℕ } : reindex₁ (i : mnMatrix m n) = i := by
  nth_rewrite 1 [← mul_one i]
  rw [@Nat.cast_mul, ← @nsmul_eq_mul, smul_reindex₁, @Nat.cast_one, reindex₁_one, nsmul_eq_mul, mul_one]


@[simp]
theorem reindex₂_natCast { i : ℕ } : reindex₂ (i : nMatrix (m * 1)) = i := by
  nth_rewrite 1 [← mul_one i]
  rw [@Nat.cast_mul, ← @nsmul_eq_mul, smul_reindex₂, @Nat.cast_one, reindex₂_one, nsmul_eq_mul, mul_one]


@[simp]
theorem reindex₃_natCast { i : ℕ } : reindex₃ (i : mnMatrix (m * n) m) = i := by
  nth_rewrite 1 [← mul_one i]
  rw [@Nat.cast_mul, ← @nsmul_eq_mul, smul_reindex₃, @Nat.cast_one, reindex₃_one, nsmul_eq_mul, mul_one]


-- theorem reindex₁_eq (A : mnMatrix m n) : reindex₁ A = A := by
--   simp only [reindex₁, reindex_apply]
--   rw [submatrix_smul]
--   rfl


-- theorem reindex₂_eq (A : nMatrix (m * 1)) : reindex₂ A = A := by
--   simp only [reindex₂, reindex_apply]
--   rw [submatrix_smul]
--   rfl


-- theorem reindex₃_eq (A : mnMatrix (m * n) m) : reindex₃ A = A := by
--   simp only [reindex₃, reindex_apply]
--   rw [submatrix_smul]
--   rfl


end Reindex
