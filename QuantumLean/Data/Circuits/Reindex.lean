import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Notation
import Mathlib.Data.Matrix.Kronecker
import Mathlib.Data.Complex.Basic

import «QuantumLean».Data.Circuits.Types

open Matrix

/-
This file contains a set of reindexes for `mathlib`'s `Matrix`. These allow the
dimensions of a matrix to be reindexed, or rewritten in a different but equivalent
way. These are the equivalences:

1. QCount_mul_QCount: (QCount m × QCount n) ≃ QCount (m + n)
2. QCount_mul_one:    (QCount (m * 1)) ≃ QCount m
3. QCount_mul_succ_n: (QCount (m * n) × QCount m) ≃ QCount (m * (n + 1))
4. QCount_assoc:      (QCount (m * n * o)) ≃ QCount (m * (n * o))
5. QCount_mul_add:    (QCount (m * n) × QCount (m * o)) ≃ QCount (m * (n + o))

Each of these are used in their respective `reindexₙ` definition to rewrite the
dimensions of a matrix.

For each of these reindexes, there are theorems defined to prove certain equalities
of type conversions. The non-nGate matrices or A, B, etc. have the right type for
the given reindex to apply.

- reindexₙ_one: reindexₙ (1 : non-nGate matrix) = 1
- reindexₙ_mul: reindexₙ (A * B) = reindexₙ A * reindexₙ B
- smul_reindexₙ: (c : ℕ) : reindexₙ (c • A) = c • reindexₙ A
- reindexₙ_natCast: { i : ℕ } : reindex₁ (i : nat cast to diagonal non-nGate matrix) = i

These theorems can be used to rewrite certain reindexes to get the reindex out of
the way.
-/

namespace Circuits
section Reindex

variable { m m' n n' o o' : ℕ }


@[simp]
theorem one_fin_two : (1 : nGate 1) = !![1, 0; 0, 1] := by
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


@[simp]
def QCount_mul_add : (QCount (m * n) × QCount (m * o)) ≃ QCount (m * (n + o)) := by
  simp [QCount]
  rw [Nat.mul_add, Nat.pow_add]
  exact @finProdFinEquiv (2 ^ (m * n)) (2 ^ (m * o))


/-- Reindex a circuit matrix to Fin 2 ^ n × Fin 2 ^ n dimensions -/
@[simp]
def reindex₁ (A : mnGate'' m m' n n') : nGate' (m + n) (m' + n') :=
  Matrix.reindex QCount_mul_QCount QCount_mul_QCount A


@[simp]
def reindex₂ (A : nGate' (m * 1) (m' * 1)) : nGate' m m' :=
  Matrix.reindex QCount_mul_one QCount_mul_one A


@[simp]
def reindex₃ (A : mnGate'' (m * n) (m' * n) m m') : nGate' (m * (n + 1)) (m' * (n + 1)) :=
  Matrix.reindex QCount_mul_succ_n QCount_mul_succ_n A


@[simp]
def reindex₄ (A : nGate' (m * n * o) (m' * n * o)) : nGate' (m * (n * o)) (m' * (n * o)) :=
  Matrix.reindex QCount_assoc QCount_assoc A


@[simp]
def reindex₅ (A : mnGate'' (m * n) (m' * n) (m * o) (m' * o)) : nGate' (m * (n + o)) (m' * (n + o)) :=
  Matrix.reindex QCount_mul_add QCount_mul_add A


@[simp]
theorem reindex₁_one : reindex₁ (1 : mnGate' m n) = 1 := by
  ext i j
  rw [reindex₁, reindex_apply, submatrix_apply]
  simp_rw [← diagonal_one, diagonal_apply]
  simp_rw [QCount_mul_QCount.symm.injective.eq_iff]


@[simp]
theorem reindex₂_one : reindex₂ (1 : nGate (m * 1)) = 1 := by
  ext i j
  rw [reindex₂, reindex_apply, submatrix_apply]
  simp_rw [← diagonal_one, diagonal_apply]
  simp only [QCount, EmbeddingLike.apply_eq_iff_eq]


@[simp]
theorem reindex₃_one : reindex₃ (1 : mnGate' (m * n) m) = 1 := by
  ext i j
  rw [reindex₃, reindex_apply, submatrix_apply]
  simp_rw [← diagonal_one, diagonal_apply]
  simp only [QCount, EmbeddingLike.apply_eq_iff_eq]


@[simp]
theorem reindex₄_one : reindex₄ (1 : nGate (m * n * o)) = 1 := by
  ext i j
  rw [reindex₄, reindex_apply, submatrix_apply]
  simp_rw [← diagonal_one, diagonal_apply]
  simp only [QCount, EmbeddingLike.apply_eq_iff_eq]


@[simp]
theorem reindex₅_one : reindex₅ (1 : mnGate' (m * n) (m * o)) = 1 := by
  ext i j
  rw [reindex₅, reindex_apply, submatrix_apply]
  simp_rw [← diagonal_one, diagonal_apply]
  simp only [QCount, EmbeddingLike.apply_eq_iff_eq]


/-- Prove linearity in multiplication -/
@[simp]
theorem reindex₁_mul (A : mnGate'' m m' n n') (B : mnGate'' m' o n' o')
  : reindex₁ (A * B) = reindex₁ A * reindex₁ B :=
  Matrix.submatrix_mul _ _ _ _ _ (QCount_mul_QCount.symm.bijective)


@[simp]
theorem reindex₂_mul (A : nGate' (m * 1) (m' * 1)) (B : nGate' (m' * 1) (o * 1))
  : reindex₂ (A * B) = reindex₂ A * reindex₂ B :=
  Matrix.submatrix_mul _ _ _ _ _ (QCount_mul_one.symm.bijective)


@[simp]
theorem reindex₃_mul (A : mnGate'' (m * n) (m' * n) m m') (B : mnGate'' (m' * n) (o * n) m' o) : reindex₃ (A * B) = reindex₃ A * reindex₃ B :=
  Matrix.submatrix_mul _ _ _ _ _ (QCount_mul_succ_n.symm.bijective)


@[simp]
theorem reindex₄_mul (A : mnGate'' (m * n) (m' * n) m m') (B : mnGate'' (m' * n) (o * n) m' o) : reindex₃ (A * B) = reindex₃ A * reindex₃ B :=
  Matrix.submatrix_mul _ _ _ _ _ (QCount_mul_succ_n.symm.bijective)


@[simp]
theorem reindex₅_mul (A : mnGate'' (m * n) (m' * n) (m * o) (m' * o)) (B : mnGate'' (m' * n) (o' * n) (m' * o) (o' * o)) : reindex₅ (A * B) = reindex₅ A * reindex₅ B :=
  Matrix.submatrix_mul _ _ _ _ _ (QCount_mul_add.symm.bijective)


@[simp]
theorem smul_reindex₁ (c : ℕ) (A : mnGate' m n) : reindex₁ (c • A) = c • reindex₁ A := by
  simp only [reindex₁, reindex_apply]
  rw [submatrix_smul]
  rfl


@[simp]
theorem smul_reindex₂ (c : ℕ) (A : nGate (m * 1)) : reindex₂ (c • A) = c • reindex₂ A := by
  simp only [reindex₂, reindex_apply]
  rw [submatrix_smul]
  rfl


@[simp]
theorem smul_reindex₃ (c : ℕ) (A : mnGate' (m * n) m) : reindex₃ (c • A) = c • reindex₃ A := by
  simp only [reindex₃, reindex_apply]
  rw [submatrix_smul]
  rfl


@[simp]
theorem reindex₁_natCast { i : ℕ } : reindex₁ (i : mnGate' m n) = i := by
  nth_rewrite 1 [← mul_one i]
  rw [@Nat.cast_mul, ← @nsmul_eq_mul, smul_reindex₁, @Nat.cast_one, reindex₁_one, nsmul_eq_mul, mul_one]


@[simp]
theorem reindex₂_natCast { i : ℕ } : reindex₂ (i : nGate (m * 1)) = i := by
  nth_rewrite 1 [← mul_one i]
  rw [@Nat.cast_mul, ← @nsmul_eq_mul, smul_reindex₂, @Nat.cast_one, reindex₂_one, nsmul_eq_mul, mul_one]


@[simp]
theorem reindex₃_natCast { i : ℕ } : reindex₃ (i : mnGate' (m * n) m) = i := by
  nth_rewrite 1 [← mul_one i]
  rw [@Nat.cast_mul, ← @nsmul_eq_mul, smul_reindex₃, @Nat.cast_one, reindex₃_one, nsmul_eq_mul, mul_one]


end Reindex
end Circuits
