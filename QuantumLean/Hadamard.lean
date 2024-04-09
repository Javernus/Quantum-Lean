import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Notation
import Mathlib.Data.Matrix.Kronecker
import Mathlib.Data.Complex.Basic

open Matrix
open Kronecker


section Hadamard
variable { n : ℕ }

def reindexHadamard (A : Matrix (Fin (2 ^ n) × Fin 2) (Fin (2 ^ n) × Fin 2) ℂ) : Matrix (Fin (2 ^ (n + 1))) (Fin (2 ^ (n + 1))) ℂ :=
  reindex finProdFinEquiv finProdFinEquiv A


theorem reindexHadamard_mul (A B : Matrix (Fin (2 ^ n) × Fin 2) (Fin (2 ^ n) × Fin 2) ℂ) : reindexHadamard (A * B) = reindexHadamard A * reindexHadamard B :=
  Matrix.submatrix_mul _ _ _ _ _ (finProdFinEquiv.symm.bijective)


theorem reindexHadamard_natCast (m : ℕ) :
    reindexHadamard (m : Matrix (Fin (2 ^ n) × Fin 2) (Fin (2 ^ n) × Fin 2) ℂ) = m := by
  ext i j
  rw [reindexHadamard, reindex_apply, submatrix_apply]
  simp_rw [← diagonal_natCast, diagonal_apply]
  simp_rw [finProdFinEquiv.symm.injective.eq_iff]


theorem kronecker_natCast_natCast {A B : Type} [DecidableEq A] [DecidableEq B] (m₁ m₂ : ℕ) :
    (m₁ : Matrix A A ℂ) ⊗ₖ (m₂ : Matrix B B ℂ) = ((m₁ * m₂ : ℕ) : Matrix (A × B) (A × B) ℂ) := by
  simp_rw [← nsmul_one]
  simp only [nsmul_eq_smul_cast ℕ, Nat.cast_id, Nat.cast_mul]
  rw [smul_kronecker, kronecker_smul, one_kronecker_one, smul_smul]
  rfl


theorem hadamardIdentity : (!![1, 1; 1, -1]) * (!![1, 1; 1, -1]) = ((2 : ℕ) : Matrix (Fin 2) (Fin 2) ℂ) := by
  simp [Matrix.mul_apply, ofNat_fin_two]
  norm_num


def Hadamard : (n : ℕ) -> Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ
  | 0 => 1
  | (n + 1) => reindexHadamard (Hadamard n ⊗ₖ !![1, 1; 1, -1])


#eval Hadamard 2

-- In general, I am trying to prove H * H = I (× a constant) for Hadamard matrices
theorem HnxHn : Hadamard n * Hadamard n = (2 ^ n : ℕ) := by
  induction n with
    | zero => simp [Hadamard]
    | succ n ih =>
      rw [Hadamard, ← reindexHadamard_mul, ← mul_kronecker_mul, ih]
      rw [hadamardIdentity]
      rw [kronecker_natCast_natCast, reindexHadamard_natCast]
      rfl

end Hadamard


-- Mathlib Data Finset Prod
-- Cartesian Product? In type def of Hadamard for size of matrix
-- Theorem that proves ⊗ₖ indices can be reindexed without any change to the matrix
