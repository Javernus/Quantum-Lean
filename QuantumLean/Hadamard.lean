import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Notation
import Mathlib.Data.Matrix.Kronecker

open Matrix
open Kronecker


section HnxHn
variable { n : ℕ }

@[simp]
def reindexHadamard (A : Matrix (Fin (2 ^ n) × Fin 2) (Fin (2 ^ n) × Fin 2) ℤ) : Matrix (Fin (2 ^ (n + 1))) (Fin (2 ^ (n + 1))) ℤ :=
  reindex finProdFinEquiv finProdFinEquiv A


@[simp]
theorem reindexHadamard_smul (A : Matrix (Fin (2 ^ n) × Fin 2) (Fin (2 ^ n) × Fin 2) ℤ) (c : ℕ) : reindexHadamard (c • A) = c • reindexHadamard A := by
  simp only [reindexHadamard, Nat.add_eq, Nat.add_zero, Nat.pow_eq, reindex_apply]
  rw [submatrix_smul]
  simp

@[simp]
theorem reindexHadamard_one : reindexHadamard (1 : Matrix (Fin (2 ^ n) × Fin 2) (Fin (2 ^ n) × Fin 2) ℤ) = 1 := by
  simp


@[simp]
theorem reindexHadamard_smul_one (c : ℕ) : reindexHadamard (c • (1 : Matrix (Fin (2 ^ n) × Fin 2) (Fin (2 ^ n) × Fin 2) ℤ)) = c • 1 := by
  rw [reindexHadamard_smul, reindexHadamard_one]


@[simp]
def Hadamard : (n : ℕ) -> Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℤ
  | 0 => 1
  | (n + 1) => reindexHadamard (Hadamard n ⊗ₖ !![1, 1; 1, -1])

@[simp]
theorem HeqH : Hadamard 1 = !![1, 1; 1, -1] := by decide


@[simp]
theorem HxH : Hadamard 1 * Hadamard 1 = 2 := by decide


@[simp]
theorem TwoXI : (2 : Matrix (Fin 2) (Fin 2) ℤ) = (2 : ℕ) • 1 := by simp


@[simp]
theorem TwoToNXI : (2 ^ n : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℤ) = (2 ^ n : ℕ) • 1 := by simp


@[simp]
theorem TwoToNPlus1XI : (2 ^ (n + 1) : Matrix (Fin (2 ^ (n + 1))) (Fin (2 ^ (n + 1))) ℤ) = (2 ^ (n + 1) : ℕ) • 1 := by
  simp only [smul_eq_mul, mul_comm, pow_succ]
  rw [mul_comm]
  simp


@[simp]
theorem TwoXTwoToNXI : (2 : ℕ) • (2 ^ n : ℕ) = 2 ^ (n + 1) := by
  rw [smul_eq_mul, mul_comm, ← pow_succ]


@[simp]
theorem Hsuccn : Hadamard (n + 1) = reindexHadamard (Hadamard n ⊗ₖ !![1, 1; 1, -1]) := by rfl



@[simp]
theorem postKroneckerReindex : reindexHadamard (M ⊗ₖ !![1, 1; 1, -1]) * reindexHadamard (M ⊗ₖ !![1, 1; 1, -1]) = reindexHadamard ((M ⊗ₖ !![1, 1; 1, -1]) * (M ⊗ₖ !![1, 1; 1, -1])) := by
  simp


-- In general, I am trying to prove H * H = I (× a constant) for Hadamard matrices
theorem HnxHn : Hadamard n * Hadamard n = 2 ^ n * 1 := by
  induction n with
    | zero => simp
    | succ n ih =>
      rw [Hsuccn]
      simp only [Nat.succ_eq_add_one]
      -- Turn current (Hn ⊗ₖ H1) * (Hn ⊗ₖ H1) into (Hn * Hn) ⊗ₖ (H1 * H1)
      rw [postKroneckerReindex, ← mul_kronecker_mul, ← HeqH, HxH, ih]
      simp only [mul_one]
      rw [TwoXI, TwoToNXI, kroneckerMap_smul_right _ (2 : ℕ) _ (2 ^ n • 1) 1, kroneckerMap_smul_left _ (2 ^ n) _ _ 1]
      rw [kroneckerMap_one_one]
      -- Why do I now have 4 cases to prove? I thought I was only rewriting equivalences...
      case succ.hf₁ => simp
      case succ.hf₂ => simp
      case succ.hf₃ => simp
      case succ =>
        -- I don't really know how to solve this anymore, in my head, this is just an equality
        -- but with the reindexHadamard and powers, I am struggling.
        rw [← smul_assoc, TwoXTwoToNXI, TwoToNPlus1XI, reindexHadamard_smul_one]
      simp [nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat, mul_assoc]
      simp [nsmul_eq_mul, mul_comm, mul_assoc]

end HnxHn


-- Mathlib Data Finset Prod
-- Cartesian Product? In type def of Hadamard for size of matrix
-- Theorem that proves ⊗ₖ indices can be reindexed without any change to the matrix
