-- import Lean.Meta.Tactic.LibrarySearch
-- import Aesop.Main

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Notation
import Mathlib.Data.Complex.Basic

-- Import the gates
import «QuantumLean».Data.Circuits.Basic
import «QuantumLean».Data.Matrix.Kronecker

open Matrix
open Complex
open Kronecker
open Circuits


section VariableDimensions


variable {m m' n n' : ℕ}


@[simp]
def tensor_power (n : ℕ) (gates : ℕ -> nMatrix' m m') : nMatrix' (m * n) (m' * n) :=
  match n with
    | 0 => !![1]
    | (n + 1) => reindex₃ (tensor_power n gates ⊗ₖ gates (n + 1))


abbrev tensor_power' (n : ℕ) (M : nMatrix' m m') := tensor_power n (fun _ => M)

-- Not the best definition due to it only working well for 1 qubit gates
abbrev apply_at (n i : ℕ) (M : nMatrix m) := tensor_power n (fun j => if i == j then M else 1)

theorem tensor_power_zero { gates : ℕ -> nMatrix' m m' } : tensor_power 0 gates = !![1] := by
  simp [tensor_power]


-- theorem reindex_tensor {m m' : ℕ} {A : nMatrix' m m'} : reindex₂ (reindex₃ (reindex (Equiv.uniqueProd (Fin (2 ^ m)) (Fin 1)).symm (Equiv.uniqueProd (Fin (2 ^ m')) (Fin 1)).symm A)) = A := by
--   simp [reindex₂, reindex₃]
--   induction m with
--     | zero =>
--     induction m' with
--       | zero =>
--         simp [Nat.zero_eq, Nat.pow_zero]
--         ext i j
--         fin_cases i <;> fin_cases j <;> rfl
--       | succ m ih₁ =>
--         ext i j
--         fin_cases i
--         rw?



-- theorem tensor_power_one {m m' : ℕ} { gates : ℕ -> nMatrix' m m' } : reindex₂ (tensor_power 1 gates) = gates 1 := by
--   simp
--   rw [kronecker_matOne]
--   simp only [reindex_apply, Equiv.symm_symm, Equiv.coe_uniqueProd]
--   simp [reindex₂, reindex₃, QCount]
--   induction m with
--     | zero =>
--       induction m' with
--         | zero =>
--           simp only [Nat.zero_eq, Nat.pow_zero]
--           ext i j
--           fin_cases i <;> fin_cases j <;> rfl
--         | succ m' ih₁ =>
--           simp only [Nat.zero_eq, Nat.pow_zero]
--           rw [ih₁]

--     | succ m ih =>

--     ext i j <;> fin_cases i <;> fin_cases j <;> rfl


theorem tensor_power_mul (M N : ℕ -> nMatrix m)
  : tensor_power n (M * N) = tensor_power n M * tensor_power n N := by
  induction n with
    | zero => simp
    | succ n ih =>
      rw [tensor_power]
      rw [tensor_power]
      rw [tensor_power]
      rw [← reindex₃_mul]
      rw [← mul_kronecker_mul]
      rw [ih]
      rw [← @Pi.mul_apply]


theorem one_eq' : !![1] = (1 :  nMatrix' (m * Nat.zero) (m * Nat.zero)) := by
  ext i j
  fin_cases i; fin_cases j; rfl


theorem tensor_power_of_one : tensor_power n (fun _ => (1 : nMatrix m)) = 1 := by
  induction n with
    | zero =>
      simp [tensor_power]
      exact one_eq'
    | succ n ih =>
      rw [tensor_power]
      rw [ih]
      rw [one_kronecker_one, reindex₃_one]


theorem tensor_power_of_natCast { i : ℕ } : tensor_power n (fun _ => (i : nMatrix m)) = ↑(i ^ n) := by
  induction n with
    | zero => rw [tensor_power_zero]; rw [Nat.pow_zero i, Nat.cast_one]; exact one_eq
    | succ n ih => rw [tensor_power, ih, kronecker_natCast_natCast, reindex₃_natCast, ← Nat.pow_succ]


theorem tensor_power_smul (M : nMatrix m) (c : ℕ)
  : tensor_power n (fun _ => c • M) = c ^ n • tensor_power n (fun _ => M) := by
  induction n with
    | zero => simp [tensor_power]
    | succ n ih =>
      rw [tensor_power, tensor_power, ih, smul_kronecker, kronecker_smul, ← smul_assoc, smul_reindex₃]
      rw [Nat.pow_succ, smul_eq_mul]


theorem tensor_power_mul_tensor_power (M : ℕ -> nMatrix' m m') (N : ℕ -> nMatrix' m' o)
  : tensor_power n M * tensor_power n N = tensor_power (n) (λ i => M i * N i) := by
  induction n with
    | zero => simp [tensor_power]
    | succ m ih =>
      rw [tensor_power]
      rw [tensor_power]
      rw [tensor_power]
      rw [← reindex₃_mul]
      rw [← mul_kronecker_mul]
      rw [ih]


-- theorem tensor_power_slice { m m' n o : ℕ } (M : nMatrix' m m')
--   : tensor_power' (n * o) M = reindex₄ (tensor_power' o (tensor_power' n M)) := by
--   rw [tensor_power', tensor_power', tensor_power']
--   induction n with
--     | zero =>
--       rw [@tensor_power_zero]
--       simp only [Nat.zero_eq, Nat.mul_zero]





end VariableDimensions
