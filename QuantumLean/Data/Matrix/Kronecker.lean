import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Notation
import Mathlib.Data.Matrix.Kronecker
import Mathlib.Data.Complex.Basic
import Mathlib.Logic.Equiv.Fin

import «QuantumLean».Data.Circuits.Basic

open Matrix
open Kronecker
open Complex

namespace Matrix
section KroneckerNatCast


theorem natCast_kronecker {A B : Type} [DecidableEq A] [DecidableEq B] (m : ℕ) (M : Matrix B B ℂ) :
    (m : Matrix A A ℂ) ⊗ₖ M = m • ((1 : Matrix A A ℂ) ⊗ₖ M) := by
  simp_rw [← nsmul_one]
  simp only [nsmul_eq_smul_cast ℕ, Nat.cast_id, Nat.cast_mul]
  rw [smul_kronecker]


theorem kronecker_natCast {A B : Type} [DecidableEq A] [DecidableEq B] (m : ℕ) (M : Matrix B B ℂ) :
    M ⊗ₖ (m : Matrix A A ℂ) = m • (M ⊗ₖ (1 : Matrix A A ℂ)) := by
  simp_rw [← nsmul_one]
  simp only [nsmul_eq_smul_cast ℕ, Nat.cast_id, Nat.cast_mul]
  rw [kronecker_smul]

theorem kronecker_natCast_natCast {A B : Type} [DecidableEq A] [DecidableEq B] (m₁ m₂ : ℕ) :
    (m₁ : Matrix A A ℂ) ⊗ₖ (m₂ : Matrix B B ℂ) = ((m₁ * m₂ : ℕ) : Matrix (A × B) (A × B) ℂ) := by
  simp_rw [← nsmul_one]
  simp only [nsmul_eq_smul_cast ℕ, Nat.cast_id, Nat.cast_mul]
  rw [smul_kronecker, kronecker_smul, one_kronecker_one, smul_smul]
  rfl


def fin_one_equiv : Fin n ≃ Fin (2 ^ 0) × Fin n := by
  rw [pow_zero]
  nth_rewrite 1 [← one_mul n]
  exact finProdFinEquiv.symm


end KroneckerNatCast
end Matrix
