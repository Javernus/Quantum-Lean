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
  rw [← nsmul_one, smul_kronecker]


theorem kronecker_natCast {A B : Type} [DecidableEq A] [DecidableEq B] (m : ℕ) (M : Matrix B B ℂ) :
    M ⊗ₖ (m : Matrix A A ℂ) = m • (M ⊗ₖ (1 : Matrix A A ℂ)) := by
  rw [← nsmul_one, kronecker_smul]


theorem kronecker_natCast_natCast {A B : Type} [DecidableEq A] [DecidableEq B] (m₁ m₂ : ℕ) :
    (m₁ : Matrix A A ℂ) ⊗ₖ (m₂ : Matrix B B ℂ) = ((m₁ * m₂ : ℕ) : Matrix (A × B) (A × B) ℂ) := by
  rw [natCast_kronecker, kronecker_natCast, one_kronecker_one, smul_smul, nsmul_one]


theorem blockDiagonal_unique {α A B : Type} [DecidableEq A] [DecidableEq B]
  (d : Fin 1 → Matrix A B α) [Zero α]:
  blockDiagonal d =
    Matrix.reindex (Equiv.prodUnique _ _).symm (Equiv.prodUnique _ _).symm (d default) := by
  ext ⟨a, ua⟩ ⟨b, ub⟩
  obtain rfl := Subsingleton.elim ua default
  obtain rfl := Subsingleton.elim ub default
  rfl


@[simp]
theorem kronecker_natOne {A B : Type} [DecidableEq A] [DecidableEq B] (M : Matrix A B ℂ) :
    (1 : Matrix (Fin 1) (Fin 1) ℂ) ⊗ₖ M =
      Matrix.reindex (Equiv.uniqueProd _ _).symm (Equiv.uniqueProd _ _).symm M := by
  rw [one_kronecker, blockDiagonal_unique]
  rfl


theorem one_eq : !![1] = (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
  ext i j
  fin_cases i; fin_cases j; rfl


theorem kronecker_matOne {A B : Type} [DecidableEq A] [DecidableEq B] (M : Matrix A B ℂ) : !![1] ⊗ₖ M = Matrix.reindex (Equiv.uniqueProd _ _).symm (Equiv.uniqueProd _ _).symm M := by
  rw [← @kronecker_natOne, one_eq]



end KroneckerNatCast
end Matrix
