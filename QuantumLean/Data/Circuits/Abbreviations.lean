import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Complex.Basic

namespace Circuits
section Abbreviations

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
abbrev Qubit (n : ℕ) := nMatrix' 0 n

end Abbreviations
end Circuits
