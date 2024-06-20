import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Complex.Basic

/-
This file defines the abbreviated types used in Quantum Lean.
Primed (with ' at the end) abbreviations should not be used in formalisations. They
are meant for internal Quantum Lean theorems and reindexings.

- QCount: a shorthand for the size of a dimension for n qubits. (n : ℕ) as argument.

- nGate: a definition of a gate for n qubits. (n : ℕ) as argument.
- nQubit: a definition for n qubits. Takes in a natural number. (n : ℕ) as argument.
-/

namespace Circuits
section Types

@[simp]
abbrev QCount (n : ℕ) := Fin (2 ^ n)

@[simp]
abbrev nGate' (n n' : ℕ) := Matrix (QCount n) (QCount n') ℂ
@[simp]
abbrev mnGate'' (m m' n n' : ℕ) := Matrix (QCount m × QCount n) (QCount m' × QCount n') ℂ

@[simp]
abbrev nGate (n : ℕ) := nGate' n n
@[simp]
abbrev mnGate' (m n : ℕ) := mnGate'' m m n n

@[simp]
abbrev nQubit (n : ℕ) := nGate' 0 n

end Types
end Circuits
