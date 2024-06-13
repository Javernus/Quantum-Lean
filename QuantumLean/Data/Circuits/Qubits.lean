import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Notation
import Mathlib.Data.Complex.Basic

-- Import the gates
import «QuantumLean».Data.Circuits.Basic
import «QuantumLean».Data.Circuits.VariableDimensions
import «QuantumLean».Data.Matrix.Kronecker

open Matrix
open Complex
open Kronecker
open Circuits

-- Implement a set of "qubit" related definitions and theorems :)
-- Could perhaps be a place where Dirac is implemened at some point?

abbrev Qubit (n : ℕ) := nMatrix' 0 n


/-- A vector with values of s n -/
-- def Q (n : ℕ) (s : ℕ -> ℂ) : Qubit n := of fun _ i => s i
def Q {n : ℕ} (s : QCount n -> ℂ) : Qubit n := of fun _ i => s i
def Q' (n : ℕ) (s : ℂ) : Qubit n := of fun _ _ => s

def QZero : Qubit 1 := !![1, 0]
def QZeroₙ (n : ℕ) := tensor_power' n QZero
def Q₀ : Qubit 2 := !![1, 0, 0, 0]
