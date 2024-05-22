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

-- Implement a set of "qubit" related definitions and theorems :)
-- Could perhaps be a place where Dirac is implemened at some point?

abbrev Qubit (n : ℕ) := nMatrix' n 0
