import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Notation
import Mathlib.Data.Complex.Basic

-- Import the gates
import «QuantumLean».Hadamard
import «QuantumLean».PauliGates
import «QuantumLean».NecessaryCode

open Matrix
open Complex


theorem HH : Hadamard * Hadamard = 2 :=
  by
    rw [Hadamard]
    simp [mul_apply]
    rw [ofNat_fin_two]
    norm_num

theorem XX : XGate * XGate = 1 :=
  by
    rw [XGate]
    simp [mul_apply]
    rw [one_fin_two]

theorem ZZ : ZGate * ZGate = 1 :=
  by
    rw [ZGate]
    simp [mul_apply]
    rw [one_fin_two]

theorem HZHeqX : Hadamard * ZGate * Hadamard = 2 * XGate :=
  by
    rw [Hadamard, XGate, ZGate]
    simp [mul_apply]
    rw [ofNat_fin_two]
    norm_num

theorem HXHeqZ : Hadamard * XGate * Hadamard = 2 * ZGate :=
  by
    rw [Hadamard, XGate, ZGate]
    simp [mul_apply]
    rw [ofNat_fin_two]
    norm_num
