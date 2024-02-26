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

-- Create the Oracle for the Deutsch Algorithm, i.e. O(a, b) = !![-1^a, 0; 0, 1^b] where a, b ∈ {0, 1}
def Oracle (a b : Bool) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![(-1)^(a.toNat), 0; 0, (-1)^(b.toNat)]

@[simp] lemma Oracle_apply_01 (a b : Bool) : (Oracle a b) 0 1 = 0 := by simp [Oracle]
@[simp] lemma Oracle_apply_10 (a b : Bool) : (Oracle a b) 1 0 = 0 := by simp [Oracle]

@[simp] lemma Oracle_apply_00 (a b : Bool) : (Oracle a b) 0 0 = (-1)^(a.toNat) := by simp [Oracle]
@[simp] lemma Oracle_apply_11 (a b : Bool) : (Oracle a b) 1 1 = (-1)^(b.toNat) := by simp [Oracle]

def ZeroQbit : Matrix (Fin 1) (Fin 2) ℤ := !![1, 0]
def OneQbit : Matrix (Fin 1) (Fin 2) ℤ := !![0, 1]
def PlusQbit : Matrix (Fin 1) (Fin 2) ℤ := !![1, 1]
def MinusQbit : Matrix (Fin 1) (Fin 2) ℤ := !![1, -1]

def Measure (q : Matrix (Fin 1) (Fin 2) ℤ) : Bool :=
  (q 0 0) = 0

-- The Deutsch Algorithm
theorem DeutschAlgorithm (a b : Bool) : Measure (PlusQbit * (Oracle a b) * Hadamard) = (a != b) :=
  by
    -- Following solves the equality for each case: write it once
    -- simp [Oracle, PlusQbit, Hadamard, mul_apply]
    -- norm_num
    cases a; cases b;
    simp [Measure, Oracle, PlusQbit, Hadamard, mul_apply]
    simp [Measure, Oracle, PlusQbit, Hadamard, mul_apply]
    cases b;
    simp [Measure, Oracle, PlusQbit, Hadamard, mul_apply]
    simp [Measure, Oracle, PlusQbit, Hadamard, mul_apply]

theorem DeutschNew (a b : Bool) : Hadamard * (Oracle a b) * Hadamard = 2 * (-1)^(a.toNat) * XGate^(a.toNat + b.toNat) :=
  by
    cases a; cases b;
    simp [XGate, Oracle, PlusQbit, Hadamard, mul_apply]
    rw [ofNat_fin_two]
    norm_num
    simp [XGate, Oracle, PlusQbit, Hadamard, mul_apply]
    rw [ofNat_fin_two]
    norm_num
    cases b;
    simp [XGate, Oracle, PlusQbit, Hadamard, mul_apply]
    rw [ofNat_fin_two]
    norm_num
    simp [XGate, Oracle, PlusQbit, Hadamard, mul_apply]
    rw [ofNat_fin_two]
    norm_num


-- Create a theorem with inputs a and b which are either 0 or 1 (Natural number type)
