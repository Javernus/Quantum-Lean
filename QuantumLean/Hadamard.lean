import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Notation

open Matrix

def Hadamard : Matrix (Fin 2) (Fin 2) ℤ :=
  !![1, 1; 1, -1]

@[simp] lemma Hadamard_apply (j : Fin 2) : Hadamard j 0 = 1 := by simp [Hadamard]

@[simp] lemma Hadamard_apply11 : Hadamard 1 1 = -1 := by simp [Hadamard]

@[simp] lemma Hadamard_apply01 : Hadamard 0 1 = 1 := by simp [Hadamard]
