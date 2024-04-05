import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Notation
import Mathlib.Data.Complex.Basic

open Matrix
open Complex

@[simp]
def XGate : Matrix (Fin 2) (Fin 2) ℤ :=
  !![0, 1; 1, 0]

@[simp]
def YGate : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, -I; I, 0]

@[simp]
def ZGate : Matrix (Fin 2) (Fin 2) ℤ :=
  !![1, 0; 0, -1]
