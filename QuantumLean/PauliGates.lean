import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Notation
import Mathlib.Data.Complex.Basic

open Matrix
open Complex

def XGate : Matrix (Fin 2) (Fin 2) ℤ :=
  !![0, 1; 1, 0]

def YGate : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, -I; I, 0]

def ZGate : Matrix (Fin 2) (Fin 2) ℤ :=
  !![1, 0; 0, -1]

@[simp] lemma XGate_apply_0_0 : XGate 0 0 = 0 := rfl
@[simp] lemma XGate_apply_0_1 : XGate 0 1 = 1 := rfl
@[simp] lemma XGate_apply_1_0 : XGate 1 0 = 1 := rfl
@[simp] lemma XGate_apply_1_1 : XGate 1 1 = 0 := rfl

@[simp] lemma YGate_apply_0_0 : YGate 0 0 = 0 := rfl
@[simp] lemma YGate_apply_0_1 : YGate 0 1 = -I := rfl
@[simp] lemma YGate_apply_1_0 : YGate 1 0 = I := rfl
@[simp] lemma YGate_apply_1_1 : YGate 1 1 = 0 := rfl

@[simp] lemma ZGate_apply_0_0 : ZGate 0 0 = 1 := rfl
@[simp] lemma ZGate_apply_0_1 : ZGate 0 1 = 0 := rfl
@[simp] lemma ZGate_apply_1_0 : ZGate 1 0 = 0 := rfl
@[simp] lemma ZGate_apply_1_1 : ZGate 1 1 = -1 := rfl
