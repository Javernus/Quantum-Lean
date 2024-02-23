-- This code is merged in the mathlib4 PR #10592, but it is not yet released.

import Mathlib.Data.Matrix.Notation

open Matrix

section AddMonoidWithOne
 variable [AddMonoidWithOne α]

 theorem natCast_fin_two (n : ℕ) : (n : Matrix (Fin 2) (Fin 2) α) = !![↑n, 0; 0, ↑n] := by
   ext i j
   fin_cases i <;> fin_cases j <;> rfl

 theorem natCast_fin_three (n : ℕ) :
     (n : Matrix (Fin 3) (Fin 3) α) = !![↑n, 0, 0; 0, ↑n, 0; 0, 0, ↑n] := by
   ext i j
   fin_cases i <;> fin_cases j <;> rfl

 -- See note [no_index around OfNat.ofNat]
 theorem ofNat_fin_two (n : ℕ) [n.AtLeastTwo] :
     (no_index (OfNat.ofNat n) : Matrix (Fin 2) (Fin 2) α) =
       !![OfNat.ofNat n, 0; 0, OfNat.ofNat n] :=
   natCast_fin_two _

 -- See note [no_index around OfNat.ofNat]
 theorem ofNat_fin_three (n : ℕ) [n.AtLeastTwo] :
     (no_index (OfNat.ofNat n) : Matrix (Fin 3) (Fin 3) α) =
       !![OfNat.ofNat n, 0, 0; 0, OfNat.ofNat n, 0; 0, 0, OfNat.ofNat n] :=
   natCast_fin_three _

 end AddMonoidWithOne
