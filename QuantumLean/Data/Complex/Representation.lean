import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Sqrt

open Complex


namespace CauSeq.Completion
open CauSeq
section

variable {α : Type*} [LinearOrderedField α]
variable {β : Type*} [Ring β] (abv : β → α) [IsAbsoluteValue abv]

unsafe instance [Repr β] : Repr (Cauchy abv) where
  reprPrec r _ :=
    let seq := r.unquot
    repr (seq 100)

end
end CauSeq.Completion

namespace Real
unsafe instance : Repr ℝ where reprPrec r _ := repr r.cauchy

end Real

namespace Complex


unsafe instance instRepr : Repr Complex where
  reprPrec f p := Repr.addAppParen (repr f.re ++ " + " ++ repr f.im ++ "*I") p

end Complex
