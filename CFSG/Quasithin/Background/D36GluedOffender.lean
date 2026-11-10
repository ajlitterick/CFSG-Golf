module

public import CFSG.Quasithin.Background.D36GluedShape
import CFSG.Quasithin.Background.F918V5A

public section

namespace CFSG.Quasithin

section Abstract

variable {Y : Type} [CommGroup Y] [Finite Y]

structure GluedSwap (X A : Subgroup (MulAut Y)) (U U' : Subgroup Y) : Prop where
  pair : GluedPair X U U'
  ne : U ≠ U'
  gap : rk ↥(U ⊓ U') + 2 < rk ↥U
  mem : A ∈ QhatStar X
  swaps : ¬ A ≤ stabSub U


namespace GluedSwap

variable {X A : Subgroup (MulAut Y)} {U U' : Subgroup Y}


theorem isPGroup (h : GluedSwap X A U U') : IsPGroup 2 A :=
  D36.isPGroup_of_mem_QhatStar h.mem


theorem ne_bot (h : GluedSwap X A U U') : A ⊓ stabSub U ≠ ⊥ :=
  (glued_swap_shape h.pair h.ne h.gap h.mem h.swaps).1


end GluedSwap


namespace GluedSwap


end GluedSwap

end Abstract

end CFSG.Quasithin
