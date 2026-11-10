module

public import CFSG.Quasithin.Background.A3Structure312Nonquasi

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique
open scoped commutatorElement


namespace A321

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem cComp_eq_top_of_quasisimple (hq : CFSG.IsQuasisimple X) {L : Subgroup X}
    (hL : L ∈ cComp (⊤ : Subgroup X)) : L = ⊤ := by
  have hsub : L.IsSubnormal := A3.subnormal_top_iff.mp (subnormal_of_mem_cComp hL)
  rcases A3.eq_top_or_le_center_of_subnormal hq hsub with h | h
  · exact h
  · exfalso
    apply ne_bot_of_mem_cComp hL
    calc L = ⁅L, L⁆ := (perfect_of_mem_cComp hL).symm
      _ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
        (h.trans (Subgroup.center_le_centralizer _))

end A321


end CFSG.Quasithin
