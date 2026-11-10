
module

public import CFSG.Monster.B.TwoA.Base.GeomResBase
public import CFSG.Monster.B.TwoA.Base.PetersenB

@[expose] public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA

open CFSG.Monster CFSG.Monster.B.Short CFSG.Monster.B Module

open CFSG.Monster.B.Co2 (v0)

attribute [local instance] parAction

private theorem zmod2_cases : ∀ t : ZMod 2, t = 0 ∨ t = 1 := by decide


theorem Vhat_eq_EU :
    Vhat = EU (Submodule.span (ZMod 2) {wFr}) := by
  have hw : wFr ∈ Submodule.span (ZMod 2) {wFr} := Submodule.mem_span_singleton_self _
  have h0 : (0 : Wv v0) ∈ Submodule.span (ZMod 2) {wFr} := Submodule.zero_mem _
  have hle : Vhat ≤ EU (Submodule.span (ZMod 2) {wFr}) := by
    intro d hd
    rcases (mem_Vhat_iff d).1 hd with rfl | rfl | rfl | rfl
    · exact Subgroup.one_mem _
    · exact xhat_mem_EU
    · exact Subgroup.mul_mem _ xhat_mem_EU (mem_EU_of (e := yhatE) (by rw [psiW_yhat]; exact hw))
    · exact mem_EU_of (e := yhatE) (by rw [psiW_yhat]; exact hw)
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [natCard_EU, natCard_submodule, finrank_span_singleton wFr_ne_zero,
    isKleinFour_Vhat.card_four]
  norm_num


end CFSG.Monster.B.TwoA
