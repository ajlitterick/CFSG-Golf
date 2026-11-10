module

public import CFSG.LocalAnalysis.ComponentClassification.HeldBalCentre
import CFSG.LocalAnalysis.ComponentClassification.CatLeafAlt
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitTypeRank

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup

theorem centreTwoPartLe_he (h : TBLit.HeldTrivialMultiplier) :
    CentreTwoPartLe Blueprint.NativeSporadic.He 1 := by
  intro L _ _ hq e S
  have hZ : Subgroup.center L = ⊥ := h L hq e
  have h1 : Nat.card (Subgroup.center L) = 1 := by
    rw [hZ]
    exact Subgroup.card_bot
  exact (Subgroup.card_le_card_group S).trans h1.le


end CFSG.ComponentClassification.GrSLit
