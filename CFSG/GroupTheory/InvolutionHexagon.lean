module

public import CFSG.GroupTheory.InvolutionHexagonAction
public import CFSG.GroupTheory.SevenInvolutionWreathLaw

public section

namespace CFSG.GroupTheory.InvolutionHexagon

open CFSG.Assembly CFSG.GroupTheory.SevenInvolutionWreathLaw


theorem localData_of_wreath {G : Type*} [Group G] [Finite G]
    (hconj : ∀ u v : G, orderOf u = 2 → orderOf v = 2 → IsConj u v) {s t w : G}
    (hst : s * t = t * s) (hs : orderOf s = 4) (ht : orderOf t = 4)
    (hinter : Subgroup.zpowers s ⊓ Subgroup.zpowers t = ⊥) (hw : orderOf w = 2)
    (hwout : w ∉ Subgroup.closure {s, t}) (hsw : w⁻¹ * s * w = t) (htw : w⁻¹ * t * w = s)
    (h7 : {g : G | g ∈ Subgroup.centralizer {(s * t) ^ 2} ∧ orderOf g = 2}.ncard = 7) :
    InvolutionProductLaw G ∧
      ∀ z : {g : G // orderOf g = 2}, ((involutionGraph G).neighborSet z).ncard = 6 := by
  obtain ⟨hlaw, hval, -⟩ := seven_involution_centralizer_wreath_law_and_small_polygons hconj
    (Subgroup.closure {s, t, w}) s t w hst hs ht hinter hw hwout hsw htw rfl h7
  exact ⟨hlaw, hval⟩

end CFSG.GroupTheory.InvolutionHexagon
