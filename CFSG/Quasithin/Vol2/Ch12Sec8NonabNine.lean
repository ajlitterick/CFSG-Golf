module

public import CFSG.Quasithin.Vol2.Ch12Sec8NonabMod

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {T M L : Subgroup G}

namespace Hyp1281Two

variable (h : Hyp1281Two G T M L) (hU : ¬ IsMulCommutative ↥(uOfL22 T M)) {g : G}
  (hg : GoodElt128 T L g)

include h hU hg

theorem sup_le_normalizer_inf_rconj_wOfU :
    L ⊔ uOfL22 T M ≤ Subgroup.normalizer ((wOfU T M ⊓ rconj (wOfU T M) g : Subgroup G) : Set G) := by
  rw [h.wOfU_inf_rconj_eq hU hg]
  exact h.sup_le_normalizer_inf_rconj hU hg

theorem exists_mul_of_mem_pCoreOf_sup {s : G} (hs : s ∈ pCoreOf 2 (L ⊔ uOfL22 T M)) :
    ∃ w ∈ wOfU T M, ∃ x ∈ rconj (wOfU T M) g, s = w * x := by
  have : s ∈ (wOfU T M : Set G) * (rconj (wOfU T M) g : Set G) := by
    rw [← (h.pCoreOf_sup_uOfL22_eq_wOfU_sup hU hg).2]
    exact hs
  obtain ⟨w, hw, x, hx, hwx⟩ := this
  exact ⟨w, hw, x, hx, hwx.symm⟩


theorem lemma_12_8_9_six {u : G} (hu : u ∈ uOfL22 T M) (huW : u ∉ wOfU T M) {x : G}
    (hx : x ∈ rconj (wOfU T M) g)
    (hxu : x * u * x⁻¹ * u⁻¹ ∈ centerOf (uOfL22 T M)) :
    x ∈ rconj (centerOf (uOfL22 T M)) g ⊔ (wOfU T M ⊓ rconj (wOfU T M) g) := by
  set ζ := u * x * u⁻¹ * x⁻¹ with hζ
  have hζZ : ζ ∈ centerOf (uOfL22 T M) := by
    have e : ζ = (x * u * x⁻¹ * u⁻¹)⁻¹ := by rw [hζ]; group
    rw [e]
    exact (centerOf (uOfL22 T M)).inv_mem hxu
  have hζW : ζ ∈ wOfU T M := centerOf_uOfL22_le_wOfU T M hζZ
  have h1 := (h.module_relations hU hg hu huW).2.2.1 x hx ζ hζW (by
    have : (u * x * u⁻¹ * x⁻¹)⁻¹ * ζ = 1 := by rw [← hζ]; group
    rw [this]
    exact Subgroup.one_mem _)
  have hyZg : g⁻¹ * ζ * g ∈ rconj (centerOf (uOfL22 T M)) g := inv_mul_mul_mem_rconj hζZ
  have e : x = (g⁻¹ * ζ * g) * (x⁻¹ * (g⁻¹ * ζ * g))⁻¹ := by group
  rw [e]
  exact Subgroup.mul_mem_sup hyZg ((wOfU T M ⊓ rconj (wOfU T M) g).inv_mem h1)

end Hyp1281Two

namespace Hyp1281Two

theorem oTwoUpper_sup_eq (h : Hyp1281Two G T M L) : oTwoUpper (L ⊔ T) = L := by
  apply le_antisymm
  · exact oTwoUpper_le_of_pow_mem fun x hx =>
      exists_pow_two_pow_mem_of_le_normalizer (h.inM.2.trans h.normal) h.sylow.1 hx
  · calc L = oTwoUpper L := h.residual.symm
      _ ≤ oTwoUpper (L ⊔ T) := oTwoUpper_mono le_sup_left

theorem exists_goodElt_L (h : Hyp1281Two G T M L) : ∃ g : G, GoodElt128 T L g := by
  obtain ⟨l, hlL, hlodd, hlC⟩ := h.exists_odd_not_mem_centralizer
  refine ⟨l, hlL, fun hlN => hlC ?_⟩
  exact h.mem_centralizer_of_odd (h.isTwoReducedIn.1.2.1 (h.le hlL)) hlN hlodd

theorem LT_le_normalizer_sup_uOfL22 (h : Hyp1281Two G T M L) :
    L ⊔ T ≤ Subgroup.normalizer ((L ⊔ uOfL22 T M : Subgroup G) : Set G) := by
  refine sup_le ((le_sup_left : L ≤ L ⊔ uOfL22 T M).trans Subgroup.le_normalizer) ?_
  intro t ht
  exact Subgroup.inf_normalizer_le_normalizer_sup L (uOfL22 T M)
    ⟨h.inM.2.trans h.normal ht, h.T_le_normalizer_uOfL22 ht⟩


end Hyp1281Two

end CFSG.Quasithin
