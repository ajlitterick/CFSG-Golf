module

public import CFSG.Quasithin.Vol2.Ch12Sec8OneAbsMod

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

namespace L128A

namespace Setting

variable {G : Type} [Group G] [Finite G] {V V₁ L T : Subgroup G}

variable (S : Setting V V₁ L T) {g : G}
  (hg : Good V₁ L g)

include S hg

theorem sup_le_normalizer_inf_rconj_wA :
    L ⊔ uA V V₁ ≤ Subgroup.normalizer ((wA V V₁ ⊓ rconj (wA V V₁) g : Subgroup G) : Set G) := by
  rw [S.wA_inf_rconj_eq hg]
  exact S.sup_le_normalizer_inf_rconj hg


theorem nine_six {u : G} (hu : u ∈ uA V V₁) (huW : u ∉ wA V V₁) {x : G}
    (hx : x ∈ rconj (wA V V₁) g)
    (hxu : x * u * x⁻¹ * u⁻¹ ∈ centerOf (uA V V₁)) :
    x ∈ rconj (centerOf (uA V V₁)) g ⊔ (wA V V₁ ⊓ rconj (wA V V₁) g) := by
  set ζ := u * x * u⁻¹ * x⁻¹ with hζ
  have hζZ : ζ ∈ centerOf (uA V V₁) := by
    have e : ζ = (x * u * x⁻¹ * u⁻¹)⁻¹ := by rw [hζ]; group
    rw [e]
    exact (centerOf (uA V V₁)).inv_mem hxu
  have hζW : ζ ∈ wA V V₁ := centerOf_uA_le_wA V V₁ hζZ
  have h1 := (S.module_relations hg hu huW).2.2.1 x hx ζ hζW (by
    have : (u * x * u⁻¹ * x⁻¹)⁻¹ * ζ = 1 := by rw [← hζ]; group
    rw [this]
    exact Subgroup.one_mem _)
  have hyZg : g⁻¹ * ζ * g ∈ rconj (centerOf (uA V V₁)) g := inv_mul_mul_mem_rconj hζZ
  have e : x = (g⁻¹ * ζ * g) * (x⁻¹ * (g⁻¹ * ζ * g))⁻¹ := by group
  rw [e]
  exact Subgroup.mul_mem_sup hyZg ((wA V V₁ ⊓ rconj (wA V V₁) g).inv_mem h1)

end Setting

end L128A

end CFSG.Quasithin.H13
