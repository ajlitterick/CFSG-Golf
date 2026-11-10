module

public import CFSG.Milestones.ASVolI.A3Aut.Core

public section

namespace CFSG.ASVolI

open scoped Pointwise

section Core2

variable {A : Type} [Group A] [Finite A]


theorem burnsideAut_le_conj_complement {E Y C X : Subgroup A}
    (hYE : Y ≤ Subgroup.normalizer (E : Set A)) (hE : IsPGroup 2 E) (hCY : C ≤ Y)
    (hEC : E ⊓ C = ⊥) (hECY : E ⊔ C = Y) (hXY : X ≤ Y) (hXodd : Odd (Nat.card X)) :
    ∃ e ∈ E, X ≤ C.map (MulAut.conj e).toMonoidHom := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C₁ : Subgroup A := (E ⊔ X) ⊓ C with hC₁
  have hEY : E ≤ Y := hECY ▸ le_sup_left
  have hXE : X ≤ Subgroup.normalizer (E : Set A) := hXY.trans hYE
  have hCE : C ≤ Subgroup.normalizer (E : Set A) := hCY.trans hYE
  have hC₁E : C₁ ≤ Subgroup.normalizer (E : Set A) := inf_le_right.trans hCE
  have hsup : E ⊔ C₁ = E ⊔ X := by
    refine le_antisymm (sup_le le_sup_left inf_le_left) (sup_le le_sup_left ?_)
    intro x hx
    have hxY : x ∈ E ⊔ C := hECY ▸ hXY hx
    obtain ⟨e, he, c, hc, rfl⟩ := (burnsideAut_mem_sup_iff hCE).1 hxY
    have hcC₁ : c ∈ C₁ := by
      refine ⟨?_, hc⟩
      have : c = e⁻¹ * (e * c) := by group
      rw [this]
      exact (E ⊔ X).mul_mem (Subgroup.mem_sup_left (E.inv_mem he)) (Subgroup.mem_sup_right hx)
    exact Subgroup.mul_mem_sup he hcC₁
  have hdisjC₁ : Disjoint E C₁ := by
    rw [disjoint_iff, eq_bot_iff]
    intro x ⟨hxE, hxC₁⟩
    have : x ∈ E ⊓ C := ⟨hxE, hxC₁.2⟩
    rwa [hEC] at this
  have hdisjX : Disjoint E X := burnsideAut_disjoint_of_odd hE hXodd
  have hXp : ¬ 2 ∣ Nat.card X := by
    rw [← even_iff_two_dvd, Nat.not_even_iff_odd]
    exact hXodd
  obtain ⟨e, he, hC₁e⟩ := burnsideAut_conj_of_complements (p := 2) hXE hC₁E hE hXp hdisjX hdisjC₁
    hsup
  refine ⟨e, he, ?_⟩
  rw [← hC₁e]
  exact Subgroup.map_mono inf_le_right


end Core2

end CFSG.ASVolI
