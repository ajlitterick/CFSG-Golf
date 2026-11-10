module

public import CFSG.Quasithin.Recognition.RuTypeJ36a

public section

namespace CFSG.Quasithin.RuType

open CFSG.Open CFSG.Quasithin CFSG.LieType.BorelTits CFSG.QuasithinUnique

variable {G : Type} [Group G]

noncomputable abbrev B5P (b : G) : Subgroup (P5 b) := (Subgroup.zpowers b).subgroupOf (P5 b)

theorem comm_b_P5 {b x : G} (hx : x ∈ P5 b) : x * b = b * x := mem_G5.mp (P5_le_G5 b hx)

theorem comm_zpowers_P5 {b x : G} (hx : x ∈ P5 b) (k : ℤ) : x * b ^ k = b ^ k * x :=
  ((Commute.zpow_right (comm_b_P5 hx) k)).eq

instance B5P_normal (b : G) : (B5P b).Normal :=
  ⟨fun x hx g => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hx
    have e : ((g * x * g⁻¹ : P5 b) : G) = x := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [← hk, comm_zpowers_P5 g.2 k, mul_inv_cancel_right]
    rw [e]
    exact hx⟩

noncomputable abbrev V5 (b : G) : Type := ↥(P5 b) ⧸ B5P b

@[expose] noncomputable def conjP5 [Finite G] {b c : G}
    (hc : c ∈ Subgroup.normalizer (Subgroup.zpowers b : Set G)) : P5 b →* P5 b where
  toFun x := ⟨c * x * c⁻¹, conj_mem_P5_of_normalizes hc x.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

@[expose] noncomputable def actV [Finite G] {b c : G}
    (hc : c ∈ Subgroup.normalizer (Subgroup.zpowers b : Set G)) : V5 b →* V5 b :=
  QuotientGroup.map (B5P b) (B5P b) (conjP5 hc) (fun x hx => by
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
    rw [Subgroup.mem_subgroupOf] at hx
    exact (Subgroup.mem_normalizer_iff.mp hc _).mp hx)


theorem G5_le_normalizer [Finite G] {b c : G} (hc : c ∈ G5 b) :
    c ∈ Subgroup.normalizer (Subgroup.zpowers b : Set G) := by
  refine mem_normalizer_of_conj_mem fun y hy => ?_
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  rw [((Commute.zpow_right (mem_G5.mp hc) k)).eq, mul_inv_cancel_right]
  exact hy

namespace RuDataM

variable (M : RuDataM G) [Finite G]

section Five

variable {M} {b : G} (hbH : b ∈ ruH M.T) (hb5 : orderOf b = 5)
include hbH hb5

theorem card_P5_eq_125
    : Nat.card (P5 b) = 125 := by
  rw [(lemma_J27_5 hbH hb5).1]
  norm_num

theorem card_V5
    : Nat.card (V5 b) = 25 := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (B5P b)
  rw [card_P5_eq_125 hbH hb5, card_subgroupOf_of_le (zpowers_le_P5 hb5), Nat.card_zpowers,
    hb5] at h
  show Nat.card (↥(P5 b) ⧸ B5P b) = 25
  omega


end Five

end RuDataM

end CFSG.Quasithin.RuType
