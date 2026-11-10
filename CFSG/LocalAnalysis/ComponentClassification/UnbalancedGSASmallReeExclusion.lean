module

public import CFSG.LieType.Ree.SmallReeModelSchreier
public import CFSG.Walter.Ree.Model.PSL2
public import CFSG.LocalAnalysis.ComponentInitial.SLTwoInvolution
public import CFSG.LocalAnalysis.ComponentClassification.SmallLocalDihedral
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSCRankOneCenter

public section

namespace CFSG.ComponentClassification.UnbalancedGS

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.Walter.Ree.Model

namespace SmallReeExclusion

variable {H : Type*} [Group H]

theorem eq_one_or_eq_of_mem_zpowers {x y : H} (hx : x * x = 1) (hy : y ∈ Subgroup.zpowers x) :
    y = 1 ∨ y = x := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  rcases Int.even_or_odd' k with ⟨m, rfl | rfl⟩
  · left
    rw [zpow_mul, zpow_two, hx, one_zpow]
  · right
    rw [zpow_add, zpow_mul, zpow_two, hx, one_zpow, one_mul, zpow_one]

theorem triple_isElementaryAbelian_card [Finite H] {t x y : H} (ht : orderOf t = 2)
    (hx : orderOf x = 2) (hy : orderOf y = 2) (htx : t * x = x * t) (hty : t * y = y * t)
    (hxy : x * y = y * x) (hyx : y ∉ Subgroup.zpowers x)
    (hinf : Subgroup.zpowers t ⊓ (Subgroup.zpowers x ⊔ Subgroup.zpowers y) = ⊥) :
    IsElementaryAbelian 2
        (Subgroup.zpowers t ⊔ (Subgroup.zpowers x ⊔ Subgroup.zpowers y) : Subgroup H) ∧
      Nat.card (Subgroup.zpowers t ⊔ (Subgroup.zpowers x ⊔ Subgroup.zpowers y) : Subgroup H) =
        2 ^ 3 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hV, hVcard⟩ := RankOneCenter.pair_isElementaryAbelian_card hx hy hxy hyx
  have : IsElementaryAbelian 2 (Subgroup.zpowers x ⊔ Subgroup.zpowers y : Subgroup H) := hV
  have : IsElementaryAbelian 2 (Subgroup.zpowers t) :=
    IsElementaryAbelian.zpowers_of_pow_eq_one (ht ▸ pow_orderOf_eq_one t)
  have hcent : Subgroup.zpowers x ⊔ Subgroup.zpowers y ≤
      Subgroup.centralizer (Subgroup.zpowers t : Set H) := by
    refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_) <;>
      refine Subgroup.mem_centralizer_iff.mpr fun g hg => ?_ <;>
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    · exact (Commute.zpow_left htx k).eq
    · exact (Commute.zpow_left hty k).eq
  refine ⟨IsElementaryAbelian.sup_of_le_centralizer hcent, ?_⟩
  have hc : ∀ g ∈ Subgroup.zpowers t, ∀ h ∈ (Subgroup.zpowers x ⊔ Subgroup.zpowers y :
      Subgroup H), g * h = h * g := fun g hg h hh =>
    Subgroup.mem_centralizer_iff.mp (hcent hh) g hg
  have h := RankOneCenter.card_sup_mul_card_inf_of_commute _ _ hc
  rw [hinf, Subgroup.card_bot, mul_one, Nat.card_zpowers, ht, hVcard] at h
  rw [h]
  norm_num

end SmallReeExclusion

open SmallReeExclusion ReeTag


end CFSG.ComponentClassification.UnbalancedGS
