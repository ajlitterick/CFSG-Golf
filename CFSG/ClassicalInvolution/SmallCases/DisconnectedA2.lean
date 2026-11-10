module

public import CFSG.Adapters.Involutions
public import CFSG.ClassicalInvolution.SmallCases.Partition
public import CFSG.ClassicalInvolution.SmallCases.DisconnectedControl

public section

namespace CFSG.ClassicalInvolution

open CFSG.Open CFSG.ClassicalInvolution.Generic

variable {G : Type} [Group G]

@[expose] def UniqueInvolutionNormal (K : Subgroup G) (z : G) : Prop :=
  orderOf z = 2 ∧ z ∈ K ∧ (∀ t ∈ K, orderOf t = 2 → t = z) ∧
    K ≤ Subgroup.centralizer ({z} : Set G) ∧
    (K.subgroupOf (Subgroup.centralizer ({z} : Set G))).Normal


theorem isPGroup_two_zpowers_of_orderOf_two {H : Type} [Group H] {b : H}
    (hb : orderOf b = 2) : IsPGroup 2 (Subgroup.zpowers b) :=
  IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hb]; norm_num)


section ZStar

variable [Finite G]

theorem exists_conj_mem_sylow_ne (hodd : CFSG.oddCore G = ⊥) (S : Sylow 2 G)
    (z : (S : Subgroup G)) (hzZ : z ∈ Subgroup.center (S : Subgroup G)) (hz : orderOf z = 2)
    (hnc : (z : G) ∉ Subgroup.center G) :
    ∃ g : G, g * (z : G) * g⁻¹ ∈ (S : Subgroup G) ∧ g * (z : G) * g⁻¹ ≠ (z : G) := by
  by_contra hne
  push Not at hne
  have hwc : ∀ g : G, g⁻¹ * (z : G) * g ∈ (S : Subgroup G) → g⁻¹ * (z : G) * g = z := by
    intro g hg
    have := hne g⁻¹
    rw [inv_inv] at this
    exact this hg
  obtain ⟨hfrat, -⟩ := CFSG.Adapters.glauberman_zStar S z hzZ hz hwc
  apply hnc
  rw [Subgroup.mem_center_iff]
  intro g
  obtain ⟨c, hc, k, hk, hgk⟩ := hfrat g
  rw [hodd, Subgroup.mem_bot] at hk
  subst hk
  rw [mul_one] at hgk
  subst hgk
  exact Subgroup.mem_centralizer_singleton_iff.mp hc

end ZStar

section Pair


end Pair

section Existence


end Existence

end CFSG.ClassicalInvolution
