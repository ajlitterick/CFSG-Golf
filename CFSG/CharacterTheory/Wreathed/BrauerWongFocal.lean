module

public import CFSG.CharacterTheory.Wreathed.QuaternionFocal
public import CFSG.CharacterTheory.Wreathed.SimpleFusion

public noncomputable section

namespace CFSG.Wreathed.BrauerWong

open CFSG.Wreathed

universe u v


variable {G : Type u} [Group G]

theorem isMulCommutative_of_le_modelBase {m : ℕ} (S : Sylow 2 G) (e : S ≃* Wreath m)
    {H : Subgroup G} (hH : H ≤ modelBase S e) : IsMulCommutative H := by
  rw [isMulCommutative_iff]
  intro x y
  obtain ⟨u, hu, hux⟩ := hH x.property
  obtain ⟨w, hw, hwy⟩ := hH y.property
  apply Subtype.ext
  change (x : G) * y = y * x
  rw [← hux, ← hwy, ← map_mul, ← map_mul]
  congr 1
  exact congrArg Subtype.val
    (isMulCommutative_iff.mp (base_is_abelian m) ⟨u, hu⟩ ⟨w, hw⟩)

variable [Finite G]

theorem transferFocal_ker_spec (S : Sylow 2 G) :
    ((S : Subgroup G).transferFocal.ker).Normal ∧
      (∃ k : ℕ, ((S : Subgroup G).transferFocal.ker).index = 2 ^ k) ∧
      (S : Subgroup G) ⊓ (S : Subgroup G).transferFocal.ker = (S : Subgroup G).focalSubgroup ∧
      ((S : Subgroup G).transferFocal.ker).index * Nat.card (S : Subgroup G).focalSubgroup =
        Nat.card (S : Subgroup G) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hidx : ((S : Subgroup G).transferFocal.ker).index =
      Nat.card (↥(S : Subgroup G) ⧸ (S : Subgroup G).focalSubgroupOf) := by
    rw [Subgroup.index_eq_card]
    exact Nat.card_congr
      (Subgroup.transferFocal.quotientKerMulEquivQuotientFocalSubroupOf S).toEquiv
  have hcardF : Nat.card (S : Subgroup G).focalSubgroupOf =
      Nat.card (S : Subgroup G).focalSubgroup :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (S : Subgroup G).focalSubgroup_le).toEquiv
  refine ⟨MonoidHom.normal_ker _, ?_, ?_, ?_⟩
  · rw [hidx]
    exact (S.isPGroup'.to_quotient _).exists_card_eq
  · rw [inf_comm]
    exact Subgroup.ker_transferFocal_inf_eq_focalSubgroup S
  · rw [hidx, ← hcardF]
    exact (Subgroup.card_eq_card_quotient_mul_card_subgroup _).symm


theorem mem_of_odd_of_two_power_index {X : Type v} [Group X] [Finite X] (K : Subgroup X)
    [K.Normal] (hK : ∃ k : ℕ, K.index = 2 ^ k) (h : X) (hodd : Odd (orderOf h)) : h ∈ K := by
  obtain ⟨k, hk⟩ := hK
  rw [← QuotientGroup.eq_one_iff]
  have hdvd₁ : orderOf (QuotientGroup.mk' K h) ∣ orderOf h := orderOf_map_dvd _ _
  have hdvd₂ : orderOf (QuotientGroup.mk' K h) ∣ 2 ^ k := by
    rw [← hk, Subgroup.index_eq_card]
    exact orderOf_dvd_natCard _
  have hcop : Nat.Coprime (orderOf h) (2 ^ k) :=
    Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hodd)
  have hone : orderOf (QuotientGroup.mk' K h) = 1 :=
    Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hdvd₁ hcop) hdvd₂
  exact orderOf_eq_one_iff.mp hone


end CFSG.Wreathed.BrauerWong
