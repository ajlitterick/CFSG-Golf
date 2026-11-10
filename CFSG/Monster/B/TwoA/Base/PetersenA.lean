
module

public import CFSG.Monster.B.TwoA.Base.PetersenABase

public import CFSG.Monster.B.TwoA.Base.Par45B

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.B.Short
  CFSG.Monster.B CFSG.Monster.VisQuot CFSG.Monster.ScalarKernel CFSG.Monster.B.Co2
  CFSG.Monster.Lifts CFSG.Monster.VisCert

open scoped IsMulCommutative

theorem flats_eq_orbit
    {E : Subgroup Dfull} [CFSG.IsElementaryAbelian 2 E]
    (hsurj : Function.Surjective (conjE E)) (h3 : E3 ≤ E) :
    {F : Subgroup Dfull | (∃ g ∈ Shat, F = conjSub g E) ∧ E3 ≤ F} =
      {F | ∃ k ∈ K3, F = conjSub k E} := by
  ext F
  constructor
  · rintro ⟨⟨g, -, rfl⟩, hF⟩
    obtain ⟨h, hh, he⟩ := exists_normalizer_conjSub_eq hsurj h3 hF
    exact ⟨h, hh, he⟩
  · rintro ⟨k, hk, rfl⟩
    refine ⟨⟨k, K3_le_Shat hk, rfl⟩, ?_⟩
    have h1 := conjSub_mono (g := k) h3
    rwa [conjSub_eq_self_iff.2 hk] at h1

theorem X4_eq :
    X4 = {F | ∃ k ∈ K3, F = conjSub k E4} :=
  flats_eq_orbit conjE_E4_surjective E3_le_E4

theorem X5_eq :
    X5 = {F | ∃ k ∈ K3, F = conjSub k E5} :=
  flats_eq_orbit conjE_E5_surjective (E3_le_E4.trans E4_le_E5)


theorem natCard_K3_inf_K4 :
    Nat.card ↥(K3 ⊓ K4) = 46179488366592 := by
  have h := (chain_flags 3 4 (by norm_num) (by norm_num) (by norm_num)).2
  rw [natCard_subspaceDim_fin (by norm_num), show qBinom 2 4 3 = 15 by decide] at h
  have h1 := ((K3 ⊓ K4).subgroupOf K4).card_mul_index
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : K3 ⊓ K4 ≤ K4)).toEquiv,
    natCard_K4] at h1
  have h2 : Nat.card ↥(K3 ⊓ K4) * 15 = 692692325498880 := (congrArg _ h.symm).trans h1
  omega

theorem natCard_K3_inf_K5 :
    Nat.card ↥(K3 ⊓ K5) = 69269232549888 := by
  have h := (chain_flags 3 5 (by norm_num) (by norm_num) (by norm_num)).2
  rw [natCard_subspaceDim_fin (by norm_num), show qBinom 2 5 3 = 155 by decide] at h
  have h1 := ((K3 ⊓ K5).subgroupOf K5).card_mul_index
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : K3 ⊓ K5 ≤ K5)).toEquiv,
    natCard_K5] at h1
  have h2 : Nat.card ↥(K3 ⊓ K5) * 155 = 10736731045232640 := (congrArg _ h.symm).trans h1
  omega

theorem natCard_X4 :
    Nat.card X4 = 15 := by
  rw [Nat.card_coe_set_eq, X4_eq, ncard_conjSub_orbit, subgroupOf_K3_eq]
  exact index_eq_of_natCard inf_le_left natCard_K3_inf_K4 natCard_K3 (by norm_num) (by norm_num)

theorem natCard_X5 :
    Nat.card X5 = 10 := by
  rw [Nat.card_coe_set_eq, X5_eq, ncard_conjSub_orbit, subgroupOf_K3_eq]
  exact index_eq_of_natCard inf_le_left natCard_K3_inf_K5 natCard_K3 (by norm_num) (by norm_num)


end CFSG.Monster.B.TwoA
