
module

public import CFSG.Monster.B.TwoA.Base.Par45ABase

public import CFSG.Monster.B.TwoA.Base.Space34C

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.B.Short
  CFSG.Monster.B CFSG.Monster.VisQuot CFSG.Monster.ScalarKernel CFSG.Monster.B.Co2
  CFSG.Monster.Lifts CFSG.Monster.VisCert

theorem qV_U3 :
    ∀ x ∈ U3, qV x = 0 := pairSpace_U3.qV_eq_zero

theorem qV_U4 :
    ∀ x ∈ U4, qV x = 0 := pairSpace_U4.qV_eq_zero

theorem Uplane_le_U3 :
    Uplane ≤ U3 := by
  rw [Uplane, Submodule.span_le]
  rintro _ (rfl | rfl)
  · exact pairSpace_U3.wFr_mem
  · exact (Submodule.subset_span ⟨1, rfl⟩ : gen3 1 ∈ U3)

theorem E4_eq_EU :
    E4 = EU U3 := by
  apply le_antisymm
  · rw [E4, Subgroup.closure_le]
    rintro x (rfl | h)
    · exact mem_EU_of (e := dhatE 4 5) (by
        rw [psiW_d45]
        exact (Submodule.subset_span ⟨2, rfl⟩ : gen3 2 ∈ U3))
    · have h' : x ∈ EU Uplane := by
        rw [← E3_eq_EU]
        exact h
      exact EU_mono Uplane_le_U3 h'
  · refine EU_span_le xhat_mem_E4 fun i => ?_
    fin_cases i
    · exact ⟨yhatE, psiW_yhat, E3_le_E4 yhat_mem_E3⟩
    · exact ⟨zhatE, psiW_zhat, E3_le_E4 zhat_mem_E3⟩
    · exact ⟨dhatE 4 5, psiW_d45, d45_mem_E4⟩

theorem E5_eq_EU :
    E5 = EU U4 := by
  apply le_antisymm
  · rw [E5, Subgroup.closure_le]
    rintro x (rfl | h)
    · exact mem_EU_of (e := dhatE 8 9) (by
        rw [psiW_d89]
        exact (Submodule.subset_span ⟨3, rfl⟩ : gen4 3 ∈ U4))
    · have h' : x ∈ EU U3 := by
        rw [← E4_eq_EU]
        exact h
      exact EU_mono U3_le_U4 h'
  · refine EU_span_le xhat_mem_E5 fun i => ?_
    fin_cases i
    · exact ⟨yhatE, psiW_yhat, E4_le_E5 (E3_le_E4 yhat_mem_E3)⟩
    · exact ⟨zhatE, psiW_zhat, E4_le_E5 (E3_le_E4 zhat_mem_E3)⟩
    · exact ⟨dhatE 4 5, psiW_d45, E4_le_E5 d45_mem_E4⟩
    · exact ⟨dhatE 8 9, psiW_d89, d89_mem_E5⟩

instance isElementaryAbelian_E4 :
    CFSG.IsElementaryAbelian 2 E4 := by
  rw [E4_eq_EU]
  exact isElementaryAbelian_EU qV_U3

instance isElementaryAbelian_E5 :
    CFSG.IsElementaryAbelian 2 E5 := by
  rw [E5_eq_EU]
  exact isElementaryAbelian_EU qV_U4

theorem natCard_E4 :
    Nat.card E4 = 2 ^ 4 := by
  rw [E4_eq_EU, natCard_EU, natCard_U3]
  norm_num

theorem natCard_E5 :
    Nat.card E5 = 2 ^ 5 := by
  rw [E5_eq_EU, natCard_EU, natCard_U4]
  norm_num

theorem tauhat_mem_normalizer_EU3 :
    tauhat ∈ Subgroup.normalizer (EU U3 : Set Dfull) := by
  rw [← E4_eq_EU]
  exact tauhat_mem_normalizer_E4

theorem tauhat_mem_normalizer_EU4 :
    tauhat ∈ Subgroup.normalizer (EU U4 : Set Dfull) := by
  rw [← E5_eq_EU]
  exact tauhat_mem_normalizer_E5

theorem H4_eq :
    H4 = HU U3 :=
  congrArg (fun E : Subgroup Dfull => Jhat ⊓ Subgroup.normalizer (E : Set Dfull)) E4_eq_EU

theorem K4_eq :
    K4 = KU U3 :=
  congrArg (fun E : Subgroup Dfull => Subgroup.normalizer (E : Set Dfull)) E4_eq_EU

theorem Z4_eq :
    Z4 = ZU U3 :=
  congrArg (fun E : Subgroup Dfull => Subgroup.centralizer (E : Set Dfull)) E4_eq_EU

theorem H5_eq :
    H5 = HU U4 :=
  congrArg (fun E : Subgroup Dfull => Jhat ⊓ Subgroup.normalizer (E : Set Dfull)) E5_eq_EU

theorem K5_eq :
    K5 = KU U4 :=
  congrArg (fun E : Subgroup Dfull => Subgroup.normalizer (E : Set Dfull)) E5_eq_EU

theorem Z5_eq :
    Z5 = ZU U4 :=
  congrArg (fun E : Subgroup Dfull => Subgroup.centralizer (E : Set Dfull)) E5_eq_EU


theorem natCard_H4 :
    Nat.card H4 = 2 ^ 23 * 5505024 := by
  rw [H4_eq, natCard_HU, natCard_N3]

theorem natCard_H5 :
    Nat.card H5 = 2 ^ 23 * 41287680 := by
  rw [H5_eq, natCard_HU, natCard_N4]


theorem natCard_K4 :
    Nat.card K4 = 692692325498880 := by
  have h := natCard_KU tauhat_mem_normalizer_EU3 N3_transitive
  rw [← K4_eq, ← E4_eq_EU, ← H4_eq, natCard_E4, natCard_H4] at h
  exact h.trans (by norm_num)

theorem natCard_K5 :
    Nat.card K5 = 10736731045232640 := by
  have h := natCard_KU tauhat_mem_normalizer_EU4 N4_transitive
  rw [← K5_eq, ← E5_eq_EU, ← H5_eq, natCard_E5, natCard_H5] at h
  exact h.trans (by norm_num)


theorem natCard_Z4 :
    Nat.card Z4 = 2 ^ 35 := by
  rw [Z4_eq, natCard_ZU, finrank_U3, natCard_CU3]
  norm_num

theorem natCard_Z5 :
    Nat.card Z5 = 2 ^ 30 := by
  rw [Z5_eq, natCard_ZU, finrank_U4, natCard_CU4]
  norm_num

theorem natCard_mulAut_E4 :
    Nat.card (MulAut E4) = 20160 := by
  rw [Nat.card_congr (mulAutEquivGL natCard_E4).toEquiv, natCard_GL_four]

theorem natCard_mulAut_E5 :
    Nat.card (MulAut E5) = 9999360 := by
  rw [Nat.card_congr (mulAutEquivGL natCard_E5).toEquiv, natCard_GL_five]

theorem conjE_E4_surjective :
    Function.Surjective (conjE E4) := by
  refine conjE_surjective_of_card ?_
  change Nat.card K4 = Nat.card (MulAut E4) * Nat.card Z4
  rw [natCard_K4, natCard_mulAut_E4, natCard_Z4]
  norm_num

theorem conjE_E5_surjective :
    Function.Surjective (conjE E5) := by
  refine conjE_surjective_of_card ?_
  change Nat.card K5 = Nat.card (MulAut E5) * Nat.card Z5
  rw [natCard_K5, natCard_mulAut_E5, natCard_Z5]
  norm_num

@[expose] def actE4 :
    K4 →* GL (Fin 4) (ZMod 2) :=
  (mulAutEquivGL natCard_E4).toMonoidHom.comp (conjE E4)

@[expose] def actE5 :
    K5 →* GL (Fin 5) (ZMod 2) :=
  (mulAutEquivGL natCard_E5).toMonoidHom.comp (conjE E5)


theorem ker_actE4 :
    actE4.ker = Z4.subgroupOf K4 := by
  ext g
  rw [MonoidHom.mem_ker, actE4, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.map_eq_one_iff, ← MonoidHom.mem_ker, ker_conjE]
  rfl

theorem ker_actE5 :
    actE5.ker = Z5.subgroupOf K5 := by
  ext g
  rw [MonoidHom.mem_ker, actE5, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.map_eq_one_iff, ← MonoidHom.mem_ker, ker_conjE]
  rfl

instance Z4_subgroupOf_normal :
    (Z4.subgroupOf K4).Normal := ker_actE4 ▸ actE4.normal_ker

instance Z5_subgroupOf_normal :
    (Z5.subgroupOf K5).Normal := ker_actE5 ▸ actE5.normal_ker


end CFSG.Monster.B.TwoA
