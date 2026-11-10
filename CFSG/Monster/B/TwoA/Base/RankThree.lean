
module

public import CFSG.Monster.B.TwoA.Base.RankThreeBase

public import CFSG.Monster.B.TwoA.Base.Plane

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.B.Short
  CFSG.Monster.B CFSG.Monster.VisQuot CFSG.Monster.ScalarKernel CFSG.Monster.B.Co2
  CFSG.Monster.Lifts CFSG.Monster.VisCert

theorem NU_transitive :

    ∀ y ∈ Uplane, y ≠ 0 → ∃ k ∈ wSetStab Uplane, wAct v0 k wFr = y := by
  intro y hy hy0
  rcases (mem_Uplane_iff y).1 hy with rfl | rfl | rfl | rfl
  · exact absurd rfl hy0
  · exact ⟨1, (wSetStab Uplane).one_mem, by rw [wAct_one, Module.End.one_apply]⟩
  · refine ⟨alpha23K * sgnK, (wSetStab Uplane).mul_mem alpha23K_mem_NU sgnK_mem_NU, ?_⟩
    rw [wAct_mul, Module.End.mul_apply, alpha23K_wFr, map_add, sgnK_wFr, sgnK_sW, ← add_assoc,
      two_smul_W, zero_add]
  · exact ⟨alpha23K, alpha23K_mem_NU, alpha23K_wFr⟩

theorem natCard_H3 :
    Nat.card H3 = 98956046499840 := by
  rw [H3_eq, natCard_HU, show wSetStab Uplane = NU from rfl, natCard_NU]
  norm_num

theorem K3_eq_closure :
    K3 = Subgroup.closure (insert tauhat (H3 : Set Dfull)) := by
  rw [K3_eq, H3_eq]
  exact KU_eq_closure tauhat_mem_normalizer_EU NU_transitive

theorem K3_le_Shat :
    K3 ≤ Shat := by
  rw [K3_eq]
  exact KU_le_Shat tauhat_mem_normalizer_EU NU_transitive


theorem natCard_K3 :
    Nat.card K3 = 692692325498880 := by
  have h := natCard_KU tauhat_mem_normalizer_EU NU_transitive
  rw [← K3_eq, ← E3_eq_EU, ← H3_eq, natCard_E3, natCard_H3] at h
  rw [h]

theorem conjE_E3_surjective :
    Function.Surjective (conjE E3) := by
  refine conjE_surjective_of_card ?_
  change Nat.card K3 = Nat.card (MulAut E3) * Nat.card C3
  rw [natCard_K3, natCard_mulAut_E3, natCard_C3]

theorem actE3_surjective :
    Function.Surjective actE3 := by
  rw [actE3, MonoidHom.coe_comp]
  exact (MulEquiv.surjective _).comp conjE_E3_surjective


attribute [local instance] vAction

attribute [local instance] l3Action


end CFSG.Monster.B.TwoA
