
module

public import CFSG.Monster.B.TwoA.Base.EU
public import CFSG.Monster.B.TwoA.Base.PlaneBase

@[expose] public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.B.Short
  CFSG.Monster.B CFSG.Monster.VisQuot CFSG.Monster.ScalarKernel CFSG.Monster.B.Co2
  CFSG.Monster.Lifts CFSG.Monster.VisCert

theorem sum_pairVec (x y : Fin 24) (b : ZMod 2) : ∑ i, pairVec x y b i = 4 - sgnI b * 4 := by
  simp [pairVec_apply, Finset.sum_sub_distrib]

theorem qL_twoΩCls : qL twoΩCls = 0 := by
  rw [twoΩCls, qL_cls]
  decide +kernel

theorem bL_twoΩCls_pairCls {x y : Fin 24} (hxy : x ≠ y) (b : ZMod 2) :
    bL twoΩCls (pairCls x y b) = 0 := by
  rw [pairCls, Griess.classOf_eq_cls (pairVec_mem hxy b).1, twoΩCls, bL, bL_cls, hInt]
  have h : ∑ i, Visible.twoΩ i * pairVec x y b i = 8 - sgnI b * 8 := by
    simp only [Visible.twoΩ_apply, ← Finset.mul_sum, sum_pairVec]
    ring
  rw [h]
  rcases sgnI_eq_one_or b with hb | hb <;> rw [hb] <;> decide

theorem qV_wFr :
    qV wFr = 0 := qL_twoΩCls

theorem qV_pairW
    {x y : Fin 24} (h : OffPair x y) (b : ZMod 2) : qV (pairW x y h b) = 0 :=
  Griess.qL_classOf_minVecs (pairVec_mem h.ne b)

theorem bV_wFr_pairW
    {x y : Fin 24} (h : OffPair x y) (b : ZMod 2) :
    bV wFr (pairW x y h b) = 0 := by
  rw [wFr, pairW, polarBilin_qW_mk]
  exact bL_twoΩCls_pairCls h.ne b

theorem qV_Uplane :
    ∀ x ∈ Uplane, qV x = 0 := by
  intro x hx
  rcases (mem_Uplane_iff x).1 hx with rfl | rfl | rfl | rfl
  · exact QuadraticMap.map_zero _
  · exact qV_wFr
  · exact qV_pairW offPair23 0
  · rw [qV_add, qV_wFr, show qV sW = 0 from qV_pairW offPair23 0,
      show bV wFr sW = 0 from bV_wFr_pairW offPair23 0, add_zero, add_zero]

@[expose] def zhat : Dfull := dhat 2 3

@[expose] def zhatE : Ehat := dhatE 2 3

theorem psiW_zhat :
    psiW zhatE = sW := psiW_dhat (by decide) offPair23

@[expose] def E3 : Subgroup Dfull := Subgroup.closure {xhat, yhat, zhat}

theorem mem_closure_of_fiber
    {S : Set Dfull} {d p : Ehat} (h : psiW d = psiW p)
    (hp : (p : Dfull) ∈ Subgroup.closure S) (hx : xhat ∈ Subgroup.closure S) :
    (d : Dfull) ∈ Subgroup.closure S := by
  rcases fiber_cases h with h1 | h1
  · rw [h1]; exact hp
  · rw [h1]; exact Subgroup.mul_mem _ hp hx

theorem E3_eq_EU :
    E3 = EU Uplane := by
  have hx : xhat ∈ E3 := Subgroup.subset_closure (by simp)
  have hy : yhat ∈ E3 := Subgroup.subset_closure (by simp)
  have hz : zhat ∈ E3 := Subgroup.subset_closure (by simp)
  apply le_antisymm
  · rw [E3, Subgroup.closure_le]
    rintro _ (rfl | rfl | rfl)
    · exact xhat_mem_EU
    · exact mem_EU_of (e := yhatE) (by rw [psiW_yhat]; exact wFr_mem_Uplane)
    · exact mem_EU_of (e := zhatE) (by rw [psiW_zhat]; exact sW_mem_Uplane)
  · intro d hd
    obtain ⟨hd', hdU⟩ := mem_EU.1 hd
    rcases (mem_Uplane_iff _).1 hdU with h | h | h | h
    · exact mem_closure_of_fiber (p := 1) (by rw [h, psiW_one]) (Subgroup.one_mem _) hx
    · exact mem_closure_of_fiber (p := yhatE) (by rw [h, psiW_yhat]) hy hx
    · exact mem_closure_of_fiber (p := zhatE) (by rw [h, psiW_zhat]) hz hx
    · exact mem_closure_of_fiber (p := yhatE * zhatE) (by rw [h, psiW_mul, psiW_yhat, psiW_zhat])
        (Subgroup.mul_mem _ hy hz) hx

instance isElementaryAbelian_E3 :
    CFSG.IsElementaryAbelian 2 E3 := by
  rw [E3_eq_EU]
  exact isElementaryAbelian_EU qV_Uplane

theorem natCard_Uplane :
    Nat.card Uplane = 4 := by
  rw [natCard_submodule, finrank_Uplane]
  rfl

theorem natCard_E3 :
    Nat.card E3 = 8 := by
  rw [E3_eq_EU, natCard_EU, natCard_Uplane]

theorem Vhat_le_E3 : Vhat ≤ E3 := by
  intro d hd
  have hx : xhat ∈ E3 := Subgroup.subset_closure (by simp)
  have hy : yhat ∈ E3 := Subgroup.subset_closure (by simp)
  rcases (mem_Vhat_iff d).1 hd with rfl | rfl | rfl | rfl
  · exact E3.one_mem
  · exact hx
  · exact E3.mul_mem hx hy
  · exact hy

theorem tauhat_conj_yhat : tauhat * yhat * tauhat⁻¹ = xhat := congrArg Subtype.val tauN_vZ

theorem tauhat_conj_zhat : tauhat * zhat * tauhat⁻¹ = zhat := by
  rw [zhat, tauhat_mul_dhat, mul_inv_cancel_right]

theorem tauhat_mem_normalizer_E3 : tauhat ∈ Subgroup.normalizer (E3 : Set Dfull) := by
  refine mem_normalizer_of_closure ?_
  have hx : xhat ∈ E3 := Subgroup.subset_closure (by simp)
  have hy : yhat ∈ E3 := Subgroup.subset_closure (by simp)
  have hz : zhat ∈ E3 := Subgroup.subset_closure (by simp)
  rintro _ (rfl | rfl | rfl)
  · rw [tauhat_conj_xhat, ← xhat_mul_yhat]
    exact E3.mul_mem hx hy
  · rw [tauhat_conj_yhat]
    exact hx
  · rw [tauhat_conj_zhat]
    exact hz

@[expose] def H3 : Subgroup Dfull := Jhat ⊓ Subgroup.normalizer (E3 : Set Dfull)

abbrev K3 : Subgroup Dfull := Subgroup.normalizer (E3 : Set Dfull)

@[expose] def C3 : Subgroup Dfull := Subgroup.centralizer (E3 : Set Dfull)

theorem H3_eq :
    H3 = HU Uplane :=
  congrArg (fun E : Subgroup Dfull => Jhat ⊓ Subgroup.normalizer (E : Set Dfull)) E3_eq_EU

theorem K3_eq :
    K3 = KU Uplane :=
  congrArg (fun E : Subgroup Dfull => Subgroup.normalizer (E : Set Dfull)) E3_eq_EU

theorem C3_eq :
    C3 = ZU Uplane :=
  congrArg (fun E : Subgroup Dfull => Subgroup.centralizer (E : Set Dfull)) E3_eq_EU

theorem H3_le_Jhat : H3 ≤ Jhat := inf_le_left

theorem tauhat_mem_normalizer_EU :
    tauhat ∈ Subgroup.normalizer (EU Uplane : Set Dfull) := by
  rw [← E3_eq_EU]
  exact tauhat_mem_normalizer_E3

theorem H3_subgroupOf_eq :
    H3.subgroupOf Jhat = NU.comap jhatToKv0 := by
  rw [H3_eq, HU_subgroupOf_eq]
  rfl


theorem C3_le_K3 : C3 ≤ K3 := Subgroup.centralizer_le_normalizer _

theorem C3_le_Jhat :
    C3 ≤ Jhat := by
  rw [C3_eq]
  exact ZU_le_Jhat

@[expose] def c3Proj :
    C3 →* CU :=
  (zuProj Uplane).comp (MulEquiv.subgroupCongr C3_eq).toMonoidHom


theorem c3Proj_surjective :
    Function.Surjective c3Proj :=
  zuProj_surjective.comp (MulEquiv.surjective _)

theorem ker_c3Proj :
    c3Proj.ker = (Ehat ⊓ C3).subgroupOf C3 := by
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  constructor
  · intro h
    have h1 : jhatToKv0 ⟨g, C3_le_Jhat g.2⟩ = 1 := congrArg Subtype.val h
    rw [← MonoidHom.mem_ker, ker_jhatToKv0, Subgroup.mem_subgroupOf] at h1
    exact ⟨h1, g.2⟩
  · intro h
    exact Subtype.ext (jhatToKv0_eq_one_of_mem_Ehat _ h.1)

theorem natCard_Ehat_inf_C3 :
    Nat.card ↥(Ehat ⊓ C3) = 2 ^ 21 := by
  have h : Nat.card ↥(Ehat ⊓ ZU Uplane) = 2 * 2 ^ (22 - Module.finrank (ZMod 2) Uplane) :=
    natCard_Ehat_inf_centralizer_EU
  rw [C3_eq, h, finrank_Uplane]
  norm_num

theorem natCard_C3 :
    Nat.card C3 = 4123168604160 := by
  rw [C3_eq, natCard_ZU, finrank_Uplane, show wFix (Uplane : Set (Wv v0)) = CU from rfl,
    natCard_CU]
  norm_num

theorem natCard_E3_pow :
    Nat.card E3 = 2 ^ 3 := natCard_E3

theorem natCard_mulAut_E3 :
    Nat.card (MulAut E3) = 168 := by
  rw [Nat.card_congr (mulAutEquivGL natCard_E3_pow).toEquiv, natCard_GL_three]

@[expose] def actE3 :
    K3 →* GL (Fin 3) (ZMod 2) :=
  (mulAutEquivGL natCard_E3_pow).toMonoidHom.comp (conjE E3)

theorem ker_actE3 :
    actE3.ker = C3.subgroupOf K3 := by
  ext g
  rw [MonoidHom.mem_ker, actE3, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.map_eq_one_iff, ← MonoidHom.mem_ker, ker_conjE]
  rfl

instance C3_subgroupOf_normal :
    (C3.subgroupOf K3).Normal := ker_actE3 ▸ actE3.normal_ker

theorem xhat_mem_E3 : xhat ∈ E3 := Subgroup.subset_closure (by simp)


attribute [local instance] vAction

@[expose] def l3ToNtwo : ↥(K3 ⊓ Ntwo) →* Ntwo := Subgroup.inclusion inf_le_right

@[expose, instance_reducible] noncomputable def l3Action : MulAction ↥(K3 ⊓ Ntwo) Vsharp :=
  MulAction.compHom _ l3ToNtwo

attribute [local instance] l3Action

theorem tauhat_mem_K3 :
    tauhat ∈ K3 := tauhat_mem_normalizer_E3

@[expose] def tauL :
    ↥(K3 ⊓ Ntwo) := ⟨tauhat, tauhat_mem_K3, tauhat_mem_Ntwo⟩


end CFSG.Monster.B.TwoA
