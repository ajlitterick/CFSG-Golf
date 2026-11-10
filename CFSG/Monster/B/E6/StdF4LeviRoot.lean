module

public import CFSG.Monster.B.E6.StdF4LeviUnitary
public import CFSG.Monster.B.E6.StdF4Points
import all CFSG.Fischer.F4

public noncomputable section

namespace CFSG.Monster.B.E6.StdF4

open Module CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LieType.Chevalley.C2E6Std CFSG.LieType.Chevalley.C2E6Std.FieldExtension
open CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.Chevalley.ExteriorCube
open CFSG.Monster.B.Classical
open CFSG.LieType.Chevalley.C2E6Overlap (K)
open CFSG.Fischer (F4)
open CFSG.LinearGroups (frobeniusF4)
open CFSG.LieType.Universal.Unitary (SU)
open CFSG.Monster.B.Classical.UnitarySix (ProjSU IsoPt tPt rep₁ rep₂ rep₃ invRank SU_ext isoGraph)
open CFSG.Monster.B.TwoA.Unitary.Clique (su6Equiv su6Mat toSU6 coe_su6Equiv)

theorem repRootL_two : repRootL 2 = (Pi.single (i6 3) 1 : Fin Tag.E6.rank → ℤ) := by
  decide

theorem coe_repPoint_two :
    (repPoint 2 : ModGL Tag.E6 K) = xUnit Tag.E6 K (i6 3) 1 := by
  rw [coe_repPoint]
  apply Units.ext
  rw [E6Adjoint.pinnedX_eq (isRoot_repRootL 2), coe_xUnit, E6Adjoint.xOp_eq, repRootL_two]

theorem repPoint_two_mem_rootClass :
    repPoint 2 ∈ rootClass :=
  (mem_rootClass_iff _).2 ⟨_, rfl⟩

theorem finrank_range_sub_one_of_mem_rootClass
    {x : stdGroup} (hx : x ∈ rootClass) :
    finrank K (LinearMap.range
      (((x : ModGL Tag.E6 K) : Module.End K (RootModule Tag.E6 K)) - 1)) = 22 := by
  obtain ⟨c, rfl⟩ := isConj_iff.1 ((isConj_comm.1 repPoint_two_mem_rootClass).trans hx)
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, finrank_range_conj_sub_one,
    coe_repPoint_two, coe_xUnit]
  exact finrank_range_xOp_three

theorem stdLevi_firstJ_le_stdGroup :
    stdLevi firstJ ≤ stdGroup :=
  (stdLevi_le_nativeParabolic two_mem_firstJ).trans (nativeParabolic_le_stdGroup firstJ)

abbrev leviG :

    stdLevi firstJ →* stdGroup := Subgroup.inclusion stdLevi_firstJ_le_stdGroup

theorem leviG_injective :
    Function.Injective leviG := Subgroup.inclusion_injective _

abbrev rootLeviSet :
    Set stdGroup := {x | x ∈ rootClass ∧ (x : ModGL Tag.E6 K) ∈ stdLevi firstJ}

@[expose] def rootPt
    (p : IsoPt) : stdGroup := leviG (leviPSU.symm (tPt p))

theorem rootPt_injective :
    Function.Injective rootPt :=
  leviG_injective.comp (leviPSU.symm.injective.comp UnitarySix.tPt_injective)


theorem leviPSU_symm_rep₁ :
    leviPSU.symm (rep₁ : ProjSU) = leviOf rep₁ := by
  rw [MulEquiv.symm_apply_eq, leviPSU_leviOf]

theorem leviG_leviOf_rep₁ :
    leviG (leviOf rep₁) = repPoint 2 :=
  Subtype.ext (coe_leviOf_rep₁.trans coe_repPoint_two.symm)

theorem rep₁_mem_rankOneClass : (rep₁ : ProjSU) ∈ UnitarySix.rankOneClass :=
  ⟨rep₁, UnitarySix.rep₁_sq, UnitarySix.invRank_rep₁, rfl⟩

theorem rootPt_mem_rootLeviSet
    (p : IsoPt) : rootPt p ∈ rootLeviSet := by
  refine ⟨?_, (leviPSU.symm (tPt p)).2⟩
  have h1 : IsConj (rep₁ : ProjSU) (tPt p) := by
    have hp := UnitarySix.tPt_mem_rankOneClass p
    rw [UnitarySix.rankOneClass_eq_conj] at hp
    have hr := rep₁_mem_rankOneClass
    rw [UnitarySix.rankOneClass_eq_conj] at hr
    exact (isConj_comm.1 hr).trans hp
  obtain ⟨c, hc⟩ := isConj_iff.1 h1
  have h2 : IsConj (repPoint 2) (rootPt p) := by
    refine isConj_iff.2 ⟨leviG (leviPSU.symm c), ?_⟩
    rw [← leviG_leviOf_rep₁, ← leviPSU_symm_rep₁, ← map_inv, ← map_mul, ← map_mul,
      ← map_inv, ← map_mul, ← map_mul, hc]
    rfl
  exact repPoint_two_mem_rootClass.trans h2

theorem sq_of_mem_rootClass
    {x : stdGroup} (hx : x ∈ rootClass) : x ^ 2 = 1 := by
  obtain ⟨c, rfl⟩ := isConj_iff.1 hx
  rw [pow_two, show c * rootInv * c⁻¹ * (c * rootInv * c⁻¹) = c * (rootInv * rootInv) * c⁻¹ by
    group, rootInv_mul_self, mul_one, mul_inv_cancel]

theorem ne_one_of_mem_rootClass
    {x : stdGroup} (hx : x ∈ rootClass) : x ≠ 1 := by
  obtain ⟨c, rfl⟩ := isConj_iff.1 hx
  intro h
  apply rootInv_ne_one
  rw [mul_inv_eq_one, mul_eq_left] at h
  exact h

theorem exists_rootPt_of_mem
    {x : stdGroup} (hx : x ∈ rootLeviSet) : ∃ p, rootPt p = x := by
  obtain ⟨hxG, hxL⟩ := hx
  set l : stdLevi firstJ := ⟨x, hxL⟩
  have hl2 : leviPSU l ^ 2 = 1 := by
    rw [← map_pow]
    have : l ^ 2 = 1 := Subtype.ext (by
      change ((x ^ 2 : stdGroup) : ModGL Tag.E6 K) = 1
      rw [sq_of_mem_rootClass hxG]
      rfl)
    rw [this, map_one]
  have hl1 : leviPSU l ≠ 1 := by
    rw [Ne, MulEquiv.map_eq_one_iff]
    intro h
    exact ne_one_of_mem_rootClass hxG
      (Subtype.ext (congrArg (Subtype.val : stdLevi firstJ → ModGL Tag.E6 K) h))
  obtain ⟨A, ⟨hA, hA2⟩, -⟩ := UnitarySix.exists_unique_involution_lift _ hl2 hl1
  have hA1 : A ≠ 1 := by
    rintro rfl
    exact hl1 hA.symm
  have h22 := finrank_range_sub_one_of_mem_rootClass hxG
  have hk : invRank A = 1 := by
    rcases UnitarySix.invRank_eq_one_or_two_or_three A hA2 hA1 with h | h | h
    · exact h
    · have := finrank_range_sub_one_of_invRank_two hA2 hA1 hA.symm h
      change finrank K (LinearMap.range
        (((x : ModGL Tag.E6 K) : Module.End K (RootModule Tag.E6 K)) - 1)) = 32 at this
      omega
    · have := finrank_range_sub_one_of_invRank_three hA2 hA1 hA.symm h
      change finrank K (LinearMap.range
        (((x : ModGL Tag.E6 K) : Module.End K (RootModule Tag.E6 K)) - 1)) = 38 at this
      omega
  obtain ⟨p, hp⟩ : (A : ProjSU) ∈ Set.range tPt := by
    rw [UnitarySix.range_tPt]
    exact ⟨A, hA2, hk, rfl⟩
  refine ⟨p, ?_⟩
  rw [rootPt, hp, hA, MulEquiv.symm_apply_apply]
  rfl

theorem rootLeviSet_eq_range :
    rootLeviSet = Set.range rootPt := by
  ext x
  constructor
  · intro hx
    obtain ⟨p, rfl⟩ := exists_rootPt_of_mem hx
    exact ⟨p, rfl⟩
  · rintro ⟨p, rfl⟩
    exact rootPt_mem_rootLeviSet p


theorem betaSU_transvec (v : UnitarySix.V) (hv : UnitarySix.herm v v = 0) :
    UnitarySix.betaSU (UnitarySix.transvec v hv) =
      UnitarySix.transvec (UnitarySix.betaV v) (UnitarySix.herm_betaV_self_eq_zero hv) := by
  refine SU_ext ?_
  rw [UnitarySix.coe_betaSU, UnitarySix.coe_transvec, UnitarySix.coe_transvec]
  ext i j
  simp only [UnitarySix.betaM, UnitarySix.transvecMat, Matrix.map_apply, Matrix.add_apply,
    Matrix.vecMulVec_apply, UnitarySix.bar_add, UnitarySix.bar_mul, UnitarySix.betaV]
  congr 1
  rw [Matrix.one_apply]
  split_ifs <;> simp

theorem tPt_betaPt (p : IsoPt) : tPt (UnitarySix.betaPt p) = UnitarySix.betaL (tPt p) := by
  induction p using UnitarySix.IsoPt.ind with
  | h v hv0 hv =>
    rw [UnitarySix.betaPt_pt, UnitarySix.tPt_pt, UnitarySix.tPt_pt, UnitarySix.betaL_mk,
      betaSU_transvec]

theorem leviPSU_symm_betaL
    (y : ProjSU) :
    leviPSU.symm (UnitarySix.betaL y) = betaLevi (leviPSU.symm y) := by
  rw [MulEquiv.symm_apply_eq, leviPSU_betaLevi, MulEquiv.apply_symm_apply]

theorem rootPt_projAct
    (l : stdLevi firstJ) (p : IsoPt) :
    rootPt (UnitarySix.projAct (leviPSU l) p) = leviG l * rootPt p * (leviG l)⁻¹ := by
  have e : leviPSU.symm (leviPSU l * tPt p * (leviPSU l)⁻¹) =
      l * leviPSU.symm (tPt p) * l⁻¹ := by
    rw [map_mul, map_mul, map_inv, MulEquiv.symm_apply_apply]
  rw [rootPt, UnitarySix.tPt_projAct, e, map_mul, map_mul, map_inv]
  rfl

theorem rootPt_betaPt
    (p : IsoPt) : rootPt (UnitarySix.betaPt p) = betaG (rootPt p) := by
  rw [rootPt, tPt_betaPt, leviPSU_symm_betaL]
  rfl

theorem extAct_leviStarHom
    (γ : leviStar) (p : IsoPt) :
    UnitarySix.extAct (leviStarHom γ) p =
      UnitarySix.projAct (leviPSU ⟨_, γ.2⟩)
        (UnitarySix.betaPermHom (betaIdx (γ : GStar).right) p) := by
  have e : leviStarHom γ = SemidirectProduct.inl (leviPSU ⟨_, γ.2⟩) *
      SemidirectProduct.inr (betaIdx (γ : GStar).right) :=
    SemidirectProduct.ext (by simp [leviStarHom_left]) (by simp [leviStarHom_right])
  rw [e, map_mul, UnitarySix.extAct_inl, UnitarySix.extAct_inr]
  rfl

theorem rootPt_betaPermHom
    (b : betaGroup) (p : IsoPt) :
    rootPt (UnitarySix.betaPermHom (betaIdx b) p) = (b : MulAut stdGroup) (rootPt p) := by
  rcases mem_betaGroup_iff.mp b.2 with hb | hb
  · rw [betaIdx_of_eq_one hb, map_one, hb]
    rfl
  · rw [betaIdx_of_eq_betaG hb, hb]
    have : UnitarySix.betaPermHom (Multiplicative.ofAdd 1) = UnitarySix.betaPerm := by
      simp [UnitarySix.betaPermHom, show ¬((1 : ZMod 2) = 0) by decide]
    rw [this]
    exact rootPt_betaPt p

theorem conj_rootPt
    (γ : leviStar) (p : IsoPt) :
    (γ : GStar) * SemidirectProduct.inl (rootPt p) * (γ : GStar)⁻¹ =
      SemidirectProduct.inl (rootPt (UnitarySix.extAct (leviStarEquiv γ) p)) := by
  rw [conj_inl, leviStarEquiv_apply, extAct_leviStarHom, rootPt_projAct, rootPt_betaPermHom]
  rfl

theorem adj_iff_commute_rootPt
    (p q : IsoPt) :
    isoGraph.Adj p q ↔ p ≠ q ∧ Commute (rootPt p) (rootPt q) := by
  rw [UnitarySix.adj_iff_commute]
  refine and_congr_right fun _ => ?_
  have hinj : Function.Injective (leviG.comp leviPSU.symm.toMonoidHom) :=
    leviG_injective.comp leviPSU.symm.injective
  constructor
  · intro h
    exact h.map (leviG.comp leviPSU.symm.toMonoidHom)
  · intro h
    have e := h.eq
    change (leviG.comp leviPSU.symm.toMonoidHom) (tPt p) *
        (leviG.comp leviPSU.symm.toMonoidHom) (tPt q) =
      (leviG.comp leviPSU.symm.toMonoidHom) (tPt q) *
        (leviG.comp leviPSU.symm.toMonoidHom) (tPt p) at e
    rw [← map_mul, ← map_mul] at e
    exact hinj e


end CFSG.Monster.B.E6.StdF4
