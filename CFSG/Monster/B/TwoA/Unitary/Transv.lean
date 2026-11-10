module

public import CFSG.Monster.B.TwoA.Unitary.TransvMat
public import CFSG.Monster.B.TwoA.Unitary.TransvFix
public import CFSG.Monster.B.TwoA.Unitary.Orbit1408Planes
public meta import CFSG.Monster.B.TwoA.Unitary.Orbit1408Points
public meta import CFSG.Monster.B.TwoA.Unitary.Orbit1408Data
public import Certificates.Certificate3125
import all CFSG.Fischer.F4
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.Monster.B.Classical.PlaneAut
public import CFSG.Monster.B.TwoA.Amalgam.Flag1Native
public import CFSG.Monster.B.TwoA.Base.GeomNative
public import CFSG.Monster.B.TwoA.Par3.MainBase
public import CFSG.Monster.B.TwoA.Sp8.GenActionBase
public import CFSG.Monster.B.TwoA.Sp8.NormalizerBase
public import CFSG.Monster.B.TwoA.Sp8.Orth8
public import CFSG.Monster.B.TwoA.Sp8.Orth8Base
public import CFSG.Monster.B.TwoA.Sp8.SubgeomBuildingBase
public import CFSG.Monster.B.TwoA.Sp8.SubgeomFive
public import CFSG.Monster.B.TwoA.Sp8.SubgeomFiveBase
public import CFSG.Monster.B.TwoA.Sp8.SubgeomIsoBase
public import CFSG.Monster.B.TwoA.Sp8.SubgeomStdBase

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Unitary

open CFSG.Fischer CFSG.Monster CFSG.Monster.B.Short CFSG.Monster.B.Co2 CFSG.Monster.B.TwoA
  Matrix Module
open CFSG.Monster.B.TwoA.Amalgam (e6 Rsp)

theorem wAct_conj (u t : Kstab v0) (x : Wv v0) :
    wAct v0 (u⁻¹ * t * u) x = wAct v0 u (wAct v0 t (wAct v0 u⁻¹ x)) := by
  rw [wAct_mul, wAct_mul, Module.End.mul_apply, Module.End.mul_apply]

@[expose] def wActEquiv (u : Kstab v0) : Wv v0 ≃ₗ[ZMod 2] Wv v0 :=
  LinearEquiv.ofLinearMap (wAct v0 u) (wAct v0 u⁻¹) (LinearMap.ext fun x => wAct_apply_inv u x)
    (LinearMap.ext fun x => wAct_inv_apply u x)

theorem sub_one_conj (u t : Kstab v0) :
    wAct v0 (u⁻¹ * t * u) - 1 =
      (wActEquiv u).toLinearMap ∘ₗ (wAct v0 t - 1) ∘ₗ (wActEquiv u).symm.toLinearMap := by
  refine LinearMap.ext fun x => ?_
  change wAct v0 (u⁻¹ * t * u) x - x =
    wAct v0 u (wAct v0 t (wAct v0 u⁻¹ x) - wAct v0 u⁻¹ x)
  rw [wAct_conj, map_sub, wAct_apply_inv]

theorem finrank_range_conj (u t : Kstab v0) :
    finrank (ZMod 2) (LinearMap.range (wAct v0 (u⁻¹ * t * u) - 1)) =
      finrank (ZMod 2) (LinearMap.range (wAct v0 t - 1)) := by
  rw [sub_one_conj, LinearMap.range_comp,
    LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range _), LinearEquiv.finrank_map_eq]

theorem wAct_injective (u : Kstab v0) : Function.Injective (wAct v0 u) := fun a b h => by
  rw [← wAct_inv_apply u a, h, wAct_inv_apply]

theorem ncard_fix_conj {S : Set (Wv v0)} {u : Kstab v0} (hS : ∀ x, x ∈ S ↔ wAct v0 u x ∈ S)
    (t : Kstab v0) :
    {x | x ∈ S ∧ wAct v0 (u⁻¹ * t * u) x = x}.ncard = {x | x ∈ S ∧ wAct v0 t x = x}.ncard := by
  have e : {x | x ∈ S ∧ wAct v0 (u⁻¹ * t * u) x = x} =
      wAct v0 u '' {x | x ∈ S ∧ wAct v0 t x = x} := by
    ext x
    constructor
    · rintro ⟨hx, hfix⟩
      refine ⟨wAct v0 u⁻¹ x, ⟨?_, ?_⟩, wAct_apply_inv u x⟩
      · rw [hS, wAct_apply_inv]
        exact hx
      · rw [wAct_conj] at hfix
        have := congrArg (wAct v0 u⁻¹) hfix
        rwa [wAct_inv_apply] at this
    · rintro ⟨y, ⟨hy, hfix⟩, rfl⟩
      refine ⟨(hS y).1 hy, ?_⟩
      rw [wAct_conj, wAct_inv_apply, hfix]
  rw [e, Set.ncard_image_of_injective _ (wAct_injective u)]

theorem mem_OmegaW_iff_wAct
    (u : Kstab v0) (x : Wv v0) : x ∈ OmegaW ↔ wAct v0 u x ∈ OmegaW :=
  ⟨wAct_mem_OmegaW u, fun h => by
    have := wAct_mem_OmegaW u⁻¹ h
    rwa [wAct_inv_apply] at this⟩


theorem coe_conj_genU
    (u : Usig) :
    ((u⁻¹ * genU 6 * u : Usig) : Kstab v0) = (u : Kstab v0)⁻¹ * genK 6 * u := rfl

theorem finrank_range_genK_six :
    finrank (ZMod 2) (LinearMap.range (wAct v0 (genK 6) - 1)) = 6 := by
  rw [Amalgam.genK_six, Sp8.range_rK_sub_one, Co2Inv.finrank_Zsp]

theorem finrank_range_transvU
    {R : Submodule F4 V6} (hR : IsSingPt R)
    :
    finrank (ZMod 2) (LinearMap.range (wAct v0 (transvU R) - 1)) = 6 := by
  obtain ⟨u, hu⟩ := exists_transvU_conj hR
  rw [hu, coe_conj_genU, finrank_range_conj, finrank_range_genK_six]


theorem ncard_fix_OmegaW_transvU
    {R : Submodule F4 V6} (hR : IsSingPt R) :
    {x | x ∈ OmegaW ∧ wAct v0 (transvU R) x = x}.ncard = 284 := by
  obtain ⟨u, hu⟩ := exists_transvU_conj hR
  rw [hu, coe_conj_genU, ncard_fix_conj (mem_OmegaW_iff_wAct u), ncard_fix_OmegaW]


theorem singVec_five : singVec 5 = e6 2 := by decide +kernel

theorem singPt_five : singPt 5 = Rsp := by
  rw [singPt, singVec_five]
  rfl

theorem five_twelve_mem :
    (5 : ℕ) ∈ o14PtOrb[0]! ∧ (12 : ℕ) ∈ o14PtOrb[1]! :=
  Certificates.certificate3125.1

theorem singPt_five_mem : singPt 5 ∈ ptOrbit 0 :=
    ⟨5, five_twelve_mem.1, rfl⟩

theorem singPt_twelve_mem : singPt 12 ∈ ptOrbit 1 :=
    ⟨12, five_twelve_mem.2, rfl⟩

theorem singGen_vals : singGen 3 5 = 1 ∧ singGen 0 1 = 12 :=
  Certificates.certificate3125.2

theorem singPt_twelve :
    singPt 12 = sigmaAct Rsp
    (phiU (genU 3 * genU 0)) := by
  rw [← singPt_five, ← singPt_singIdx, singIdx_mul, singIdx_genU, singIdx_genU, singGen_vals.1,
    singGen_vals.2]

@[expose] def fixTauPts :
    Set (Submodule F4 V6) :=
  {R | IsSingPt R ∧ wAct v0 (transvU R) tauW = tauW}

theorem fixTauPts_smul
    {R : Submodule F4 V6}
    (hR : R ∈ fixTauPts) {a : Usig} (ha : a ∈ Atau) :
    sigmaAct R (phiU a) ∈ fixTauPts := by
  refine ⟨isSingPt_sigmaAct hR.1 _, ?_⟩
  have h := mem_Atau.1 ha
  have hinv : wAct v0 ((a : Kstab v0)⁻¹) tauW = tauW :=
    calc wAct v0 ((a : Kstab v0)⁻¹) tauW = wAct v0 ((a : Kstab v0)⁻¹) (wAct v0 a tauW) := by
          rw [h]
      _ = tauW := wAct_inv_apply _ _
  rw [transvU_sigmaAct hR.1, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, wAct_conj, hinv,
    hR.2]
  exact h

theorem Rsp_mem_fixTauPts :
    Rsp ∈ fixTauPts := by
  refine ⟨isSingPt_Rsp, ?_⟩
  rw [transvU_Rsp]
  exact wAct_genK_six_tauW

theorem singPt_twelve_not_mem :
    singPt 12 ∉ fixTauPts := by
  rintro ⟨-, h⟩
  rw [singPt_twelve, transvU_sigmaAct isSingPt_Rsp, transvU_Rsp, coe_conj_genU] at h
  have hu : wAct v0 ((genU 3 * genU 0 : Usig) : Kstab v0) (decW 1919652) = tauW := by
    rw [show ((genU 3 * genU 0 : Usig) : Kstab v0) = genK 3 * genK 0 from rfl, wAct_mul,
      Module.End.mul_apply]
    exact wAct_genK_three_zero_wit
  have hy : wAct v0 ((genU 3 * genU 0 : Usig) : Kstab v0)⁻¹ tauW = decW 1919652 := by
    rw [← hu, wAct_inv_apply]
  rw [wAct_conj, hy] at h
  apply wAct_genK_six_wit_ne
  apply wAct_injective ((genU 3 * genU 0 : Usig) : Kstab v0)
  rw [h, hu]

theorem fixTauPts_eq :
    fixTauPts = ptOrbit 0 := by
  have h0 : orbitA (singPt 5) = ptOrbit 0 := orbitA_of_mem_ptOrbit (by norm_num) singPt_five_mem
  apply le_antisymm
  · intro R hR
    have hsing : R ∈ {P | IsSingPt P} := hR.1
    rw [setOf_isSingPt_eq_union] at hsing
    rcases hsing with h | h
    · exact h
    · exfalso
      have h1 : orbitA R = ptOrbit 1 := orbitA_of_mem_ptOrbit (by norm_num) h
      have h12 : singPt 12 ∈ orbitA R := h1 ▸ singPt_twelve_mem
      obtain ⟨a, ha, e⟩ := h12
      exact singPt_twelve_not_mem (e ▸ fixTauPts_smul hR ha)
  · intro P hP
    rw [← h0] at hP
    obtain ⟨a, ha, rfl⟩ := hP
    rw [singPt_five]
    exact fixTauPts_smul Rsp_mem_fixTauPts ha


end CFSG.Monster.B.TwoA.Unitary
