module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicCheck
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicStandard17U

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.Cert

open Subgroup CFSG.Open CFSG.ComponentClassification.RankTwoSporadic CFSG.ABGLocalTools
open CFSG.RankThree.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

section Model

variable {G : Type*} [Group G]

theorem autModel_of_conj {P R : Subgroup G} (hPR : P ≤ R) {X₀ : Type*} [Group X₀]
    (eP : ↥P ≃* X₀) (e : ↥R ≃* MulAut ↥P)
    (he : ∀ (x : ↥R) (p : ↥P), ((e x p : ↥P) : G) = (x : G) * p * (x : G)⁻¹) :
    AutModel X₀ ↥R (P.subgroupOf R) where
  normal := by
    refine ⟨fun y hy x => ?_⟩
    rw [mem_subgroupOf] at hy ⊢
    have := he x ⟨y, hy⟩
    simp only [coe_mul, coe_inv]
    rw [← this]
    exact (e x ⟨y, hy⟩).2
  centralizer_eq_bot := by
    rw [eq_bot_iff]
    intro x hx
    rw [mem_bot]
    apply e.injective
    rw [map_one]
    ext p
    have hxp := mem_centralizer_iff.mp hx ⟨p, hPR p.2⟩ (by
      rw [SetLike.mem_coe, mem_subgroupOf]
      exact p.2)
    have h1 := he x p
    have h2 : (x : G) * p * (x : G)⁻¹ = p := by
      have := congrArg Subtype.val hxp
      simp only [coe_mul] at this
      rw [← this]
      group
    rw [h1, h2]
    rfl
  nonempty_mulEquiv := ⟨(subgroupOfEquivOfLe hPR).trans eP⟩
  exists_conj α := by
    set ψ := subgroupOfEquivOfLe hPR
    refine ⟨e.symm (MulAut.congr ψ α), fun y => ?_⟩
    have h1 := he (e.symm (MulAut.congr ψ α)) (ψ y)
    rw [MulEquiv.apply_symm_apply] at h1
    simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply] at h1
    apply Subtype.ext
    simp only [coe_mul, coe_inv]
    exact h1

theorem autModel_of_allInner {P : Subgroup G} {X₀ : Type*} [Group X₀] (eP : ↥P ≃* X₀)
    (hc : center ↥P = ⊥) (hi : ∀ α : MulAut ↥P, ∃ g : ↥P, α = MulAut.conj g) :
    AutModel X₀ ↥P (P.subgroupOf P) := by
  have hinj : Function.Injective (MulAut.conj : ↥P →* MulAut ↥P) := by
    intro x y hxy
    have hmem : y⁻¹ * x ∈ center ↥P := by
      rw [mem_center_iff]
      intro g
      have h := congrArg (fun φ : MulAut ↥P => φ g) hxy
      simp only [MulAut.conj_apply] at h
      calc g * (y⁻¹ * x) = y⁻¹ * (y * g * y⁻¹) * y * y⁻¹ * x := by group
        _ = y⁻¹ * (x * g * x⁻¹) * y * y⁻¹ * x := by rw [h]
        _ = y⁻¹ * x * g := by group
    rw [hc, mem_bot] at hmem
    calc x = y * (y⁻¹ * x) := by group
      _ = y := by rw [hmem, mul_one]
  have hsurj : Function.Surjective (MulAut.conj : ↥P →* MulAut ↥P) := fun α => by
    obtain ⟨g, hg⟩ := hi α
    exact ⟨g, hg.symm⟩
  let e : ↥P ≃* MulAut ↥P :=
    MulEquiv.ofBijective (MulAut.conj : ↥P →* MulAut ↥P) ⟨hinj, hsurj⟩
  refine autModel_of_conj le_rfl eP e fun x p => ?_
  change ((MulAut.conj x p : ↥P) : G) = (x : G) * p * (x : G)⁻¹
  rw [MulAut.conj_apply]
  simp only [coe_mul, coe_inv]

theorem commutator_le_of_index_two {H : Subgroup G} (h : H.index = 2) :
    ⁅(⊤ : Subgroup G), ⊤⁆ ≤ H := by
  rw [commutator_le]
  intro a _ b _
  rw [commutatorElement_def, mul_mem_iff_of_index_two h, mul_mem_iff_of_index_two h,
    mul_mem_iff_of_index_two h, inv_mem_iff, inv_mem_iff]
  tauto

end Model


end CFSG.ComponentClassification.RankTwoSporadic.Cert
