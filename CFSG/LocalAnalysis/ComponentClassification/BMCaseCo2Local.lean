module

public import CFSG.Monster.B.Cbar.Simple
public import CFSG.Monster.B.Co2Catalog
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.ComponentClassification.BMCase

open CFSG CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.B
  CFSG.Monster.B.Short

theorem Kstab_rStar_simple :
    IsSimpleGroup (Kstab (phi0 (coordOf rStar))) ∧
      Nat.card (Kstab (phi0 (coordOf rStar))) = 42305421312000 := by
  have h := (Co2.native_short_stabilizer_simple.1 (vMinus 0 1) (vMinus_mem (by decide))).2.2
  have hs := (Co2.native_short_stabilizer_simple.1 (vMinus 0 1) (vMinus_mem (by decide))).1
  have e : Kstab (classOf (vMinus 0 1)) ≃* Kstab (phi0 (coordOf rStar)) :=
    MulEquiv.subgroupCongr (congrArg Kstab phi0_coordOf_rStar.symm)
  exact ⟨@MulEquiv.isSimpleGroup _ _ _ _ hs e.symm, (Nat.card_congr e.toEquiv).symm.trans h⟩


theorem centralizer_Ebar_eq : Subgroup.centralizer (Ebar : Set Cbar) = Subgroup.zpowers xbar := by
  apply le_antisymm
  · intro c hc
    have hcx : c ∈ Subgroup.centralizer ({xbar} : Set Cbar) :=
      Subgroup.mem_centralizer_singleton_iff.2
        ((Subgroup.mem_centralizer_iff.1 hc) xbar xbar_mem_Ebar).symm
    rw [centralizer_xbar] at hcx
    rw [← centralizer_Ebar]
    exact ⟨hcx, hc⟩
  · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    intro e he
    have hx : xbar ∈ (Subgroup.center Ebar).map Ebar.subtype := by
      rw [map_center_Ebar]
      exact Subgroup.mem_zpowers xbar
    obtain ⟨z, hz, hzx⟩ := hx
    have h := congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨e, he⟩)
    rw [← hzx]
    change e * (z : Cbar) = (z : Cbar) * e
    simpa using h

theorem zQ_mul_wQ_mem_centralizer : zQ * wQ ∈ Subgroup.centralizer {rStar} := by
  have hspin := triality_four_group_spin_identification
  have hy : xmatTau = rhoEquiv (zQ * wQ) := hspin.2.2.2.2.2.1
  have hc := commute_tStar_of_mem_Cgen xmatTau_mem_Cgen
  rw [hy, tStar, ← rhoEquiv_mul, ← rhoEquiv_mul] at hc
  exact Subgroup.mem_centralizer_singleton_iff.2 (rhoEquiv_injective hc).symm

theorem conj_xbar_mem_Ebar : taubar * xbar * taubar⁻¹ ∈ Ebar := by
  rw [taubar_conj_xbar]
  have e : yC = ⟨rhoEquiv (zQ * wQ), rhoEquiv_mem_Cgen zQ_mul_wQ_mem_centralizer⟩ :=
    Subtype.ext triality_four_group_spin_identification.2.2.2.2.2.1
  change kappa yC ∈ Ebar
  rw [e]
  exact kappa_rho_mem_Ebar zQ_mul_wQ_mem_centralizer

theorem conj_xbar_not_mem_zpowers : taubar * xbar * taubar⁻¹ ∉ Subgroup.zpowers xbar := by
  rw [taubar_conj_xbar, Short.mem_zpowers_iff_of_orderOf_eq_two orderOf_xbar]
  rintro (h | h)
  · exact ybar_ne_one h
  · exact xbar_ne_ybar h.symm


theorem exists_surjective_ker_eq_of_quotient_equiv {J : Type*} [Group J] (N : Subgroup J)
    [N.Normal] {G : Type*} [Group G] (e : J ⧸ N ≃* G) :
    ∃ f : J →* G, Function.Surjective f ∧ f.ker = N := by
  refine ⟨e.toMonoidHom.comp (QuotientGroup.mk' N),
    e.surjective.comp (QuotientGroup.mk'_surjective N), ?_⟩
  ext g
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff,
    QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]

theorem jbar_exact_sequence : ∃ f : Jbar →* Blueprint.NativeSporadic.Co2,
    Function.Surjective f ∧ f.ker = Ebar.subgroupOf Jbar :=
  exists_surjective_ker_eq_of_quotient_equiv _ Co2Catalog.jbarQuotEquiv


end CFSG.ComponentClassification.BMCase
