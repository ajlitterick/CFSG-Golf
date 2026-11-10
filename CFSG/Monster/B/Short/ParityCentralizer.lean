module

public import CFSG.Monster.B.Short.ParityJ
public import CFSG.Monster.B.Short.Transitivity
public import CFSG.Monster.VisQuot.Simple

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.Short

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.ScalarKernel CFSG.Monster.Visible CFSG.Monster.VisQuot
  CFSG.Monster.VisCert CFSG.Monster.Generated Subgroup

theorem range_piJ
    {r : Q} (hr : IsShortCoord (coordOf r)) :
    (piJ r).range = (Kstab (phi0 (coordOf r))).op := by
  apply le_antisymm
  · rintro _ ⟨f, rfl⟩
    exact piJ_mem_Kstab r f
  · intro x hx
    obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective x.unop
    have hk : (QuotientGroup.mk g : OLq) ∈ Kstab (phi0 (coordOf r)) := hg ▸ hx
    obtain ⟨s, hs⟩ := exists_mem_Pvis g
    obtain ⟨p', hp', hp'2⟩ := exists_conjQ_eq hr ⟨(s, g), hs⟩ hk
    have hc : thetaEquiv p' * rhoEquiv r = rhoEquiv r * thetaEquiv p' := by
      have h1 := thetaEquiv_conj_rhoEquiv p' r
      rw [hp'] at h1
      exact mul_inv_eq_iff_eq_mul.1 h1
    have hJ : thetaEquiv p' ∈ Jmat r := mem_Jmat_iff.2 ⟨thetaEquiv_mem_Gvis p', hc⟩
    refine ⟨⟨thetaEquiv p', hJ⟩, ?_⟩
    rw [piJ_apply]
    refine (piVis_thetaEquiv p').trans ?_
    apply MulOpposite.unop_injective
    rw [MulOpposite.unop_op, hp'2, hg]

theorem orbit_Hvis_eq_shortSet
    {v : L2} (hv : v ∈ shortSet) : MulAction.orbit Hvis v = shortSet := by
  ext y
  constructor
  · rintro ⟨⟨u, hu⟩, rfl⟩
    exact smul_mem_shortSet_of_mem_Hvis hu hv
  · intro hy
    obtain ⟨u, hu, hux⟩ := exists_Hvis_smul_eq_of_short hv hy
    exact ⟨⟨u, hu⟩, hux⟩

theorem natCard_stabilizer_Hvis
    {v : L2} (hv : v ∈ shortSet) :
    Nat.card (MulAction.stabilizer Hvis v) = 42305421312000 := by
  have h1 := (MulAction.stabilizer Hvis v).card_mul_index
  rw [MulAction.index_stabilizer, orbit_Hvis_eq_shortSet hv, ncard_shortSet, natCard_Hvis] at h1
  omega

theorem natCard_Kstab_eq (v : L2) :
    Nat.card (Kstab v) = Nat.card (MulAction.stabilizer Hvis v) := by
  have hmem : ∀ k : OLq, opQHom (MulOpposite.op k) ∈ Hvis := fun k => by
    rw [← range_opQHom]
    exact ⟨_, rfl⟩
  refine Nat.card_eq_of_bijective
    (fun k => (⟨⟨opQHom (MulOpposite.op k.1), hmem k.1⟩, k.2⟩ : MulAction.stabilizer Hvis v))
    ⟨fun a b hab => ?_, ?_⟩
  · have h1 : opQHom (MulOpposite.op a.1) = opQHom (MulOpposite.op b.1) :=
      congrArg (fun x : MulAction.stabilizer Hvis v => ((x : Hvis) : GLV)) hab
    exact Subtype.ext (MulOpposite.op_injective (opQHom_injective h1))
  · rintro ⟨⟨h, hh⟩, hstab⟩
    have hh' : h ∈ opQHom.range := by rw [range_opQHom]; exact hh
    obtain ⟨x, rfl⟩ := hh'
    exact ⟨⟨x.unop, hstab⟩, rfl⟩

theorem natCard_Kstab_of_short
    {v : L2} (hv : v ∈ shortSet) :
    Nat.card (Kstab v) = 42305421312000 :=
  (natCard_Kstab_eq v).trans (natCard_stabilizer_Hvis hv)

instance finite_Q : Finite Q := Nat.finite_of_card_ne_zero (by rw [natCard_Q]; norm_num)

theorem natCard_Q' : Nat.card Q = 2 ^ (1 + 2 * 12) := natCard_Q

theorem natCard_centralizer_Q {r : Q} (hr : IsShortCoord (coordOf r)) :
    Nat.card (centralizer {r} : Subgroup Q) = 2 ^ 24 :=
  (extraspecial_involution_centralizer_quotient (by norm_num) isExtraspecialPGroup_Q natCard_Q'
    center_Q (orderOf_of_isShortCoord hr) (not_mem_center_of_isShortCoord hr)).1

theorem natCard_ker_piJ {r : Q} (hr : IsShortCoord (coordOf r)) :
    Nat.card (piJ r).ker = 2 ^ 24 := by
  rw [ker_piJ, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (rhoCent_le_Jmat r)).toEquiv,
    natCard_rhoCent, natCard_centralizer_Q hr]

theorem natCard_op_eq {G : Type*} [Group G] (H : Subgroup G) : Nat.card H.op = Nat.card H :=
  (Nat.card_congr (Subgroup.equivOp H)).symm

theorem phi0_mem_shortSet' {r : Q} (hr : IsShortCoord (coordOf r)) :
    phi0 (coordOf r) ∈ shortSet := hr

theorem natCard_Jmat
    {r : Q} (hr : IsShortCoord (coordOf r)) :
    Nat.card (Jmat r) = 709767191322427392000 := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (piJ r).ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange (piJ r)).toEquiv, range_piJ hr,
    natCard_op_eq, natCard_Kstab_of_short (phi0_mem_shortSet' hr), natCard_ker_piJ hr] at h
  rw [h]
  norm_num

@[expose] def opSubgroupEquiv {G : Type*} [Group G] (H : Subgroup G) : H.op ≃* H where
  toFun x := ⟨(MulOpposite.unop (x : Gᵐᵒᵖ))⁻¹, H.inv_mem x.2⟩
  invFun k := ⟨MulOpposite.op (k : G)⁻¹, H.inv_mem k.2⟩
  left_inv x := Subtype.ext (by simp)
  right_inv k := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp)


theorem equot_facts {r : Q} (hr : IsShortCoord (coordOf r)) :
    IsExtraspecialPGroup 2 (Equot r) ∧ Nat.card (Equot r) = 2 ^ 23 ∧
    center (Equot r) = zpowers ⟨QuotientGroup.mk (xJ r), mk_xJ_mem_Equot r⟩ ∧
    commutator (Equot r) = zpowers ⟨QuotientGroup.mk (xJ r), mk_xJ_mem_Equot r⟩ ∧
    frattini (Equot r) = zpowers ⟨QuotientGroup.mk (xJ r), mk_xJ_mem_Equot r⟩ := by
  obtain ⟨-, -, -, -, hE, hcard, hcen, hcomm, hfr⟩ :=
    extraspecial_involution_centralizer_quotient (by norm_num) isExtraspecialPGroup_Q natCard_Q'
      center_Q (orderOf_of_isShortCoord hr) (not_mem_center_of_isShortCoord hr)
  have hx := equotEquiv_mk_zD hr
  have hcen' : center (Equot r) = zpowers ⟨QuotientGroup.mk (xJ r), mk_xJ_mem_Equot r⟩ :=
    (center_eq_zpowers_of_mulEquiv (equotEquiv hr) hcen).trans (congrArg zpowers hx)
  have hcomm' : commutator (Equot r) = zpowers ⟨QuotientGroup.mk (xJ r), mk_xJ_mem_Equot r⟩ :=
    (commutator_eq_zpowers_of_mulEquiv (equotEquiv hr) hcomm).trans (congrArg zpowers hx)
  have hfr' : frattini (Equot r) = zpowers ⟨QuotientGroup.mk (xJ r), mk_xJ_mem_Equot r⟩ :=
    (frattini_eq_zpowers_of_mulEquiv (equotEquiv hr) hfr).trans (congrArg zpowers hx)
  have hord : orderOf (⟨QuotientGroup.mk (xJ r), mk_xJ_mem_Equot r⟩ : Equot r) = 2 :=
    (congrArg orderOf hx).symm.trans ((MulEquiv.orderOf_eq (equotEquiv hr) _).trans
      (orderOf_mk_zD isExtraspecialPGroup_Q center_Q (orderOf_of_isShortCoord hr)
        (not_mem_center_of_isShortCoord hr)))
  refine ⟨⟨IsPGroup.of_equiv hE.1 (equotEquiv hr), hcomm'.trans hcen'.symm,
    hfr'.trans hcen'.symm, ?_⟩, ?_, hcen', hcomm', hfr'⟩
  · rw [hcen', Nat.card_zpowers, hord]
  · rw [← Nat.card_congr (equotEquiv hr).toEquiv, hcard]


end CFSG.Monster.B.Short
