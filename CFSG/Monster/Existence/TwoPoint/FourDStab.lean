module

public import CFSG.Monster.Existence.TwoPoint.FourDLift
public import CFSG.Monster.Existence.TwoPoint.FourDRoot
public import CFSG.Monster.Existence.TwoPoint.ShapeOneHC
public import CFSG.Monster.B.TwoA.Amalgam.LocalLabel
public import CFSG.Monster.Existence.TwoPoint.Fi23ConjBase
public import CFSG.Monster.Existence.TwoPoint.Fi23MiscBase
public import CFSG.Monster.Existence.TwoPoint.Fi23Rels0Base
public import CFSG.Monster.Existence.TwoPoint.Fi23Rels1Base
public import CFSG.Monster.Existence.TwoPoint.Fi23Rels2Base
public import CFSG.Monster.Existence.TwoPoint.Fi23Rels3Base
public import CFSG.Monster.Existence.TwoPoint.Fi23Rels4Base
public import CFSG.Monster.Existence.TwoPoint.Fi23Rels5Base
public import CFSG.Monster.Existence.TwoPoint.Fi23RelsLongADBase
public import CFSG.Monster.Existence.TwoPoint.Fi23RelsLongJ
public import CFSG.Monster.Existence.TwoPoint.Fi23RelsLongJBase
public import CFSG.Monster.Existence.TwoPoint.Fi23RelsLongM
public import CFSG.Monster.Existence.TwoPoint.Fi23RelsLongMBase
public import CFSG.Monster.Existence.TwoPoint.Fi23RelsLongP
public import CFSG.Monster.Existence.TwoPoint.Fi23RelsLongPBase
public import CFSG.Monster.Existence.TwoPoint.OddAssembly
public import CFSG.Sporadic.Fi22
public import CFSG.Sporadic.HN.CertificateBase

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Existence

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.B.Short
  CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Sp8 CFSG.Monster.B.TwoA.Amalgam
  CFSG.Monster.B.E6 CFSG.Monster.B.E6.StdF4 CFSG.LieType.Chevalley.C2E6Std
  CFSG.LieType.Chevalley.C2E6Std.FieldExtension CFSG.Monster.GMS

@[expose] noncomputable def fdEdgeShat
    (hG : Gmat = AutO) : ↥(cent2 tGriess uGriess) →* Shat :=
  (centToShat hG).comp (Subgroup.inclusion (inf_le_left : cent2 tGriess uGriess ≤ cent tGriess))

theorem coe_fdEdgeShat
    (hG : Gmat = AutO) (e : ↥(cent2 tGriess uGriess)) :
    fdEdgeShat hG e = centToShat hG ⟨e.1, e.2.1⟩ := rfl

theorem fdEdgeShat_commute_cQ
    (hG : Gmat = AutO) (e : ↥(cent2 tGriess uGriess)) :
    ((fdEdgeShat hG e : Shat) : Dfull) * cQ = cQ * ((fdEdgeShat hG e : Shat) : Dfull) := by
  have h : (⟨e.1, e.2.1⟩ : cent tGriess) * uGriessCent = uGriessCent * ⟨e.1, e.2.1⟩ :=
    Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 e.2.2)
  have := congrArg (fun z => ((centToShat hG z : Shat) : Dfull)) h
  simp only [coe_fdEdgeShat]
  simpa [map_mul, centToShat_uGriessCent] using this

theorem fdEdgeShat_mem_vStab
    (hG : Gmat = AutO) (hC : CTIB.CentralizerInput)
    (e : ↥(cent2 tGriess uGriess)) : fdEdgeShat hG e ∈ vStab cv0 := by
  rw [mem_vStab]
  refine (hC cv0 _).1 ?_
  rw [clabel_cv0]
  exact fdEdgeShat_commute_cQ hG e

@[expose] noncomputable def fdEdgeV
    (hG : Gmat = AutO) (hC : CTIB.CentralizerInput) :
    ↥(cent2 tGriess uGriess) →* vStab cv0 :=
  (fdEdgeShat hG).codRestrict (vStab cv0) (fdEdgeShat_mem_vStab hG hC)


@[expose] noncomputable def fdTEdge : ↥(cent2 tGriess uGriess) :=
  ⟨tGriess, Subgroup.mem_inf.2 ⟨self_mem_cent tGriess,
    Subgroup.mem_centralizer_singleton_iff.2 tGriess_mul_uGriess⟩⟩

@[expose] noncomputable def fdUEdge : ↥(cent2 tGriess uGriess) :=
  ⟨uGriess, Subgroup.mem_inf.2 ⟨shapeSix_uGriess_mem_cent, self_mem_cent uGriess⟩⟩

theorem fdEdgeV_eq_one_iff
    (hG : Gmat = AutO) (hC : CTIB.CentralizerInput)
    (e : ↥(cent2 tGriess uGriess)) : fdEdgeV hG hC e = 1 ↔ e = 1 ∨ e = fdTEdge := by
  have h1 : fdEdgeV hG hC e = 1 ↔ centToShat hG ⟨e.1, e.2.1⟩ = 1 :=
    ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  rw [h1, centToShat_eq_one_iff]
  constructor
  · rintro (h | h)
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)
  · rintro (h | h)
    · exact Or.inl (congrArg Subtype.val h)
    · exact Or.inr (congrArg Subtype.val h)

theorem natCard_ker_fdEdgeV
    (hG : Gmat = AutO) (hC : CTIB.CentralizerInput) :
    Nat.card (fdEdgeV hG hC).ker = 2 := by
  refine fd_natCard_eq_two_of_mem_iff _ fdTEdge ?_ fun y => ?_
  · rw [fdTEdge, Subgroup.orderOf_mk]
    exact orderOf_tGriess
  · rw [MonoidHom.mem_ker, fdEdgeV_eq_one_iff]

structure FourDLocalMap
    (ρ : vStab cv0 →* GStar) (iv : cgraph.neighborSet cv0 ≃ rootClass) :
    Prop where
  surj : Function.Surjective ρ
  ker : ∀ y : vStab cv0, ρ y = 1 ↔ ((y : Shat) : Dfull) ∈ Subgroup.zpowers (clabel cv0)
  ord : orderOf (clabel cv0) = 2
  equivar : ∀ (y : vStab cv0) (z : cgraph.neighborSet cv0),
    SemidirectProduct.inl (iv (stabAct y z) : stdGroup) =
      (ρ y)⁻¹ * SemidirectProduct.inl (iv z : stdGroup) * ρ y

theorem exists_fourD_localMap :
    ∃ (ρ : vStab cv0 →* GStar) (iv : cgraph.neighborSet cv0 ≃ rootClass), FourDLocalMap ρ iv := by
  obtain ⟨ρ, iv, h1, h2, -, h4, h5, -, -, -⟩ := native_local_label_root cv0
  exact ⟨ρ, iv, ⟨h1, h2, h4, h5⟩⟩

variable {ρ : vStab cv0 →* GStar} {iv : cgraph.neighborSet cv0 ≃ rootClass}

theorem FourDLocalMap.orderOf_cQ (hρ : FourDLocalMap ρ iv) : orderOf cQ = 2 := by
  have := hρ.ord
  rwa [clabel_cv0] at this

theorem fd_cS_mem_vStab
    (hC : CTIB.CentralizerInput) :
    (⟨cQ, cQ_mem_Shat⟩ : Shat) ∈ vStab cv0 :=
  mem_vStab.2 ((hC cv0 ⟨cQ, cQ_mem_Shat⟩).1 (by rw [clabel_cv0]))

@[expose] noncomputable def fdCV (hC : CTIB.CentralizerInput) : vStab cv0 :=
  ⟨⟨cQ, cQ_mem_Shat⟩, fd_cS_mem_vStab hC⟩

theorem FourDLocalMap.orderOf_cV (hρ : FourDLocalMap ρ iv) (hC : CTIB.CentralizerInput) :
    orderOf (fdCV hC) = 2 := by
  rw [fdCV, Subgroup.orderOf_mk, Subgroup.orderOf_mk]
  exact hρ.orderOf_cQ

theorem FourDLocalMap.mem_ker_iff (hρ : FourDLocalMap ρ iv) (hC : CTIB.CentralizerInput)
    (y : vStab cv0) : y ∈ ρ.ker ↔ y = 1 ∨ y = fdCV hC := by
  rw [MonoidHom.mem_ker, hρ.ker, clabel_cv0,
    CFSG.Monster.B.Short.mem_zpowers_iff_of_orderOf_eq_two hρ.orderOf_cQ]
  constructor
  · rintro (h | h)
    · exact Or.inl (Subtype.ext (Subtype.ext h))
    · exact Or.inr (Subtype.ext (Subtype.ext h))
  · rintro (h | h)
    · exact Or.inl (by rw [h]; rfl)
    · exact Or.inr (by rw [h]; rfl)

theorem FourDLocalMap.natCard_ker (hρ : FourDLocalMap ρ iv) (hC : CTIB.CentralizerInput) :
    Nat.card ρ.ker = 2 :=
  fd_natCard_eq_two_of_mem_iff _ (fdCV hC) (hρ.orderOf_cV hC) (hρ.mem_ker_iff hC)

theorem FourDLocalMap.natCard_vStab (hρ : FourDLocalMap ρ iv) (hC : CTIB.CentralizerInput) :
    Nat.card (vStab cv0) = 2 * Nat.card GStar := by
  have := Subgroup.card_ker_mul_card_of_surjective hρ.surj
  rw [hρ.natCard_ker hC] at this
  exact this.symm

@[expose] noncomputable def fdEdgeRho
    (hG : Gmat = AutO) (hC : CTIB.CentralizerInput)
    (ρ : vStab cv0 →* GStar) : ↥(cent2 tGriess uGriess) →* GStar :=
  ρ.comp (fdEdgeV hG hC)

theorem fdEdgeV_fdUEdge
    (hG : Gmat = AutO) (hC : CTIB.CentralizerInput) :
    fdEdgeV hG hC fdUEdge = fdCV hC :=
  Subtype.ext (Subtype.ext (centToShat_uGriessCent hG))

theorem fdEdgeRho_range
    (hG : Gmat = AutO) (hC : CTIB.CentralizerInput) (hρ : FourDLocalMap ρ iv) :
    (fdEdgeRho hG hC ρ).range = Ginl := by
  have hE := natCard_cent2_tGriess_uGriess_of hC
  have h1 := Subgroup.card_ker_mul_card_range (fdEdgeV hG hC)
  rw [natCard_ker_fdEdgeV hG hC, hE] at h1
  have hQ : Nat.card (fdEdgeV hG hC).range = 2 * Nat.card stdGroup := by omega
  have h2 := hρ.natCard_vStab hC
  rw [card_GStar] at h2
  have h3 := Subgroup.card_mul_index (fdEdgeV hG hC).range
  rw [hQ, h2, card_stdGroup] at h3
  have hidx : (fdEdgeV hG hC).range.index = 2 := by omega
  have hker : ρ.ker ≤ (fdEdgeV hG hC).range := by
    intro y hy
    rcases (hρ.mem_ker_iff hC y).1 hy with h | h
    · rw [h]; exact one_mem _
    · exact ⟨fdUEdge, by rw [fdEdgeV_fdUEdge, h]⟩
  have hidx' : (fdEdgeRho hG hC ρ).range.index = 2 := by
    rw [fdEdgeRho, MonoidHom.range_comp, Subgroup.index_map_eq (fdEdgeV hG hC).range hρ.surj hker]
    exact hidx
  have hc : (commutator GStar).index = 2 := by rw [commutator_GStar]; exact index_Ginl
  rw [fd_eq_commutator_of_index_two hidx' hc, commutator_GStar]

theorem natCard_ker_fdEdgeRho
    (hG : Gmat = AutO) (hC : CTIB.CentralizerInput)
    (hρ : FourDLocalMap ρ iv) : Nat.card (fdEdgeRho hG hC ρ).ker = 4 := by
  have h1 := Subgroup.card_ker_mul_card_range (fdEdgeRho hG hC ρ)
  rw [fdEdgeRho_range hG hC hρ, natCard_cent2_tGriess_uGriess_of hC] at h1
  have : Nat.card Ginl = Nat.card stdGroup := (Nat.card_congr stdGroupEquivGinl.toEquiv).symm
  rw [this, card_stdGroup] at h1
  omega

end CFSG.Monster.Existence
