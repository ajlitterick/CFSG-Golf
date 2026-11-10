module

public import CFSG.Monster.B.CTIB.VisibleOctadCentralizer
public import CFSG.Monster.B.CTIB.Rank2048
public import CFSG.LocalAnalysis.ComponentInitial.SylowLocalTransfer
public import CFSG.LocalAnalysis.ComponentInitial.ParabolicLocalCharacteristicTransfer
public import CFSG.Monster.B.CTIB.UniqueComponentFinal
public import CFSG.Monster.B.CTIB.Rank2158
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.CTIB

open MulOpposite CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Monster CFSG.Monster.B
  CFSG.Monster.Spin CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.Griess
  CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Census CFSG.LocalAnalysis.ComponentInitial
open CFSG.Sporadic.Co2Inv (co2_involution_input)

local notation "MatB" => Matrix (Fin 4370) (Fin 4370) (ZMod 2)
local notation "βr" s => ((betaRow Dyadic.betaS s : MatBˣ) : MatB)

section Transport

variable {A B : Type*} [Group A] [Group B]

theorem exists_selfCent_of_mulEquiv (e : A ≃* B)
    (h : ∃ R : Subgroup A, R.Normal ∧ IsPGroup 2 R ∧ Subgroup.centralizer (R : Set A) ≤ R) :
    ∃ R : Subgroup B, R.Normal ∧ IsPGroup 2 R ∧ Subgroup.centralizer (R : Set B) ≤ R := by
  obtain ⟨R, hRn, hR2, hRc⟩ := h
  refine ⟨R.map e.toMonoidHom, hRn.map _ e.surjective, hR2.map _, fun b hb => ?_⟩
  have hb' : e.symm b ∈ Subgroup.centralizer (R : Set A) :=
    Subgroup.mem_centralizer_iff.2 fun r hr => e.injective (by
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact Subgroup.mem_centralizer_iff.1 hb (e r) ⟨r, hr, rfl⟩)
  exact Subgroup.mem_map_equiv.2 (hRc hb')

theorem ordProj_le_of_mulEquiv (e : A ≃* B) {n : ℕ} (h : ordProj[2] (Nat.card A) ≤ n) :
    ordProj[2] (Nat.card B) ≤ n :=
  (congrArg (fun m => ordProj[2] m) (Nat.card_congr e.toEquiv)).symm.trans_le h

theorem not_isComponent_of_mulEquiv (e : A ≃* B) (h : ∀ K : Subgroup A, ¬ CFSG.IsComponent K) :
    ∀ K : Subgroup B, ¬ CFSG.IsComponent K := fun K hK =>
  h (K.map e.symm.toMonoidHom) (CFSG.LocalCores.isComponent_map_mulEquiv e.symm hK)

theorem exists_selfCent_of_le {D : Type*} [Group D] {T R : Subgroup D} (e : A ≃* T)
    (hRT : R ≤ T) (hRn : (R.subgroupOf T).Normal) (hR2 : IsPGroup 2 R)
    (hcen : T ⊓ Subgroup.centralizer (R : Set D) ≤ R) :
    ∃ R' : Subgroup A, R'.Normal ∧ IsPGroup 2 R' ∧ Subgroup.centralizer (R' : Set A) ≤ R' := by
  refine exists_selfCent_of_mulEquiv e.symm ⟨R.subgroupOf T, hRn,
    hR2.comap_of_injective T.subtype T.subtype_injective, fun x hx => ?_⟩
  refine Subgroup.mem_subgroupOf.2 (hcen ⟨x.2, Subgroup.mem_centralizer_iff.2 fun r hr => ?_⟩)
  exact congrArg Subtype.val
    (Subgroup.mem_centralizer_iff.1 hx ⟨r, hRT hr⟩ (Subgroup.mem_subgroupOf.2 hr))

@[expose] noncomputable def centConjEquiv {G : Type*} [Group G] {a b : G} (c : G)
    (h : c * a * c⁻¹ = b) : Subgroup.centralizer {a} ≃* Subgroup.centralizer {b} :=
  (centralizerEquiv (MulAut.conj c) a).trans (MulEquiv.subgroupCongr (by
    rw [MulAut.conj_apply, h]))

end Transport

@[expose] noncomputable def octadConj :
    SpaceB ≃ₗ[ℚ] SpaceB :=
  exists_conj_cosetRep_one_tStar.choose

theorem octadConj_mem :
    octadConj ∈ Gmat := exists_conj_cosetRep_one_tStar.choose_spec.1

theorem octadConj_conj :
    octadConj * (cosetRep 1 : SpaceB ≃ₗ[ℚ] SpaceB) * octadConj⁻¹ = Short.tStar :=
  exists_conj_cosetRep_one_tStar.choose_spec.2

theorem conj_comm_conj {G : Type*} [Group G] {a b h : G} (hb : b * h = h * b) :
    a * b * a⁻¹ * (a * h * a⁻¹) = a * h * a⁻¹ * (a * b * a⁻¹) := by
  calc a * b * a⁻¹ * (a * h * a⁻¹) = a * (b * h) * a⁻¹ := by group
    _ = a * (h * b) * a⁻¹ := by rw [hb]
    _ = a * h * a⁻¹ * (a * b * a⁻¹) := by group

theorem octadConj_mem_Cfull
    (c : Subgroup.centralizer ({hGmat} : Set Gmat)) :
    octadConj * ((c : Gmat) : SpaceB ≃ₗ[ℚ] SpaceB) * octadConj⁻¹ ∈ Cfull := by
  refine Subgroup.mem_inf.2 ⟨mul_mem (mul_mem octadConj_mem (c : Gmat).2) (inv_mem octadConj_mem),
    Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
  have hc : ((c : Gmat) : SpaceB ≃ₗ[ℚ] SpaceB) * cosetRep 1 = cosetRep 1 * (c : Gmat) :=
    (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 c.2))
  rw [← octadConj_conj]
  exact conj_comm_conj hc

theorem octadConj_inv_mem
    (d : Cfull) :
    (⟨octadConj⁻¹ * (d : SpaceB ≃ₗ[ℚ] SpaceB) * octadConj, mul_mem (mul_mem
      (inv_mem octadConj_mem) (Subgroup.mem_inf.1 d.2).1) octadConj_mem⟩ : Gmat) ∈
        Subgroup.centralizer ({hGmat} : Set Gmat) := by
  refine Subgroup.mem_centralizer_singleton_iff.2 (Subtype.ext ?_)
  have hd : (d : SpaceB ≃ₗ[ℚ] SpaceB) * Short.tStar = Short.tStar * d :=
    commute_tStar_of_mem_Cfull d.2
  rw [← octadConj_conj] at hd
  have h := conj_comm_conj (a := octadConj⁻¹) hd
  simp only [inv_inv] at h
  calc octadConj⁻¹ * (d : SpaceB ≃ₗ[ℚ] SpaceB) * octadConj * (cosetRep 1 : SpaceB ≃ₗ[ℚ] SpaceB) =
      octadConj⁻¹ * (d : SpaceB ≃ₗ[ℚ] SpaceB) * octadConj *
        (octadConj⁻¹ * (octadConj * (cosetRep 1 : SpaceB ≃ₗ[ℚ] SpaceB) * octadConj⁻¹) *
          octadConj) := by group
    _ = octadConj⁻¹ * (octadConj * (cosetRep 1 : SpaceB ≃ₗ[ℚ] SpaceB) * octadConj⁻¹) *
          octadConj * (octadConj⁻¹ * (d : SpaceB ≃ₗ[ℚ] SpaceB) * octadConj) := h
    _ = (cosetRep 1 : SpaceB ≃ₗ[ℚ] SpaceB) * (octadConj⁻¹ * (d : SpaceB ≃ₗ[ℚ] SpaceB) *
          octadConj) := by group

@[expose] noncomputable def octadCentEquiv :
    Subgroup.centralizer ({hGmat} : Set Gmat) ≃* Cfull where
  toFun c := ⟨octadConj * ((c : Gmat) : SpaceB ≃ₗ[ℚ] SpaceB) * octadConj⁻¹,
    octadConj_mem_Cfull c⟩
  invFun d := ⟨_, octadConj_inv_mem d⟩
  left_inv c := Subtype.ext (Subtype.ext (by
    show octadConj⁻¹ * (octadConj * ((c : Gmat) : SpaceB ≃ₗ[ℚ] SpaceB) * octadConj⁻¹) *
      octadConj = c
    group))
  right_inv d := Subtype.ext (by
    show octadConj * (octadConj⁻¹ * (d : SpaceB ≃ₗ[ℚ] SpaceB) * octadConj) * octadConj⁻¹ = d
    group)
  map_mul' a b := Subtype.ext (by
    show octadConj * (((a : Gmat) : SpaceB ≃ₗ[ℚ] SpaceB) * ((b : Gmat) : SpaceB ≃ₗ[ℚ] SpaceB)) *
      octadConj⁻¹ = octadConj * ((a : Gmat) : SpaceB ≃ₗ[ℚ] SpaceB) * octadConj⁻¹ *
        (octadConj * ((b : Gmat) : SpaceB ≃ₗ[ℚ] SpaceB) * octadConj⁻¹)
    group)

theorem octadCentEquiv_hGmat :
    octadCentEquiv ⟨hGmat, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩ = tStarF :=
  Subtype.ext octadConj_conj

theorem map_selfZpowers_hGmat :
    (selfZpowers hGmat).map octadCentEquiv.toMonoidHom = ZstarF :=
  (MonoidHom.map_zpowers _ _).trans (congrArg Subgroup.zpowers octadCentEquiv_hGmat)

@[expose] noncomputable def octadQuotEquiv :
    octadD ≃* Dfull :=
  QuotientGroup.congr (selfZpowers hGmat) ZstarF octadCentEquiv map_selfZpowers_hGmat

@[expose] noncomputable def octadV :
    Dfull := octadQuotEquiv octadT

theorem orderOf_octadT :
    orderOf octadT = 2 := by
  have hx2 : (⟨CFSG.Monster.Existence.xGmat, xGmat_mem_centralizer_hGmat⟩ :
      Subgroup.centralizer ({hGmat} : Set Gmat)) ^ 2 = 1 := by
    have h := pow_orderOf_eq_one CFSG.Monster.Existence.xGmat
    rw [orderOf_xGmat'] at h
    exact Subtype.ext h
  refine orderOf_eq_prime ?_ ?_
  · rw [octadT, ← QuotientGroup.mk_pow, hx2, QuotientGroup.mk_one]
  · intro h1
    rw [octadT, QuotientGroup.eq_one_iff] at h1
    have hh2 : orderOf (⟨hGmat, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩ :
        Subgroup.centralizer ({hGmat} : Set Gmat)) = 2 :=
      (Subgroup.orderOf_coe _).symm.trans orderOf_hGmat
    rcases (Short.mem_zpowers_iff_of_orderOf_eq_two hh2).1 h1 with h | h
    · have h' := congrArg Subtype.val h
      have := orderOf_xGmat'
      rw [show CFSG.Monster.Existence.xGmat = 1 from h', orderOf_one] at this
      exact absurd this (by norm_num)
    · exact hGmat_ne_xGmat (congrArg Subtype.val h).symm

theorem orderOf_octadV :
    orderOf octadV = 2 :=
  (MulEquiv.orderOf_eq octadQuotEquiv octadT).trans orderOf_octadT

@[expose] noncomputable def centOctadVEquiv :
    (Subgroup.centralizer {octadT} : Subgroup octadD) ≃* Subgroup.centralizer {octadV} :=
  centralizerEquiv octadQuotEquiv octadT

theorem isCharacteristicP_octadV :
    CFSG.IsCharacteristicP 2 (Subgroup.centralizer {octadV} : Subgroup Dfull) :=
  isCharacteristicP_of_mulEquiv centOctadVEquiv
    visible_octad_centralizer_normal_two_subgroup_and_bound.2.2.2.2.2.1

theorem ordProj_octadV_le :
    ordProj[2] (Nat.card (Subgroup.centralizer {octadV} : Subgroup Dfull)) ≤ 2 ^ 38 :=
  ordProj_le_of_mulEquiv centOctadVEquiv
    visible_octad_centralizer_normal_two_subgroup_and_bound.2.2.2.2.2.2.2

theorem exists_sylow_le_Shat :
    ∃ P : Sylow 2 Dfull, (P : Subgroup Dfull) ≤ Shat := by
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 2 Jhat))
  obtain ⟨S, hS, -⟩ := full_short_centralizer_odd_index.2.2.2.2.2.2.1 P
  exact ⟨S, hS.le.trans ((Subgroup.map_subtype_le _).trans Jhat_le_Shat)⟩

theorem octad_transfer :
    ∃ s : Dfull, orderOf s = 2 ∧ s ∈ Shat ∧
      (∃ R : Subgroup Dfull, R ≤ Shat ⊓ Subgroup.centralizer {s} ∧
        (R.subgroupOf (Shat ⊓ Subgroup.centralizer {s})).Normal ∧ IsPGroup 2 R ∧
        Shat ⊓ Subgroup.centralizer {s} ⊓ Subgroup.centralizer (R : Set Dfull) ≤ R) ∧
      ordProj[2] (Nat.card ↥(Shat ⊓ Subgroup.centralizer ({s} : Set Dfull))) ≤ 2 ^ 38 := by
  have h := sylow_containing_subgroup_local_normal_two_transfer exists_sylow_le_Shat
    orderOf_octadV isCharacteristicP_octadV
  obtain ⟨s, ⟨g, hg⟩, hsS, hR, -, hcard⟩ := h
  refine ⟨s, ?_, hsS, hR, hcard.trans_le ordProj_octadV_le⟩
  have e := MulEquiv.orderOf_eq (MulAut.conj g⁻¹) octadV
  rw [MulAut.conj_apply, inv_inv] at e
  exact (congrArg orderOf hg).trans (e.trans orderOf_octadV)

@[expose] noncomputable def centShatEquiv (s : Shat) :
    Subgroup.centralizer {s} ≃* (Shat ⊓ Subgroup.centralizer {(s : Dfull)} : Subgroup Dfull) where
  toFun x := ⟨x.1, Subgroup.mem_inf.2 ⟨x.1.2, Subgroup.mem_centralizer_singleton_iff.2
    (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 x.2))⟩⟩
  invFun y := ⟨⟨y, (Subgroup.mem_inf.1 y.2).1⟩, Subgroup.mem_centralizer_singleton_iff.2
    (Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 y.2).2))⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

theorem exists_local_witness :
    ∃ w : Sbp, orderOf w = 2 ∧
    (∃ R : Subgroup (Subgroup.centralizer {w}), R.Normal ∧ IsPGroup 2 R ∧
      Subgroup.centralizer (R : Set (Subgroup.centralizer {w})) ≤ R) ∧
    ordProj[2] (Nat.card (Subgroup.centralizer {w})) ≤ 2 ^ 38 := by
  have ht := octad_transfer
  obtain ⟨s, hs2, hsS, ⟨R, hRT, hRn, hR2, hcen⟩, hcard⟩ := ht
  have hw : sEquiv (sEquiv.symm ⟨s, hsS⟩) = ⟨s, hsS⟩ := sEquiv.apply_symm_apply _
  let e : Subgroup.centralizer {sEquiv.symm ⟨s, hsS⟩} ≃*
      (Shat ⊓ Subgroup.centralizer {s} : Subgroup Dfull) :=
    ((centralizerEquiv sEquiv _).trans (MulEquiv.subgroupCongr
      (congrArg (fun y : Shat => Subgroup.centralizer {y}) hw))).trans (centShatEquiv ⟨s, hsS⟩)
  refine ⟨sEquiv.symm ⟨s, hsS⟩, ?_, exists_selfCent_of_le e hRT hRn hR2 hcen,
    ordProj_le_of_mulEquiv e.symm hcard⟩
  exact (MulEquiv.orderOf_eq sEquiv.symm _).trans
    ((Subgroup.orderOf_coe (⟨s, hsS⟩ : Shat)).symm.trans hs2)

theorem ordProj_two_pow_mul_odd {k m : ℕ} (hm : Odd m) : ordProj[2] (2 ^ k * m) = 2 ^ k := by
  rw [Nat.factorization_mul (pow_ne_zero _ two_ne_zero) (Nat.pos_of_ne_zero
      (fun h => by simp [h] at hm)).ne', Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (Nat.not_even_iff_odd.2 hm ∘ even_iff_two_dvd.2),
    add_zero]

theorem isConj_rs_three_of_rank
    {s : Sbp} (hs : orderOf s = 2)
    (hr : ((βr s) - 1).rank = 2168) : IsConj s (rs 3) := by
  obtain ⟨i, ⟨hi, hc⟩, -⟩ := four_classes co2_involution_input hs
  have e := rank_beta_conj hc
  obtain ⟨h1, h0, h5, h3⟩ := rank_four
  have hi3 : i = 3 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl <;> omega
  exact hi3 ▸ hc

theorem not_isComponent_of_exists_selfCent {G : Type*} [Group G] [Finite G]
    (h : ∃ R : Subgroup G, R.Normal ∧ IsPGroup 2 R ∧ Subgroup.centralizer (R : Set G) ≤ R)
    (K : Subgroup G) : ¬ CFSG.IsComponent K := by
  obtain ⟨R, hRn, hR2, hRc⟩ := h
  exact CFSG.ComponentClassification.OutcomeLocal.not_isComponent_of_selfCentralizing
    (p := 2) hRn hR2 hRc K

theorem rank_of_local_witness
    (h2158 : ∀ s : Sbp, orderOf s = 2 → ((βr s) - 1).rank = 2158 →
      ∃ K : Subgroup (Subgroup.centralizer {s}), CFSG.IsComponent K ∧
        (∀ K' : Subgroup (Subgroup.centralizer {s}), CFSG.IsComponent K' → K' = K) ∧
        IsSimpleGroup K ∧ Nonempty (K ≃* adjointGroup Tag.F4 (ZMod 2)) ∧
        Nat.card K = 3311126603366400 ∧ 17 ∣ Nat.card K)
    {w : Sbp} (hw : orderOf w = 2)
    (hR : ∃ R : Subgroup (Subgroup.centralizer {w}), R.Normal ∧ IsPGroup 2 R ∧
      Subgroup.centralizer (R : Set (Subgroup.centralizer {w})) ≤ R)
    (hcard : ordProj[2] (Nat.card (Subgroup.centralizer {w})) ≤ 2 ^ 38) :
    ((βr w) - 1).rank = 2168 := by
  obtain ⟨i, ⟨hi, hc⟩, -⟩ := four_classes co2_involution_input hw
  have e := rank_beta_conj hc
  obtain ⟨h1, h0, h5, h3⟩ := rank_four
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl
  · have hK := native_rank_1860_unique_component_final w hw (e.trans h1)
    obtain ⟨K, hK, -⟩ := hK
    exact absurd hK (not_isComponent_of_exists_selfCent hR K)
  · have h2048 := native_rank_2048_centralizer_has_no_components w hw (e.trans h0)
    obtain ⟨-, -, -, ⟨m, hm, hmc⟩, -⟩ := h2048
    rw [hmc, ordProj_two_pow_mul_odd hm] at hcard
    exact absurd hcard (by norm_num)
  · have hK := h2158 w hw (e.trans h5)
    obtain ⟨K, hK, -⟩ := hK
    exact absurd hK (not_isComponent_of_exists_selfCent hR K)
  · exact e.trans h3

theorem native_rank_2168_centralizer_has_no_components_of
    (h2158 : ∀ s : Sbp, orderOf s = 2 → ((βr s) - 1).rank = 2158 →
      ∃ K : Subgroup (Subgroup.centralizer {s}), CFSG.IsComponent K ∧
        (∀ K' : Subgroup (Subgroup.centralizer {s}), CFSG.IsComponent K' → K' = K) ∧
        IsSimpleGroup K ∧ Nonempty (K ≃* adjointGroup Tag.F4 (ZMod 2)) ∧
        Nat.card K = 3311126603366400 ∧ 17 ∣ Nat.card K) :
    ∀ s : Sbp, orderOf s = 2 → ((βr s) - 1).rank = 2168 →
      (∃ R : Subgroup (Subgroup.centralizer {s}), R.Normal ∧ IsPGroup 2 R ∧
        Subgroup.centralizer (R : Set (Subgroup.centralizer {s})) ≤ R) ∧
      ordProj[2] (Nat.card (Subgroup.centralizer {s})) ≤ 2 ^ 38 ∧
      ∀ K : Subgroup (Subgroup.centralizer {s}), ¬ CFSG.IsComponent K := by
  intro s hs hr
  have hwit := exists_local_witness
  obtain ⟨w, hw, hR, hcard⟩ := hwit
  have hrw := rank_of_local_witness h2158 hw hR hcard
  have hsw := (isConj_rs_three_of_rank hs hr).trans (isConj_rs_three_of_rank hw hrw).symm
  obtain ⟨c, hc⟩ := isConj_iff.1 hsw
  have hR' := exists_selfCent_of_mulEquiv (centConjEquiv c hc).symm hR
  exact ⟨hR', ordProj_le_of_mulEquiv (centConjEquiv c hc).symm hcard,
    not_isComponent_of_exists_selfCent hR'⟩

end CFSG.Monster.B.CTIB
