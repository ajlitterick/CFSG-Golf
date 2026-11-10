module

public import CFSG.Monster.B.GSide.CompletionFusion
public import CFSG.Monster.B.GSide.EdgeQCertL
public import CFSG.Monster.B.CTIB.HOuter

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.GSide

open MulOpposite CFSG.Monster.B CFSG.Monster.B.CTIB CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Sp8
  CFSG.Monster.B.TwoA.Amalgam

local notation "MatB" => Matrix (Fin 4370) (Fin 4370) (ZMod 2)
local notation "βr" s => ((betaRow Dyadic.betaS s : MatBˣ) : MatB)

theorem rs6_mul_self :
    rs 6 * rs 6 = 1 := by
  obtain ⟨g, hg⟩ := isConj_iff.1 isConj_rs6_labelS
  calc rs 6 * rs 6 = g⁻¹ * ((g * rs 6 * g⁻¹) * (g * rs 6 * g⁻¹)) * g := by group
    _ = 1 := by rw [hg, labelS_mul_self]; group

theorem exists_rkH_2168_mul_2048 :
    ∃ y : vStab cv0, y * y = 1 ∧ rkH y = 2168 ∧ rkH (cV0 * y) = 2048 := by
  obtain ⟨k, hk⟩ := isConj_iff.1 isConj_rs6_labelS
  set g : Sbp := k⁻¹ with hgk
  have hg : g⁻¹ * rs 6 * g = labelS := by rw [hgk, inv_inv]; exact hk
  have hrx : rs 6 * xs = xs * rs 6 := commute_rs6_xs.eq
  set s : Sbp := g⁻¹ * (rs 6 * xs) * g with hs
  have hls : labelS * s = g⁻¹ * xs * g := by
    rw [← hg, hs]
    calc g⁻¹ * rs 6 * g * (g⁻¹ * (rs 6 * xs) * g) = g⁻¹ * (rs 6 * rs 6 * xs) * g := by group
      _ = g⁻¹ * xs * g := by rw [rs6_mul_self, one_mul]
  have hsl : s * labelS = g⁻¹ * xs * g := by
    rw [← hg, hs]
    calc g⁻¹ * (rs 6 * xs) * g * (g⁻¹ * rs 6 * g) = g⁻¹ * (rs 6 * (xs * rs 6)) * g := by group
      _ = g⁻¹ * (rs 6 * (rs 6 * xs)) * g := by rw [hrx]
      _ = g⁻¹ * xs * g := by rw [← mul_assoc (rs 6), rs6_mul_self, one_mul]
  have hcomm : s * labelS = labelS * s := hsl.trans hls.symm
  have hss : s * s = 1 := by
    rw [hs]
    calc g⁻¹ * (rs 6 * xs) * g * (g⁻¹ * (rs 6 * xs) * g) =
        g⁻¹ * (rs 6 * (xs * rs 6) * xs) * g := by group
      _ = g⁻¹ * (rs 6 * rs 6 * (xs * xs)) * g := by rw [← hrx]; group
      _ = 1 := by rw [rs6_mul_self, xs_mul_self, one_mul]; group
  refine ⟨⟨sEquiv s, (commute_labelS_iff_mem s).1 hcomm⟩, ?_, ?_, ?_⟩
  · apply Subtype.ext
    show sEquiv s * sEquiv s = 1
    rw [← map_mul, hss, map_one]
  · show ((βr (sEquiv.symm (sEquiv s))) - 1).rank = 2168
    rw [MulEquiv.symm_apply_apply, hs, rank_conj, rank_rs6_mul_xs]
  · rw [rkH_cV0_mul]
    show ((βr (labelS * sEquiv.symm (sEquiv s))) - 1).rank = 2048
    rw [MulEquiv.symm_apply_apply, hls, rank_conj, rank_xs]

theorem rkH_one :
    rkH 1 = 0 := by
  rw [rkH, Subgroup.coe_one, map_one]
  exact rank_beta_one

theorem h2D_of_psi
    {G : Type*} [Group G] {d : G} (ψ : Subgroup.centralizer {d} ≃* vStab cv0)
    (hψ : ψ ⟨d, mem_centralizer_singleton_self d⟩ = cV0) :
    ∃ y : vStab cv0, orderOf y = 2 ∧ rankS (y : Shat) = 2168 ∧ y ∉ dH ψ := by
  obtain ⟨y, hy2, hr, hcr⟩ := exists_rkH_2168_mul_2048
  have hy1 : y ≠ 1 := by
    rintro rfl
    rw [rkH_one] at hr
    exact absurd hr (by decide)
  refine ⟨y, orderOf_eq_prime (by rw [sq, hy2]) hy1, hr, ?_⟩
  exact not_mem_dH_of_rkH_mul_2048 ψ hψ hy2 hcr (by rw [hr]; decide)

theorem conjugatesOf_inter_range_of_psi
    {G : Type*} [Group G] {d : G} (hd : d ≠ 1)
    (ψ : Subgroup.centralizer {d} ≃* vStab cv0)
    (hψ : ψ ⟨d, mem_centralizer_singleton_self d⟩ = cV0) (Φ : Shat →* G)
    (hΦ : ∀ a : vStab cv0, Φ a = psiInvHom ψ a)
    (h2C : ∀ y : vStab cv0, orderOf y = 2 →
      Nat.card (Subgroup.centralizer {y}) = 13244506413465600 → ¬ IsConj y (cV0 * y)) :
    conjugatesOf d ∩ (Φ.range : Set G) = dZero Φ.range d :=
  conjugatesOf_inter_range hd ψ Φ hΦ h2C (h2D_of_psi ψ hψ)

theorem symm_mem_centQ
    {a : cEdgeFix} (haQ : cEdgeIncl a ∈ edgeQ) :
    sEquiv.symm (a : Shat) ∈ Qs ∧
      sEquiv.symm (a : Shat) * labelS = labelS * sEquiv.symm (a : Shat) := by
  have hN : ((a : Shat) : Dfull) ∈ (N1 : Set Dfull) :=
    ⟨haQ, (mem_cEdgeFix_iff.1 a.2).2⟩
  rw [← image_centQ_labelS] at hN
  obtain ⟨y, ⟨hyQ, hyc⟩, hy⟩ := hN
  have e : sEquiv y⁻¹ = (a : Shat) := by
    apply Subtype.ext
    rw [coe_sEquiv, ← hy]
    show (iotaD (y⁻¹).unop)⁻¹ = iotaD y.unop
    rw [unop_inv, map_inv, inv_inv]
  rw [← e, MulEquiv.symm_apply_apply]
  refine ⟨Qs.inv_mem hyQ, ?_⟩
  calc y⁻¹ * labelS = y⁻¹ * (labelS * y) * y⁻¹ := by group
    _ = y⁻¹ * (y * labelS) * y⁻¹ := by rw [hyc]
    _ = labelS * y⁻¹ := by group

theorem rkH_cEdgeFixToH
    (a : cEdgeFix) :
    rkH (cEdgeFixToH a) = ((βr (sEquiv.symm (a : Shat))) - 1).rank := rfl

theorem rkH_cV0_mul_cEdgeFixToH
    (a : cEdgeFix) :
    rkH (cV0 * cEdgeFixToH a) = ((βr (labelS * sEquiv.symm (a : Shat))) - 1).rank := by
  rw [rkH_cV0_mul]
  rfl

theorem symm_mul_self
    {a : cEdgeFix} (ha2 : a * a = 1) :
    sEquiv.symm (a : Shat) * sEquiv.symm (a : Shat) = 1 := by
  rw [← map_mul, ← Subgroup.coe_mul, ha2, Subgroup.coe_one, map_one]

theorem symm_ne_one
    {a : cEdgeFix} (ha1 : a ≠ 1) : sEquiv.symm (a : Shat) ≠ 1 := by
  intro h
  apply ha1
  apply Subtype.ext
  rw [Subgroup.coe_one]
  exact (MulEquiv.map_eq_one_iff sEquiv.symm).1 h

theorem symm_ne_labelS
    {a : cEdgeFix} (hac : a ≠ lamV0) : sEquiv.symm (a : Shat) ≠ labelS := by
  intro h
  apply hac
  apply Subtype.ext
  rw [← sEquiv_symm_cV0] at h
  exact sEquiv.symm.injective h

theorem rkH_pair_of_mem_edgeQ
    {a : cEdgeFix} (haQ : cEdgeIncl a ∈ edgeQ) (ha2 : a * a = 1)
    (ha1 : a ≠ 1) (hac : a ≠ lamV0) :
    (rkH (cEdgeFixToH a) = 2048 ∧ rkH (cV0 * cEdgeFixToH a) = 1860) ∨
      (rkH (cEdgeFixToH a) = 1860 ∧ rkH (cV0 * cEdgeFixToH a) = 2048) ∨
      (rkH (cEdgeFixToH a) = 2048 ∧ rkH (cV0 * cEdgeFixToH a) = 2168) ∨
      (rkH (cEdgeFixToH a) = 2168 ∧ rkH (cV0 * cEdgeFixToH a) = 2048) ∨
      (rkH (cEdgeFixToH a) = 2168 ∧ rkH (cV0 * cEdgeFixToH a) = 2168) := by
  have hQc := symm_mem_centQ haQ
  have hcen := (native_inner_involution_census labelS_mem (IsConj.refl labelS)).2.1
  have h := hcen _ hQc.1 hQc.2 (symm_mul_self ha2) (symm_ne_one ha1) (symm_ne_labelS hac)
  rw [rkH_cEdgeFixToH, rkH_cV0_mul_cEdgeFixToH]
  exact h

theorem rankS_eq_1860_iff_label
    {s : Shat} (hs : orderOf s = 2) :
    rankS s = 1860 ↔ ∃ v : CVert, s = clabelS v := by
  constructor
  · intro h
    obtain ⟨g, hg⟩ := isConj_iff.1 (isConj_of_rankS_eq orderOf_coe_cV0 hs (rankS_cV0.trans h.symm))
    refine ⟨cvMul cv0 g⁻¹, ?_⟩
    rw [clabelS_cvMul, inv_inv, ← hg, coe_cV0]
  · rintro ⟨v, rfl⟩
    rw [← rankS_cV0]
    apply rankS_conj
    rw [coe_cV0]
    exact isConj_clabelS v cv0

theorem rkH_eq_1860_iff_label
    {a : cEdgeFix} (ha2 : orderOf a = 2) :
    rkH (cEdgeFixToH a) = 1860 ↔ ∃ v : CVert, (a : Shat) = clabelS v := by
  have h : orderOf (a : Shat) = 2 := by rw [Subgroup.orderOf_coe, ha2]
  exact rankS_eq_1860_iff_label h

theorem native_N1_exclusion
    {a : cEdgeFix} (haQ : cEdgeIncl a ∈ edgeQ) (ha2 : orderOf a = 2)
    (hac : a ≠ lamV0) (hal : ¬ ∃ v : CVert, (a : Shat) = clabelS v) :
    rkH (cEdgeFixToH a) = 2048 ∨
      (rkH (cV0 * cEdgeFixToH a) = 2048 ∧ rkH (cEdgeFixToH a) ≠ 1860) ∨
      (rkH (cEdgeFixToH a) = 2168 ∧ rkH (cV0 * cEdgeFixToH a) = 2168) := by
  have ha2' : a * a = 1 := by
    have h := pow_orderOf_eq_one a
    rwa [ha2, sq] at h
  have ha1 : a ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at ha2
    exact absurd ha2 (by norm_num)
  have h1860 : rkH (cEdgeFixToH a) ≠ 1860 := fun h => hal ((rkH_eq_1860_iff_label ha2).1 h)
  rcases rkH_pair_of_mem_edgeQ haQ ha2' ha1 hac with h | h | h | h | h
  · exact .inl h.1
  · exact absurd h.1 h1860
  · exact .inl h.1
  · exact .inr (.inl ⟨h.2, h1860⟩)
  · exact .inr (.inr h)

theorem label_of_mem_dH_of_mem_edgeQ
    {G : Type*} [Group G] {d : G}
    (ψ : Subgroup.centralizer {d} ≃* vStab cv0)
    (hψ : ψ ⟨d, mem_centralizer_singleton_self d⟩ = cV0)
    (hY3 : ∀ a : cEdgeFix, cEdgeIncl a ∈ edgeQ → a * a = 1 → rkH (cEdgeFixToH a) = 2168 →
      rkH (cV0 * cEdgeFixToH a) = 2168 → cEdgeFixToH a ∉ dH ψ)
    {a : cEdgeFix} (haQ : cEdgeIncl a ∈ edgeQ) (ha2 : orderOf a = 2)
    (haD : cEdgeFixToH a ∈ dH ψ) : ∃ v : CVert, (a : Shat) = clabelS v := by
  by_contra hal
  have ha2' : a * a = 1 := by
    have h := pow_orderOf_eq_one a
    rwa [ha2, sq] at h
  have hy2 : cEdgeFixToH a * cEdgeFixToH a = 1 := by rw [← map_mul, ha2', map_one]
  by_cases hac : a = lamV0
  · exact hal ⟨cv0, by rw [hac]; rfl⟩
  rcases native_N1_exclusion haQ ha2 hac hal with h | ⟨h, h'⟩ | ⟨h, h'⟩
  · exact not_mem_dH_of_rkH_2048 ψ hψ hy2 h haD
  · exact not_mem_dH_of_rkH_mul_2048 ψ hψ hy2 h h' haD
  · exact hY3 a haQ ha2' h h' haD

theorem rkH_eq_1860_iff_edgeL
    {a : cEdgeFix} (haQ : cEdgeIncl a ∈ edgeQ) (ha2 : orderOf a = 2)
    (hac : a ≠ lamV0) : rkH (cEdgeFixToH a) = 1860 ↔ a = lamW0 ∨ a ∈ edgeL := by
  rw [rkH_eq_1860_iff_label ha2]
  constructor
  · rintro ⟨v, hv⟩
    by_cases h1 : a = lamW0
    · exact .inl h1
    · exact .inr ⟨haQ, ⟨v, hv⟩, hac, h1⟩
  · rintro (rfl | ⟨-, hl, -, -⟩)
    · exact ⟨cw0, rfl⟩
    · exact hl

theorem native_N1_exclusion_edgeL
    {a : cEdgeFix} (haQ : cEdgeIncl a ∈ edgeQ)
    (ha2 : orderOf a = 2) (hac : a ≠ lamV0) (hae : a ≠ lamW0) (haL : a ∉ edgeL) :
    rkH (cEdgeFixToH a) = 2048 ∨
      (rkH (cV0 * cEdgeFixToH a) = 2048 ∧ rkH (cEdgeFixToH a) ≠ 1860) ∨
      (rkH (cEdgeFixToH a) = 2168 ∧ rkH (cV0 * cEdgeFixToH a) = 2168) :=
  native_N1_exclusion haQ ha2 hac fun ⟨v, hv⟩ => haL ⟨haQ, ⟨v, hv⟩, hac, hae⟩

theorem hN1D_of_Y3
    {G : Type*} [Group G] {d : G} (ψ : Subgroup.centralizer {d} ≃* vStab cv0)
    (hψ : ψ ⟨d, mem_centralizer_singleton_self d⟩ = cV0)
    (hY3 : ∀ a : cEdgeFix, cEdgeIncl a ∈ edgeQ → a * a = 1 → rkH (cEdgeFixToH a) = 2168 →
      rkH (cV0 * cEdgeFixToH a) = 2168 → cEdgeFixToH a ∉ dH ψ)
    {a : cEdgeFix} (haQ : cEdgeIncl a ∈ edgeQ) (ha2 : orderOf a = 2)
    (haD : cEdgeFixToH a ∈ dH ψ) : a = lamV0 ∨ a = lamW0 ∨ a ∈ edgeL := by
  obtain ⟨v, hv⟩ := label_of_mem_dH_of_mem_edgeQ ψ hψ hY3 haQ ha2 haD
  by_cases h0 : a = lamV0
  · exact .inl h0
  by_cases h1 : a = lamW0
  · exact .inr (.inl h1)
  exact .inr (.inr ⟨haQ, ⟨v, hv⟩, h0, h1⟩)

end CFSG.Monster.B.GSide
