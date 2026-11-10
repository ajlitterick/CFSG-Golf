module

public import CFSG.Monster.B.GSide.HInnerFusionY3Cert
public import CFSG.Monster.B.GSide.HInnerFusionI3

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.GSide

open MulOpposite CFSG.Blueprint CFSG.Monster.B CFSG.Monster.B.CTIB CFSG.Monster.B.TwoA
  CFSG.Monster.B.TwoA.Sp8 CFSG.Monster.B.TwoA.Amalgam ConjAct
open CFSG.Monster.B.CTIB.Native (qmul gArr liftImgsN sqCode autApply qinv wordAut genInvImgs
  natCertOK natBfs)

local notation "MatB" => Matrix (Fin 4370) (Fin 4370) (ZMod 2)
local notation "βr" s => ((betaRow Dyadic.betaS s : MatBˣ) : MatB)

theorem y3Cert_parts :
    (List.range 6).all (fun j => yAct (yAuts ()) j 7 == 7) = true ∧ frameA innerTab 32 = true ∧
    natCertOK (yAct (yAuts ())) 6 (fun p => decide (p < 2 ^ 23)) 32
      (natBfs (yAct (yAuts ())) 6 32 2241).1 (natBfs (yAct (yAuts ())) 6 32 2241).2.1
      (natBfs (yAct (yAuts ())) 6 32 2241).2.2.1 (natBfs (yAct (yAuts ())) 6 32 2241).2.2.2 =
      true ∧
    (natBfs (yAct (yAuts ())) 6 32 2241).1.size = 2240 ∧
    innerTy innerTab 128 = 1 ∧ autApply gArr (liftImgsN 8).toArray 128 = 128 ∧
    qmul gArr 128 9 = qmul gArr 9 128 ∧
    qmul gArr (sqCode 8) (qmul gArr (autApply gArr (liftImgsN 8).toArray 9) 9) = 7618823 ∧
    innerTy innerTab 7618823 = 3 ∧ qmul gArr 128 7618823 = qmul gArr 7618823 128 ∧
    innerTy innerTab (qmul gArr 128 7618823) = 3 := by
  have h := y3CertOK_eq_true
  simp only [y3CertOK, Bool.and_eq_true, beq_iff_eq, and_assoc] at h
  exact h

theorem rank_of_innerTy_three
    {n : ℕ} (hn : n < 2 ^ 23) (h : innerTy innerTab n = 3) :
    ((βr (qS n)) - 1).rank = 2168 := by
  rw [(rank_of_innerTy hn h (by decide)).2]
  rfl

@[expose] def yElt
    (j : ℕ) : Sbp := wordS' (yWords.getD j []) * qS (yFlips.getD j 0)

theorem yWords_letters {j : ℕ} (hj : j < 6) : ∀ l ∈ yWords.getD j [], IsLetter2 l := by
  interval_cases j <;> decide

theorem yWords_length : yWords.length = 6 := rfl

theorem yAuts_getD {j : ℕ} (hj : j < 6) :
    (yAuts ()).getD j #[] = wordAut (genInvImgs ()) (yWords.getD j []) := by
  have hl : j < yWords.length := by rw [yWords_length]; exact hj
  rw [yAuts, Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_map,
    List.getElem?_eq_getElem hl, Option.map_some, Option.getD_some, List.getD_eq_getElem _ _ hl]

theorem conj_yElt_qS
    {j : ℕ} (hj : j < 6) (n : ℕ) :
    (yElt j)⁻¹ * qS n * yElt j = qS (yAct (yAuts ()) j n) := by
  have hw := conj_wordS' (yWords_letters hj)
  have hc := conj_qS hw.2.2 hw.1 n
  have e : (yElt j)⁻¹ * qS n * yElt j = (qS (yFlips.getD j 0))⁻¹ *
      ((wordS' (yWords.getD j []))⁻¹ * qS n * wordS' (yWords.getD j [])) *
      qS (yFlips.getD j 0) := by
    rw [yElt]
    group
  rw [e, hc, yAct, yAuts_getD hj, ← qS_mul, ← qS_mul, qS_qinv]

theorem yElt_mem_Jbar
    {j : ℕ} (hj : j < 6) : yElt j ∈ Jbar.op :=
  Jbar.op.mul_mem (conj_wordS' (yWords_letters hj)).2.2 (Ebar_le_Jbar (qS_mem _))

@[expose] def kQ7 : Subgroup Sbp := Subgroup.centralizer {qS 7} ⊓ Subgroup.centralizer {xs}

theorem yElt_inv_mem_kQ7
    {j : ℕ} (hj : j < 6) : (yElt j)⁻¹ ∈ kQ7 := by
  have h7 : (yElt j)⁻¹ * qS 7 * yElt j = qS 7 := by
    rw [conj_yElt_qS hj]
    have h := y3Cert_parts.1
    simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at h
    rw [h j hj]
  refine kQ7.inv_mem ⟨Subgroup.mem_centralizer_singleton_iff.2 ?_, ?_⟩
  · calc yElt j * qS 7 = yElt j * ((yElt j)⁻¹ * qS 7 * yElt j) := by rw [h7]
      _ = qS 7 * yElt j := by group
  · rw [centralizer_xs_eq]
    exact yElt_mem_Jbar hj

theorem qS32_mem_aSet :
    qS 32 ∈ aSet := by
  have h := y3Cert_parts.2.1
  simp only [frameA, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨h1, hc⟩, h3⟩ := h
  refine ⟨qS_mem _, mem_jClass_of_innerTy (by norm_num) h1, qS_comm_of_code hc, ?_⟩
  rw [qS_mul]
  exact rank_of_innerTy_three (qmul_lt _ _) h3

theorem exists_conj_of_mem_aSet
    {c : Sbp} (hc : c ∈ aSet) :
    ∃ k ∈ kQ7, c = k * qS 32 * k⁻¹ := by
  obtain ⟨-, -, hcert, hsize, -⟩ := y3Cert_parts
  have hact : ∀ j < 6, ∀ a, decide (a < 2 ^ 23) = true →
      qS (yAct (yAuts ()) j a) = (fun j => toConjAct (yElt j)⁻¹) j • qS a := by
    intro j hj a _
    rw [toConjAct_smul, inv_inv, conj_yElt_qS hj]
  have hinj : ∀ a b, decide (a < 2 ^ 23) = true → decide (b < 2 ^ 23) = true →
      qS a = qS b → a = b := fun a b ha hb h =>
    qS_injOn (of_decide_eq_true ha) (of_decide_eq_true hb) h
  obtain ⟨-, hnc, -, -⟩ := orbit_of_nativeCert (dec := qS) hcert hact hinj
  set O := MulAction.orbit (Subgroup.closure
    ((fun j => toConjAct (yElt j)⁻¹) '' {k | k < 6})) (qS 32) with hO
  have hcl : Subgroup.closure ((fun j => toConjAct (yElt j)⁻¹) '' {k | k < 6}) ≤
      kQ7.map (toConjAct : Sbp ≃* ConjAct Sbp).toMonoidHom := by
    rw [Subgroup.closure_le]
    rintro _ ⟨j, hj, rfl⟩
    exact ⟨(yElt j)⁻¹, yElt_inv_mem_kQ7 hj, rfl⟩
  have hOk : ∀ x ∈ O, ∃ k ∈ kQ7, x = k * qS 32 * k⁻¹ := by
    rintro x ⟨⟨c, hc⟩, rfl⟩
    obtain ⟨k, hk, rfl⟩ := hcl hc
    refine ⟨k, hk, ?_⟩
    show (toConjAct k : ConjAct Sbp) • qS 32 = k * qS 32 * k⁻¹
    rw [toConjAct_smul]
  have hOA : O ⊆ aSet := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := hOk x hx
    exact mem_aSet_conj hk qS32_mem_aSet
  have hOeq : O = aSet := Set.eq_of_subset_of_ncard_le hOA
    (by rw [hnc, hsize]; exact ncard_aSet_le) (Set.toFinite _)
  rw [← hOeq] at hc
  exact hOk c hc

theorem witness_aSet :
    ∃ c₀ ∈ aSet, ∃ s : Sbp, s * c₀ = c₀ * s ∧ s * s = qS 7 := by
  obtain ⟨-, -, -, -, h128, -, h9c, hsq, hy3, hyc, hy33⟩ := y3Cert_parts
  have hs₀c : cosetElt 8 9 * qS 128 = qS 128 * cosetElt 8 9 := cosetElt8_comm h9c
  have hs₀2 : cosetElt 8 9 * cosetElt 8 9 = qS 7618823 := by
    rw [cosetElt_sq (.inr (.inl rfl)), ← liftImgsN_eq, hsq]
  obtain ⟨g, hg, hge⟩ := mem_jClass_seven_of_innerTy (by norm_num) hy3
  have e7 : g * qS 7618823 * g⁻¹ = qS 7 := by rw [hge]; group
  refine ⟨g * qS 128 * g⁻¹, ⟨?_, ?_, ?_, ?_⟩, g * cosetElt 8 9 * g⁻¹, ?_, ?_⟩
  · have h := conj_mem_Qs (g := g⁻¹) (Jbar.op.inv_mem hg) (qS_mem 128)
    rwa [inv_inv] at h
  · exact conj_mem_jClass hg (mem_jClass_of_innerTy (by norm_num) h128)
  · rw [← e7, conj_mul_conj', conj_mul_conj', qS_comm_of_code hyc]
  · rw [← e7, conj_mul_conj', rank_conj_inv, qS_mul]
    exact rank_of_innerTy_three (qmul_lt _ _) hy33
  · rw [conj_mul_conj', conj_mul_conj', hs₀c]
  · rw [conj_mul_conj', hs₀2, e7]

theorem sq_of_mem_aSet
    {c : Sbp} (hc : c ∈ aSet) : ∃ s : Sbp, s * c = c * s ∧ s * s = qS 7 := by
  obtain ⟨c₀, hc₀, s, hsc, hs2⟩ := witness_aSet
  obtain ⟨k₁, hk₁, rfl⟩ := exists_conj_of_mem_aSet hc
  obtain ⟨k₂, hk₂, hc₂⟩ := exists_conj_of_mem_aSet hc₀
  have hk : k₁ * k₂⁻¹ ∈ kQ7 := kQ7.mul_mem hk₁ (kQ7.inv_mem hk₂)
  have hk7 : k₁ * k₂⁻¹ * qS 7 * (k₁ * k₂⁻¹)⁻¹ = qS 7 := by
    rw [Subgroup.mem_centralizer_singleton_iff.1 hk.1]
    group
  have hcc : k₁ * qS 32 * k₁⁻¹ = k₁ * k₂⁻¹ * c₀ * (k₁ * k₂⁻¹)⁻¹ := by
    rw [hc₂]
    group
  refine ⟨k₁ * k₂⁻¹ * s * (k₁ * k₂⁻¹)⁻¹, ?_, ?_⟩
  · rw [hcc, conj_mul_conj', conj_mul_conj', hsc]
  · rw [conj_mul_conj', hs2, hk7]

theorem square_of_rank_pair_Q
    {y : Sbp} (hyQ : y ∈ Qs) (hy2 : y * y = 1)
    (hyc : y * labelS = labelS * y) (hry : ((βr y) - 1).rank = 2168)
    (hrcy : ((βr (labelS * y)) - 1).rank = 2168) :
    ∃ s : Sbp, s * labelS = labelS * s ∧ s * s = y := by
  obtain ⟨g, hg, hgy⟩ := mem_jClass_seven_of_rank hyQ hy2 hry
  have e7 : g * y * g⁻¹ = qS 7 := by rw [hgy]; group
  have hc' : g * labelS * g⁻¹ ∈ aSet := by
    refine ⟨?_, conj_mem_jClass hg labelS_mem_jClass, ?_, ?_⟩
    · have h := conj_mem_Qs (g := g⁻¹) (Jbar.op.inv_mem hg) labelS_mem
      rwa [inv_inv] at h
    · rw [← e7, conj_mul_conj', conj_mul_conj', hyc]
    · rw [← e7, conj_mul_conj', rank_conj_inv, hrcy]
  obtain ⟨s, hsc, hs2⟩ := sq_of_mem_aSet hc'
  exact ⟨_, sqrt_conj rfl e7 hsc hs2⟩

theorem square_of_rkH_2168_pair
    {y : vStab cv0} (hyQ : sEquiv.symm (y : Shat) ∈ Qs)
    (hy2 : y * y = 1) (hr : rkH y = 2168) (hr' : rkH (cV0 * y) = 2168) :
    ∃ s : vStab cv0, s * s = y := by
  rw [rkH_cV0_mul] at hr'
  obtain ⟨s, hsc, hs2⟩ :=
    square_of_rank_pair_Q hyQ (mul_self_symm hy2) (commute_labelS_of_mem y) hr hr'
  exact square_of_S hsc hs2

theorem not_mem_dH_of_rkH_2168_pair
    {G : Type*} [Group G] {d : G}
    (ψ : Subgroup.centralizer {d} ≃* vStab cv0)
    (hψ : ψ ⟨d, mem_centralizer_singleton_self d⟩ = cV0) {y : vStab cv0}
    (hyQ : sEquiv.symm (y : Shat) ∈ Qs) (hy2 : y * y = 1) (hr : rkH y = 2168)
    (hr' : rkH (cV0 * y) = 2168) : y ∉ dH ψ := by
  obtain ⟨s, hs⟩ := square_of_rkH_2168_pair hyQ hy2 hr hr'
  exact not_mem_dH_of_square ψ hψ hs (ne_cV0_of_rkH (by rw [hr]; decide))

theorem hY3_native
    {G : Type*} [Group G] {d : G} (ψ : Subgroup.centralizer {d} ≃* vStab cv0)
    (hψ : ψ ⟨d, mem_centralizer_singleton_self d⟩ = cV0) :
    ∀ a : cEdgeFix, cEdgeIncl a ∈ edgeQ → a * a = 1 → rkH (cEdgeFixToH a) = 2168 →
      rkH (cV0 * cEdgeFixToH a) = 2168 → cEdgeFixToH a ∉ dH ψ := by
  intro a haQ ha2 hr hr'
  refine not_mem_dH_of_rkH_2168_pair ψ hψ ?_ ?_ hr hr'
  · rw [coe_cEdgeFixToH]
    exact (symm_mem_centQ haQ).1
  · rw [← map_mul, ha2, map_one]

theorem hY3_native_all :
    ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] {d : G},
    orderOf d = 2 → ∀ ψ : Subgroup.centralizer {d} ≃* vStab cv0,
    ψ ⟨d, mem_centralizer_singleton_self d⟩ = cV0 → 2 ∣ (Subgroup.centralizer {d}).index →
    ∀ a : cEdgeFix, cEdgeIncl a ∈ edgeQ → a * a = 1 → rkH (cEdgeFixToH a) = 2168 →
      rkH (cV0 * cEdgeFixToH a) = 2168 → cEdgeFixToH a ∉ dH ψ :=
  fun _ _ _ _ _ _ ψ hψ _ => hY3_native ψ hψ


end CFSG.Monster.B.GSide
