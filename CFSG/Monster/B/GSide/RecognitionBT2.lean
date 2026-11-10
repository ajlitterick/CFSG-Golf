module

public import CFSG.Monster.B.GSide.CompletionBT2
public import CFSG.Monster.B.GSide.BT2C2
public import CFSG.Monster.B.GSide.NotTwoCentral
public import CFSG.Monster.B.GSide.EdgeAut
public import CFSG.Monster.B.GSide.EdgeDCompat
public import CFSG.Monster.B.GSide.EdgeQCertOrbits
public import CFSG.Monster.B.GSide.HInnerFusionI3
public import CFSG.Monster.B.GSide.TriangleHom1782
public import CFSG.Monster.B.GSide.TwoBCentralizer

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.GSide

open CFSG.Blueprint CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Amalgam

theorem symm_trans_symm_trans_apply {A B C : Type*} [Mul A] [Mul B] [Mul C]
    (ψ : A ≃* C) (e : B ≃* C) (c : C) : ((ψ.trans e.symm).trans e).symm c = ψ.symm c := by
  simp

theorem centralizer_le_range_of_classes
    {G : Type} [Group G] [Finite G] {d : G} (hd1 : d ≠ 1)
    (ψ : Subgroup.centralizer {d} ≃* vStab cv0)
    (hψ : ψ ⟨d, mem_centralizer_singleton_self d⟩ = cV0) (Φ : Shat →* G)
    (hΦ : ∀ a : vStab cv0, Φ a = psiInvHom ψ a) (hGold : GoldschmidtTheorem)
    (hΓ2D : conjugatesOf d ∩ (Φ.range : Set G) = dZero Φ.range d →
      (∀ s : Shat, orderOf s = 2 → rankS s = 2048 → Subgroup.centralizer {Φ s} ≤ Φ.range) →
      ∀ s : Shat, orderOf s = 2 → rankS s = 2168 → Subgroup.centralizer {Φ s} ≤ Φ.range) :
    ∀ t ∈ Φ.range, orderOf t = 2 → Subgroup.centralizer {t} ≤ Φ.range := by
  have hΦc : Φ (cV0 : Shat) = d := map_cV0_of_psiInvHom hd1 ψ hΦ
  have hinj : Function.Injective Φ := injective_of_map_cV0_ne_one Φ (hΦc.symm ▸ hd1)
  have hDM := conjugatesOf_inter_range_native hd1 ψ hψ Φ hΦ
  have h2B := centralizer_le_range_of_rankS_eq_2048 hd1 ψ Φ hΦ hDM hGold
  intro t ht ht2
  obtain ⟨s, rfl⟩ := MonoidHom.mem_range.1 ht
  have hs : orderOf s = 2 := (orderOf_injective Φ hinj s).symm.trans ht2
  rcases rankS_mem_of_orderOf hs with h | h | h | h
  · have hc := isConj_iff.1 (isConj_of_rankS_eq orderOf_coe_cV0 hs (rankS_cV0.trans h.symm))
    obtain ⟨g, rfl⟩ := hc
    have e : Φ (g * (cV0 : Shat) * g⁻¹) = Φ g * d * (Φ g)⁻¹ :=
      (map_mul_mul_inv Φ g _).trans (congrArg (fun y => Φ g * y * (Φ g)⁻¹) hΦc)
    exact e ▸ (completion_centralizer hd1 ψ Φ hΦ).2.2 _ (MonoidHom.mem_range.2 ⟨g, rfl⟩)
  · exact h2B s hs h
  · exact centralizer_le_range_of_rankS_eq_2158_of_gold hd1 ψ Φ hΦ hDM hGold hs h
  · exact hΓ2D hDM h2B s hs h

theorem exists_edge_triangle_homs
    {G : Type} [Group G] [Finite G] {d : G} (hd : orderOf d = 2)
    (ψ : Subgroup.centralizer {d} ≃* vStab cv0)
    (hψ : ψ ⟨d, mem_centralizer_singleton_self d⟩ = cV0)
    (hidx : 2 ∣ (Subgroup.centralizer {d}).index)
    (hY3 : ∀ ψ' : Subgroup.centralizer {d} ≃* vStab cv0,
      ψ' ⟨d, mem_centralizer_singleton_self d⟩ = cV0 →
      ∀ a : cEdgeFix, cEdgeIncl a ∈ edgeQ → a * a = 1 → rkH (cEdgeFixToH a) = 2168 →
        rkH (cV0 * cEdgeFixToH a) = 2168 → cEdgeFixToH a ∉ dH ψ')
    (hQ4 : ∀ K : Subgroup cEdgeStab, K ≤ edgeMB edgeU0 →
      (∀ m ∈ edgeMB edgeU0, ∀ k ∈ K, m * k * m⁻¹ ∈ K) →
      Nat.card K = 2 ^ 23 → (∀ k ∈ K, (∀ k' ∈ K, k * k' = k' * k) ↔
        k = 1 ∨ k = cEdgeIncl (lamV0 * lamW0)) → K = edgeQ)
    (hWit : ∃ y, ∃ hs : clabelS y ∈ cvSetStab {cv0, cw0},
      IsTriB 0 (clabelS y) ∧ (⟨clabelS y, hs⟩ : cEdgeStab) ∈ edgeQ) :
    ∃ ψ' : Subgroup.centralizer {d} ≃* vStab cv0,
      ψ' ⟨d, mem_centralizer_singleton_self d⟩ = cV0 ∧
      ∃ (φe : cvSetStab {cv0, cw0} →* G) (φt : cvSetStab {cv0, cw0, cu 0} →* G),
        (∀ a (ha : a ∈ vStab cv0) (hb : a ∈ cvSetStab {cv0, cw0}),
          psiInvHom ψ' ⟨a, ha⟩ = φe ⟨a, hb⟩) ∧
        (∀ a (ha : a ∈ vStab cv0) (hb : a ∈ cvSetStab {cv0, cw0, cu 0}),
          psiInvHom ψ' ⟨a, ha⟩ = φt ⟨a, hb⟩) ∧
        (∀ a (ha : a ∈ cvSetStab {cv0, cw0}) (hb : a ∈ cvSetStab {cv0, cw0, cu 0}),
          φe ⟨a, ha⟩ = φt ⟨a, hb⟩) := by
  have hE := exists_edge_hom ψ hψ hd hidx cEdgeFix_mulAut_eq_inner_beta
    cEdgeFix_commutator_index center_cEdgeFix_le_commutator cEdgeFix_beta_not_inner
  obtain ⟨ψ', -, hψ', hψ'e, φe, hinj, hext, hswap⟩ := hE
  have he : ((ψ'.symm lamW0H : Subgroup.centralizer {d}) : G) =
      ((ψ.symm lamW0H : Subgroup.centralizer {d}) : G) := congrArg Subtype.val hψ'e
  have hφsw : ∀ b : cEdgeStab, (b : Shat) ∉ cEdgeFix →
      φe b * d * (φe b)⁻¹ = ((ψ'.symm lamW0H : Subgroup.centralizer {d}) : G) ∧
      φe b * ((ψ'.symm lamW0H : Subgroup.centralizer {d}) : G) * (φe b)⁻¹ = d := fun b hb =>
    he ▸ hswap b hb
  have hN1D : ∀ a : cEdgeFix, cEdgeIncl a ∈ edgeQ → cEdgeFixToH a ∈ dH ψ' →
      a = lamV0 ∨ a = lamW0 ∨ a ∈ edgeL := fun a haQ haD =>
    hN1D_of_Y3 ψ' hψ' (hY3 ψ' hψ') haQ
      ((orderOf_injective _ cEdgeFixToH_injective a).symm.trans (orderOf_of_mem_dH ψ' hd haD))
      haD
  have hQ2 := edgeQCert_Q2
  obtain ⟨hOunion, hOorb, hOdisj, hOcard, hOlab⟩ := hQ2
  have hDC := edge_dCompat_label ψ' hψ' hd hidx φe hinj hext hφsw edgeQ edgeQ_normal
    natCard_edgeQ lamV0_mem_edgeQ (fun q hq => edgeQ_comm_iff hq) edgeQ_hQ1 edgeO hOunion hOorb
    hOdisj hOcard hOlab edgeL ⟨edgeU0, edgeU0_mem_edgeL, edgeL_eq_class⟩ ncard_edgeL
    (fun a ha => edgeL_subset_RA ha) (fun a ha => mul_mem_edgeL ha)
    ⟨lamV0_not_mem_edgeL, lamW0_not_mem_edgeL⟩ hN1D edgeU0 edgeU0_mem_edgeL
    (edge_hBu edgeU0_mem_edgeL) (edgeMB edgeU0) (fun b => mem_edgeMB_iff)
    (index_edgeMB edgeU0_mem_edgeL) hQ4
  have hve : ∀ a (ha : a ∈ vStab cv0) (hb : a ∈ cvSetStab {cv0, cw0}),
      psiInvHom ψ' ⟨a, ha⟩ = φe ⟨a, hb⟩ := hve_of_edge_hom ψ' φe hext
  have hw := hWit
  obtain ⟨y, hs, hb, hyQ⟩ := hw
  have hyA : clabelS y ∉ cEdgeFix := fun h =>
    cgraph_adj_cv0_cw0.ne ((mem_vStab.1 h.1).symm.trans hb.1)
  have hDC' : ∃ y, ∃ hs : clabelS y ∈ cvSetStab {cv0, cw0},
      IsTriB 0 (clabelS y) ∧ IsConj d (φe ⟨clabelS y, hs⟩) :=
    ⟨y, hs, hb, hDC _ hs hyQ hyA ⟨y, rfl⟩⟩
  have ht := exists_triangleHom_1782 ψ' hψ' φe hve hDC'
  obtain ⟨φt, hvt, het⟩ := ht
  exact ⟨ψ', hψ', φe, φt, hve, hvt, het⟩

theorem recognition_of_inputs
    (hBT2C1 : BT2C1)
    (T : Sylow 2 (vStab cv0)) {β : vStab cv0} {X : Subgroup (vStab cv0)} (hβ2 : β ^ 2 = 1)
    (hβK : β ∉ commutator (vStab cv0)) (hXT : X ≤ T) (hcX : cV0 ∈ X) (hβX : β ∈ X)
    (hXβ : X ≤ Subgroup.centralizer {β}) (hXsyl : Odd (X.relIndex (Subgroup.centralizer {β})))
    (hX : Nat.card X = 2 ^ 26)
    (hZ : ∀ z ∈ X, (∀ y ∈ X, z * y = y * z) → z ∈ centerInfCommutator X ∨
      cV0⁻¹ * z ∈ centerInfCommutator X ∨ β⁻¹ * z ∈ centerInfCommutator X ∨
      (cV0 * β)⁻¹ * z ∈ centerInfCommutator X)
    (hcU : cV0 ∉ centerInfCommutator X) (hβcU : β⁻¹ * cV0 ∉ centerInfCommutator X)
    (hHC5 : ∀ u ∈ centerInfCommutator X, ∃ u' ∈ centerInfCommutator X, u' ≠ u ∧
      IsConj (cV0 * β * u) (cV0 * β * u'))
    (hHC5ii : ∀ u ∈ centerInfCommutator X, u ≠ 1 →
      cV0 * u ∈ RA ∨ (u * u = 1 ∧ rkH u = 2048 ∧ rkH (cV0 * u) ≠ 1860))
    (hY3 : ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] {d : G}, orderOf d = 2 →
      ∀ ψ : Subgroup.centralizer {d} ≃* vStab cv0,
      ψ ⟨d, mem_centralizer_singleton_self d⟩ = cV0 → 2 ∣ (Subgroup.centralizer {d}).index →
      ∀ a : cEdgeFix, cEdgeIncl a ∈ edgeQ → a * a = 1 → rkH (cEdgeFixToH a) = 2168 →
        rkH (cV0 * cEdgeFixToH a) = 2168 → cEdgeFixToH a ∉ dH ψ)
    (hQ4 : ∀ K : Subgroup cEdgeStab, K ≤ edgeMB edgeU0 →
      (∀ m ∈ edgeMB edgeU0, ∀ k ∈ K, m * k * m⁻¹ ∈ K) →
      Nat.card K = 2 ^ 23 → (∀ k ∈ K, (∀ k' ∈ K, k * k' = k' * k) ↔
        k = 1 ∨ k = cEdgeIncl (lamV0 * lamW0)) → K = edgeQ)
    (hWit : ∃ y, ∃ hs : clabelS y ∈ cvSetStab {cv0, cw0},
      IsTriB 0 (clabelS y) ∧ (⟨clabelS y, hs⟩ : cEdgeStab) ∈ edgeQ)
    (hGold : GoldschmidtTheorem)
    (hΓ2D : ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] {d : G}, d ≠ 1 →
      ∀ (ψ : Subgroup.centralizer {d} ≃* vStab cv0) (Φ : Shat →* G),
      (∀ a : vStab cv0, Φ a = psiInvHom ψ a) →
      conjugatesOf d ∩ (Φ.range : Set G) = dZero Φ.range d →
      (∀ s : Shat, orderOf s = 2 → rankS s = 2048 → Subgroup.centralizer {Φ s} ≤ Φ.range) →
      ∀ s : Shat, orderOf s = 2 → rankS s = 2168 → Subgroup.centralizer {Φ s} ≤ Φ.range)
    (d₀ : NativeSporadic.B) (hd₀ : orderOf d₀ = 2)
    (hrank : Matrix.rank (d₀.val.val - 1) = 1860)
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (d : G) (hd : orderOf d = 2)
    (hcentralizer : Nonempty (Subgroup.centralizer ({d} : Set G) ≃*
      Subgroup.centralizer ({d₀} : Set NativeSporadic.B))) :
    Nonempty (G ≃* NativeSporadic.B) := by
  obtain ⟨φ⟩ := hcentralizer
  have hd1 : d ≠ 1 := fun h => by
    rw [h, orderOf_one] at hd
    exact absurd hd (by norm_num)
  have hψ : psiOf hd₀ hrank φ ⟨d, mem_centralizer_singleton_self d⟩ = cV0 :=
    psiOf_self hd₀ hrank hd1 φ
  have hG2 : Nat.card G ≠ 2 := fun h => by
    have h1 := (Subgroup.centralizer {d}).card_le_card_group
    rw [natCard_centralizer_of_equiv (psiOf hd₀ hrank φ), h] at h1
    exact absurd h1 (by norm_num)
  have hidx := two_dvd_index_centralizer_of_native_of_isSimpleGroup hG2 (psiOf hd₀ hrank φ) hψ T
    hβ2 hβK hXT hcX hβX hXβ hXsyl hZ hcU hβcU hHC5 (hc_of_rkH _ hψ hHC5ii)
    (inner_involution_he hX)
  have hET := exists_edge_triangle_homs hd (psiOf hd₀ hrank φ) hψ hidx
    (fun ψ' hψ' => hY3 G hd ψ' hψ' hidx) hQ4 hWit
  obtain ⟨ψ', hψ', φe, φt, hve, hvt, het⟩ := hET
  have hpsi : ∀ a : vStab cv0, psiInvHom (psiOf hd₀ hrank
      (ψ'.trans (centralizerVStabEquiv hd₀ hrank).symm)) a = psiInvHom ψ' a := fun a =>
    congrArg Subtype.val (symm_trans_symm_trans_apply ψ' (centralizerVStabEquiv hd₀ hrank) a)
  exact gside_reduction_bt2 hBT2C1 bt2C2 d₀ hd₀ hrank
    (ψ'.trans (centralizerVStabEquiv hd₀ hrank).symm) φe φt
    (fun a ha hb => (hpsi _).trans (hve a ha hb)) (fun a ha hb => (hpsi _).trans (hvt a ha hb))
    het (fun Φ hΦv _ _ => centralizer_le_range_of_classes hd1 ψ' hψ' Φ
      (fun a => (hΦv a).trans (hpsi a)) hGold
      (hΓ2D G hd1 ψ' Φ (fun a => (hΦv a).trans (hpsi a))))

end CFSG.Monster.B.GSide
