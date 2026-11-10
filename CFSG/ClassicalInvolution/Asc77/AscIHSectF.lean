module

public import CFSG.ClassicalInvolution.Asc77.AscIHSectE
public import CFSG.ClassicalInvolution.Asc77.AscT7AU
public import CFSG.ClassicalInvolution.RouteD.G2D4Ih8Free

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic AscE184Sect ExactLayer
open scoped commutatorElement

section Generation

variable {G : Type} [Group G]

theorem omegaGen_restrictFamily_eq_top (Λ : Set (Subgroup G)) (Y : Subgroup G)
    (hY : (⨆ L ∈ Λ, L) = Y) : omegaGen (restrictFamily Λ Y) = ⊤ := by
  have hle : ∀ L ∈ Λ, L ≤ Y := fun L hL => hY ▸ le_iSup₂ (f := fun L (_ : L ∈ Λ) => L) L hL
  apply Subgroup.map_injective Y.subtype_injective
  rw [Subgroup.map_top, Subgroup.range_subtype]
  refine le_antisymm (Subgroup.map_subtype_le _) ?_
  calc Y = ⨆ L ∈ Λ, L := hY.symm
    _ ≤ (omegaGen (restrictFamily Λ Y)).map Y.subtype := by
      refine iSup₂_le fun L hL => ?_
      have hmem : L.subgroupOf Y ≤ omegaGen (restrictFamily Λ Y) :=
        le_omegaGen ⟨L, hL, hle L hL, rfl⟩
      calc L = (L.subgroupOf Y).map Y.subtype :=
            (Subgroup.map_subgroupOf_eq_of_le (hle L hL)).symm
        _ ≤ _ := Subgroup.map_mono hmem

theorem omegaGen_quotFamily_eq_top (Λ : Set (Subgroup G)) (N : Subgroup G) [N.Normal]
    (h : omegaGen Λ = ⊤) : omegaGen (quotFamily Λ N) = ⊤ := by
  have hle : omegaGen Λ ≤ (omegaGen (quotFamily Λ N)).comap (QuotientGroup.mk' N) := by
    refine iSup₂_le fun L hL => ?_
    exact (Subgroup.le_comap_map _ L).trans
      (Subgroup.comap_mono (le_omegaGen (map_mem_quotFamily hL)))
  rw [h, top_le_iff] at hle
  refine eq_top_iff.mpr fun x _ => ?_
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N x
  have hg : g ∈ (omegaGen (quotFamily Λ N)).comap (QuotientGroup.mk' N) := by
    rw [hle]; exact Subgroup.mem_top g
  exact hg

end Generation

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {A : Subgroup G}

theorem dstarConnected_quot_of_twinTriple_gen (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hΩ : HypOmegaMod p f Ω) (hA : IsPGroup 2 ↥A) (hY : sectionHull Ω A ≠ ⊤)
    (hBelow : CITBelowU p f (Nat.card G)) (h3s : T3.Thm3SectBelow p f (Nat.card G))
    (hMF : DStarConnectedTwinGen p f)
    (htt : TwinTriple (quotFamily (restrictFamily (sectionFamily Ω A) (sectionHull Ω A))
      (classicalInvolutionOddCore ↥(sectionHull Ω A)))) :
    T3.DStarConnected (quotFamily (restrictFamily (sectionFamily Ω A) (sectionHull Ω A))
      (classicalInvolutionOddCore ↥(sectionHull Ω A))) := by
  set Y := sectionHull Ω A with hYdef
  set Λ : Set (Subgroup ↥Y) := restrictFamily (sectionFamily Ω A) Y with hΛdef
  set N₀ : Subgroup ↥Y := classicalInvolutionOddCore ↥Y with hN₀def
  have hN₀odd : Odd (Nat.card N₀) := CFSG.ComponentClassification.OddCore.odd_card ↥Y
  have hΛ : HypOmegaMod p f Λ := hypOmegaMod_sectionFamily hp hq hΩ hA
  have hΛ' : HypOmegaMod p f (quotFamily Λ N₀) := oddQuotHyp p f hp hq ↥Y Λ hΛ N₀ hN₀odd
  have hltY := natCard_lt_of_ne_top hY
  have hlt : Nat.card (↥Y ⧸ N₀) < Nat.card G := by
    have h1 : Nat.card (↥Y ⧸ N₀) ≤ Nat.card ↥Y :=
      Nat.le_of_dvd Nat.card_pos (Subgroup.index_dvd_card N₀)
    omega
  have hOq : classicalInvolutionOddCore (↥Y ⧸ N₀) = ⊥ :=
    CFSG.ComponentClassification.OddCore.quotient_corefree ↥Y
  have hgenΛ : omegaGen Λ = ⊤ := omegaGen_restrictFamily_eq_top (sectionFamily Ω A) Y rfl
  have hgenQ : omegaGen (quotFamily Λ N₀) = ⊤ := omegaGen_quotFamily_eq_top Λ N₀ hgenΛ
  by_contra hdis
  have hΛA : ∀ L ∈ Λ, AEmpty Λ L := h3s hp hq ↥Y hltY Λ hΛ hdis
  have hAΛ' := aEmpty_quotFamily hp hq hΛ hΛ' hN₀odd hΛA
  obtain ⟨K₀, hK₀, -⟩ := id htt
  rcases dichotomy_of_thm4 hp hq (thm4Below_of_citBelow hBelow) hlt hΛ' hOq hAΛ' hK₀ with hc | horb
  · exact hdis (T3.dstarConnected_of_pivot hK₀ hc)
  · have htrans : ∀ K ∈ quotFamily Λ N₀, ∀ L ∈ quotFamily Λ N₀,
        ∃ g : ↥Y ⧸ N₀, conjSub g K = L := by
      intro K hK L hL
      obtain ⟨y₁, hy₁⟩ := horb K hK
      obtain ⟨y₂, hy₂⟩ := horb L hL
      exact ⟨y₂ * y₁⁻¹, by rw [conjSub_mul, ← hy₁, conjSub_inv_conjSub, hy₂]⟩
    obtain ⟨D⟩ := ih8_exists_omegaLie hBelow hΛ'.conjInvariant hΛ'.classical ⟨_, hK₀⟩ hOq hlt
    exact hdis (hMF _ _ ⟨hΛ', hOq, hgenQ, htrans, hAΛ'⟩ D htt)

section Main

variable [IsSimpleGroup G] {K K' J W : Subgroup G} {z u t : G}
  (h : Hyp21 p f Ω K K' z u J t W)

include h

theorem tqMembers_subset_dstarComp_gen (hMF : DStarConnectedTwinGen p f)
    (h3s : ∀ n, CITBelowU p f n → T3.Thm3SectBelow p f n) (h3 : C21_3 p f)
    (hα : alphaOf (Subgroup.closure ({u, z} : Set G)) = ⊥) :
    ∀ M ∈ tqMembers Ω (t * z), M ∈ dstarComp Ω K := by
  have hp : p ≠ 2 := h.std.stand.odd
  have hq : 5 ≤ p ^ f := h.std.stand.five
  have hΩ : HypOmegaMod p f Ω := h.std.stand.hyp
  have hK : K ∈ Ω := h.std.stand.mem
  have hK'Ω : K' ∈ Ω := h.std.hK'.1
  have hJΩ : J ∈ Ω := h.hJ.1
  have hz : IsUniqueInvolution K z := h.std.hz
  have hzK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hz h.std.hK'
  have hBelow : CITBelowU p f (Nat.card G) := h.std.stand.below f hq
  set c : G := t * z with hcdef
  have hc2 : c * c = 1 := h.tz_sq
  have hc1 : c ≠ 1 := h.tz_ne_one
  have hcA : IsPGroup 2 (Subgroup.zpowers c) := isPGroup_zpowers_of_sq_eq_one hc2
  set A : Subgroup G := Subgroup.zpowers c with hAdef
  obtain ⟨S, R, R', T, hRsyl, hR'syl, hTsyl, hRS, hR'S, hTS, hRR', hRT, hR'T⟩ :=
    exists_twinSylow hp hq hΩ hK hz h.std.hK' h.std.hne h.hJ
  have h8R : 8 ≤ Nat.card R := hΩ.eight_le_of_mem_RSet hp (mem_RSet_of_isSylow2In hK hRsyl)
  have h8T : 8 ≤ Nat.card T := hΩ.eight_le_of_mem_RSet hp (mem_RSet_of_isSylow2In hJΩ hTsyl)
  have hzR : z ∈ R := mem_of_isUniqueInvolution_of_isPGroup hz hRsyl.1 hRsyl.2.1 (by omega)
  have htT : t ∈ T := mem_of_isUniqueInvolution_of_isPGroup h.ht hTsyl.1 hTsyl.2.1 (by omega)
  have hcomm_tz : ∀ x : G, x * t = t * x → x * z = z * x → x * c = c * x := by
    intro x hxt hxz
    calc x * c = (x * t) * z := by rw [hcdef]; group
      _ = (t * x) * z := by rw [hxt]
      _ = t * (x * z) := by group
      _ = t * (z * x) := by rw [hxz]
      _ = c * x := by rw [hcdef]; group
  have hRc : R ≤ Subgroup.centralizer ({c} : Set G) := fun r hr =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (hcomm_tz r (hRT r hr t htT) (hz.commute_of_mem (hRsyl.1 hr)).symm)
  have hR'c : R' ≤ Subgroup.centralizer ({c} : Set G) := fun r hr =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (hcomm_tz r (hR'T r hr t htT) (hzK'.commute_of_mem (hR'syl.1 hr)).symm)
  have hTc : T ≤ Subgroup.centralizer ({c} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (hcomm_tz x (h.ht.commute_of_mem (hTsyl.1 hx)).symm (hRT z hzR x hx).symm)
  have hKt : K ∈ tqMembers Ω c :=
    (mem_tqMembers_iff_exists_sylow hp hq hΩ hcA).mpr ⟨hK, R, hRsyl, hRc⟩
  have hK't : K' ∈ tqMembers Ω c :=
    (mem_tqMembers_iff_exists_sylow hp hq hΩ hcA).mpr ⟨hK'Ω, R', hR'syl, hR'c⟩
  have hJt : J ∈ tqMembers Ω c :=
    (mem_tqMembers_iff_exists_sylow hp hq hΩ hcA).mpr ⟨hJΩ, T, hTsyl, hTc⟩
  have hKm : K ∈ sectionMembers Ω A := by rw [hAdef, sectionMembers_zpowers]; exact hKt
  have hK'm : K' ∈ sectionMembers Ω A := by rw [hAdef, sectionMembers_zpowers]; exact hK't
  have hJm : J ∈ sectionMembers Ω A := by rw [hAdef, sectionMembers_zpowers]; exact hJt
  have hRA : IsSylow2In R (secMember A K) :=
    (isSylow2In_secMember_iff hcA hKm.2).mpr (mem_fixedSylows_zpowers_iff.mpr ⟨hRsyl, hRc⟩)
  have hR'A : IsSylow2In R' (secMember A K') :=
    (isSylow2In_secMember_iff hcA hK'm.2).mpr (mem_fixedSylows_zpowers_iff.mpr ⟨hR'syl, hR'c⟩)
  have hTA : IsSylow2In T (secMember A J) :=
    (isSylow2In_secMember_iff hcA hJm.2).mpr (mem_fixedSylows_zpowers_iff.mpr ⟨hTsyl, hTc⟩)
  have hJK : J ≠ K := (h.hJ.2 K (mem_twinSet_self hK hz)).2.1
  have hJK' : J ≠ K' := (h.hJ.2 K' h.std.hK').2.1
  have hT2 : IsPGroup 2 ↥T := hTsyl.2.1
  have hTz : T ≤ Subgroup.centralizer ({z} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hRT z hzR x hx).symm
  have hTNK : T ≤ Subgroup.normalizer (K : Set G) :=
    hΩ.le_normalizer_of_le_centralizer hp hq hK hJΩ (Ne.symm hJK) hz hTsyl.1 hT2 (by omega) hTz
  have hTNK' : T ≤ Subgroup.normalizer (K' : Set G) :=
    hΩ.le_normalizer_of_le_centralizer hp hq hK'Ω hJΩ (Ne.symm hJK') hzK' hTsyl.1 hT2
      (by omega) hTz
  have hcent : Subgroup.centralizer ((A : Subgroup G) : Set G) =
      Subgroup.centralizer ({c} : Set G) := by
    rw [hAdef, CFSG.ClassicalInvolution.Balance.Bootstrap.centralizer_zpowers_eq_singleton']
  have hTCA : T ≤ Subgroup.centralizer ((A : Subgroup G) : Set G) := by rw [hcent]; exact hTc
  have hTNKA : T ≤ Subgroup.normalizer ((secMember A K : Subgroup G) : Set G) := fun x hx =>
    mem_normalizer_iff_conjSub_eq.mpr (conjSub_secMember_of_normalizer (hTCA hx) (hTNK hx))
  have hTNK'A : T ≤ Subgroup.normalizer ((secMember A K' : Subgroup G) : Set G) := fun x hx =>
    mem_normalizer_iff_conjSub_eq.mpr (conjSub_secMember_of_normalizer (hTCA hx) (hTNK' hx))
  set Y : Subgroup G := sectionHull Ω A with hYdef
  have hKY : secMember A K ≤ Y := le_sectionHull hKm
  have hK'Y : secMember A K' ≤ Y := le_sectionHull hK'm
  have hJY : secMember A J ≤ Y := le_sectionHull hJm
  have hΛ : HypOmegaMod p f (restrictFamily (sectionFamily Ω A) Y) :=
    hypOmegaMod_sectionFamily hp hq hΩ hcA
  have hN₀odd : Odd (Nat.card (classicalInvolutionOddCore ↥Y)) :=
    CFSG.ComponentClassification.OddCore.odd_card ↥Y
  have hΛ' : HypOmegaMod p f (quotFamily (restrictFamily (sectionFamily Ω A) Y)
      (classicalInvolutionOddCore ↥Y)) :=
    oddQuotHyp p f hp hq ↥Y _ hΛ _ hN₀odd
  have htt : TwinTriple (quotFamily (restrictFamily (sectionFamily Ω A) Y)
      (classicalInvolutionOddCore ↥Y)) :=
    twinTriple_quot hp hΛ' hN₀odd (subgroupOf_secMember_mem hKm)
      (twinSet_subgroupOf hKY hK'Y (secMember_mem_twinSet hp hΩ hcA hKm hK'm h.std.hK'))
      (subgroupOf_secMember_mem hJm) (hRA.subgroupOf hKY) (hR'A.subgroupOf hK'Y)
      (hTA.subgroupOf hJY) (commutes_subgroupOf hRR') (commutes_subgroupOf hRT)
      (commutes_subgroupOf hR'T) (le_normalizer_subgroupOf_of_le hKY hTNKA)
      (le_normalizer_subgroupOf_of_le hK'Y hTNK'A)
  have hYtop : Y ≠ ⊤ := by
    intro htop
    have hle : Y ≤ Subgroup.centralizer ({c} : Set G) := by
      have := sectionHull_le_centralizer Ω A
      rwa [hcent] at this
    rw [htop, top_le_iff] at hle
    have hcomm : ∀ g : G, g * c = c * g := fun g =>
      Subgroup.mem_centralizer_singleton_iff.mp (hle ▸ Subgroup.mem_top g)
    obtain ⟨V, hV, -⟩ := IsSylow2In.exists_ge (isPGroup_two_bot (G := G)) (bot_le : ⊥ ≤ K)
    have hVR : V ∈ RSet Ω := mem_RSet_of_isSylow2In hK hV
    obtain ⟨x, -, y, -, hxy⟩ := (hΩ.isQuatSub_of_mem_RSet hp hVR).exists_not_commute
    exact hc1 (T7A.eq_one_of_central ⟨x, y, hxy⟩ hcomm)
  have hconn := dstarConnected_quot_of_twinTriple_gen hp hq hΩ hcA hYtop hBelow (h3s _ hBelow)
    hMF htt
  have hinv : ∀ n : ↥Y, n ∈ classicalInvolutionOddCore ↥Y → (n : G) ∈ sigmaStarNorm Ω K := by
    intro n hn
    have hnO : (n : G) ∈ oddCoreOf Y := ⟨n, hn, rfl⟩
    have hnC := oddCoreOf_sectionHull_le hΩ A hnO
    rw [hcent] at hnC
    have hnz : (n : G) * z = z * (n : G) := h.oddCore_centralizer_tz_comm h3 hα hnC
    have hnzn : (n : G) * z * (n : G)⁻¹ = z := by
      calc (n : G) * z * (n : G)⁻¹ = (z * (n : G)) * (n : G)⁻¹ := by rw [hnz]
        _ = z := by group
    have hKn : conjSub (n : G) K ∈ twinSet Ω K :=
      ⟨hΩ.conjInvariant n K hK, z, hz, hnzn ▸ hz.conj (n : G)⟩
    exact T7A.mem_sigmaStarNorm_of_conj hΩ.conjInvariant hK
      (AscE186.mem_dstarComp_of_twin hp hΩ hK hKn)
  have hJd : J ∈ dstarComp Ω K :=
    Relation.ReflTransGen.single ⟨hJΩ, Or.inl (T3.omegaNbr_subset_omegaStarNbr hp hΩ K
      (h.hJ.2 K (mem_twinSet_self hK hz)))⟩
  intro M hM
  have hMs : M ∈ sectionMembers Ω A := by rw [hAdef, sectionMembers_zpowers]; exact hM
  obtain ⟨n, hn, J', hJ', hJ'd, rfl⟩ :=
    exists_conj_mem_dstarComp_of_conn hp hq hΩ hcA hJm hconn hMs
  exact ((mem_sigmaStarNorm_iff.mp (hinv n hn)) J').mp (hJd.trans hJ'd)

theorem centralizer_tz_le_sigmaStarNorm_gen (hMF : DStarConnectedTwinGen p f)
    (h3s : ∀ n, CITBelowU p f n → T3.Thm3SectBelow p f n) (h3 : C21_3 p f)
    (hα : alphaOf (Subgroup.closure ({u, z} : Set G)) = ⊥) :
    Subgroup.centralizer ({t * z} : Set G) ≤ sigmaStarNorm Ω K := by
  have hp : p ≠ 2 := h.std.stand.odd
  have hΩ : HypOmegaMod p f Ω := h.std.stand.hyp
  have hK : K ∈ Ω := h.std.stand.mem
  have hJΩ : J ∈ Ω := h.hJ.1
  have hJd : J ∈ dstarComp Ω K :=
    Relation.ReflTransGen.single ⟨hJΩ, Or.inl (T3.omegaNbr_subset_omegaStarNbr hp hΩ K
      (h.hJ.2 K (mem_twinSet_self hK h.std.hz)))⟩
  intro g hg
  have hgJ : conjSub g J ∈ tqMembers Ω (t * z) :=
    conjSub_mem_tqMembers hΩ.conjInvariant hg h.mem_tqMembers_tz_J
  have h1 : conjSub g J ∈ dstarComp Ω K :=
    tqMembers_subset_dstarComp_gen h hMF h3s h3 hα _ hgJ
  have hJJ : conjSub g J ∈ dstarComp Ω J := (T3.mem_dstarComp_symm hK hJd).2.trans h1
  have hgJn : g ∈ sigmaStarNorm Ω J :=
    T7A.mem_sigmaStarNorm_of_conj hΩ.conjInvariant hJΩ hJJ
  rwa [sigmaStarNorm_congr (T7A.dstarComp_eq_of_mem hK hJd)] at hgJn


end Main

variable (p f) in
theorem c21_13_star_of_sections_gen (hMF : DStarConnectedTwinGen p f)
    (h3s : ∀ n, CITBelowU p f n → T3.Thm3SectBelow p f n) (h3 : C21_3 p f) :
    C21_13_star p f := by
  intro G _ _ _ Ω K K' z u J t W h hα hD heq
  apply hD
  have hp : p ≠ 2 := h.std.stand.odd
  have hq : 5 ≤ p ^ f := h.std.stand.five
  have hΩ : HypOmegaMod p f Ω := h.std.stand.hyp
  have hcA : IsPGroup 2 (Subgroup.zpowers (t * z)) := isPGroup_zpowers_of_sq_eq_one h.tz_sq
  refine iSup₂_le fun R hR => iSup_le fun hRc => ?_
  obtain ⟨J', hJ'Ω, hRJ'⟩ := exists_isSylow2In_of_mem_RSet hR
  have hJ't : J' ∈ tqMembers Ω (t * z) :=
    (mem_tqMembers_iff_exists_sylow hp hq hΩ hcA).mpr ⟨hJ'Ω, R, hRJ', hRc⟩
  have hdst := tqMembers_subset_dstarComp_gen h hMF h3s h3 hα J' hJ't
  rw [← heq] at hdst
  exact hRJ'.1.trans (le_iSup₂_of_le J' hdst le_rfl)

variable (p f) in
theorem c21_17_tz_of_sections_gen (hMF : DStarConnectedTwinGen p f)
    (h3s : ∀ n, CITBelowU p f n → T3.Thm3SectBelow p f n) (h3 : C21_3 p f) :
    C21_17_tz p f := by
  intro G _ _ _ Ω K K' z u J t W h hα _ _
  exact centralizer_tz_le_sigmaStarNorm_gen h hMF h3s h3 hα


end CFSG.ClassicalInvolution.Asc77
