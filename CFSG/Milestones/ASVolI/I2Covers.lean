module

public import CFSG.Milestones.ASVolI.I2
public import Certificates.Certificate7280
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCover2
public import CFSG.Goldschmidt75.Transfer
public import CFSG.Quasithin.Background.E2KGSz8CoverPf
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.M22Centralizer
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.Cov9
public import Certificates.Certificate7285
public import Certificates.Certificate7286
public import CFSG.Quasithin.H13.L32NZ4Q8Q8
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverExternal
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverExternalConjugacy
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.PumpHSLift
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog5CovHS
public import CFSG.LieType.Steinberg.CentralExt.GriessG2FourRootLifts
public import CFSG.LocalAnalysis.EvenSmallLie.GTwoFour.Outer
public import CFSG.LieType.Multipliers.G24Cover
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk47eOmega
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverRigid
public import Certificates.Certificate7290
public import Certificates.Certificate7291
public import CFSG.Quasithin.Vol2.KGFactC31RuCoverDbl
public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.FactsRu
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicRuCover
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.RuSzNormal
public import CFSG.Quasithin.Vol2.KGFactC31RuM64
public import CFSG.GH74.GLS.IVK.Lifted.TwoCoverRank
public import CFSG.Quasithin.H13.L32AKG1468g
public import CFSG.LargeExtraspecial.BridgeNat
public import Certificates.Certificate7295
public import Certificates.Certificate7296
public import CFSG.Sporadic.J4.QT2LocProof
public import CFSG.Sporadic.Schreier.J4SCommGenBase1
public import Certificates.Kernel.Sporadic.Fi22.C2068
public import Certificates.Kernel.Sporadic.Fi22.C3151
public import CFSG.Certificates.Kernel.LocalCompTits.Span
public import CFSG.GH74.GLS.Defs
public import CFSG.Goldschmidt75.WeakClosure
public import CFSG.LieType.Steinberg.CentralExt.F4E8Multiplier
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4CoverMult
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4OneComp
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCenterBase
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCyclicCenterModel
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsParabolicGen
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsStandard
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverModels
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicGenCensus
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicRu
public import CFSG.LocalAnalysis.EvenSporadicStandard.Common
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoRu.HypOne
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.InnerCoverBase
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilySmall
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1AutModel
public import CFSG.Quasithin.Background.F9Basic
public import CFSG.Quasithin.H13.L32AKG1468c
public import CFSG.Quasithin.H13.L32AKG1468f
public import CFSG.Quasithin.H13.L32NStatements
public import CFSG.Quasithin.Recognition.G23TypeDefs
public import CFSG.RankThree.OrthogonalInvolutions.SuzukiTypes
public import Certificates.Kernel.J4Count.FixCE
public import Certificates.Kernel.J4Count.FixCPairBase1

public section

namespace CFSG.ASVolI

open CFSG.Open
section PartBurnsideI2a_part12

theorem burnsideI2a_pRank_three_cover_alternating {n : ℕ} (hn6 : 6 ≤ n) (hn8 : n ≤ 8)
    {K : Type} [Group K] [Finite K] [Group.IsPerfect K]
    (π : K →* alternatingGroup (Fin n)) (hπ : Function.Surjective π)
    (hC : π.ker ≤ Subgroup.center K) : CFSG.pRank 3 K = 2 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Q₀, hQ₀⟩ := CFSG.SectionRank.exists_sylow_eq_sylowThreeAlt hn6 hn8
  obtain ⟨P, hP⟩ := Sylow.mapSurjective_surjective hπ 3 Q₀
  have hmap : (P : Subgroup K).map π = (Q₀ : Subgroup (alternatingGroup (Fin n))) := by
    rw [← Sylow.coe_mapSurjective hπ P, hP]
  have hQel : CFSG.Open.IsElemAbelian 3 (Q₀ : Subgroup (alternatingGroup (Fin n))) :=
    hQ₀ ▸ CFSG.SectionRank.isElemAbelian_sylowThreeAlt hn6
  have hQcard : Nat.card (Q₀ : Subgroup (alternatingGroup (Fin n))) = 3 ^ 2 :=
    hQ₀ ▸ CFSG.SectionRank.card_sylowThreeAlt hn6
  obtain ⟨C⟩ : Nonempty (Sylow 3 π.ker) := inferInstance
  obtain ⟨-, hCle⟩ :=
    CFSG.ShultStronglyClosedTI.central_cover_elementary_rank_two_sylow_kernel_bound
      π hπ hC C Q₀ hQel hQcard
  set A : Subgroup K := (C : Subgroup π.ker).map π.ker.subtype
  have hAZ : A ≤ Subgroup.center K := (Subgroup.map_subtype_le _).trans hC
  have hAP : A ≤ (P : Subgroup K) :=
    CFSG.ShultStronglyClosedTI.central_pSubgroup_le_sylow P A hAZ (C.isPGroup'.map π.ker.subtype)
  have hker := CFSG.ShultStronglyClosedTI.central_kernel_sylow_restriction π hC C P
  have hder := CFSG.ShultStronglyClosedTI.central_kernel_sylow_restriction_le_derived π hC C P
  have hkercard :
      Nat.card (π.subgroupMap (P : Subgroup K)).ker = Nat.card (C : Subgroup π.ker) := by
    rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAP).toEquiv]
    exact (Nat.card_congr ((C : Subgroup π.ker).equivMapOfInjective π.ker.subtype
      Subtype.coe_injective).toEquiv).symm
  have hcardP : Nat.card (P : Subgroup K) = 3 ^ 2 * Nat.card (C : Subgroup π.ker) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (π.subgroupMap (P : Subgroup K)).ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _
        (MonoidHom.subgroupMap_surjective π (P : Subgroup K))).toEquiv,
      Nat.card_congr (MulEquiv.subgroupCongr hmap).toEquiv, hQcard, hkercard]
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 C.isPGroup'
  have hk1 : k ≤ 1 := by
    by_contra h
    push Not at h
    have : 3 ^ 2 ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) h
    omega
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top, ← (CFSG.SectionRank.pRank_sylow P).1]
  apply le_antisymm
  · refine CFSG.SectionRank.pRank_le (by norm_num) fun E hEP hE => ?_
    by_contra hlt
    push Not at hlt
    have hEle : Nat.card E ≤ Nat.card (P : Subgroup K) := Subgroup.card_le_of_le hEP
    interval_cases k
    · rw [hk] at hcardP
      omega
    · rw [hk] at hcardP
      have hdvd : Nat.card E ∣ 27 := by
        have := Subgroup.card_dvd_of_le hEP
        rwa [show Nat.card (P : Subgroup K) = 27 by omega] at this
      have hE27 : Nat.card E = 27 := by
        have h27 : Nat.card E ≤ 27 := Nat.le_of_dvd (by norm_num) hdvd
        generalize Nat.card E = d at hdvd h27 hlt
        interval_cases d <;> omega
      have hEP' : E = (P : Subgroup K) :=
        Subgroup.eq_of_le_of_card_ge hEP (by omega)
      have hcomm : IsMulCommutative ↥(P : Subgroup K) := hEP' ▸ hE.1
      have hbot : (π.subgroupMap (P : Subgroup K)).ker ≤ ⊥ := by
        have := hder
        rwa [commutator_eq_bot] at this
      have h1 : Nat.card (π.subgroupMap (P : Subgroup K)).ker = 1 := by
        rw [le_bot_iff.mp hbot]
        exact Subgroup.card_bot
      omega
  · by_contra hlt
    push Not at hlt
    have hnc : ¬ IsCyclic ↥(P : Subgroup K) := by
      intro hcyc
      have h1 : IsCyclic ↥((P : Subgroup K).map π) :=
        isCyclic_of_surjective (π.subgroupMap (P : Subgroup K))
          (MonoidHom.subgroupMap_surjective π (P : Subgroup K))
      rw [hmap] at h1
      obtain ⟨g, hg⟩ := isCyclic_iff_exists_orderOf_eq_natCard.1 h1
      have hg3 : g ^ 3 = 1 := Subtype.ext (hQel.2 _ g.2)
      have := orderOf_dvd_of_pow_eq_one hg3
      rw [hg, hQcard] at this
      omega
    haveI : Fact (IsPGroup 3 ↥(P : Subgroup K)) := ⟨P.isPGroup'⟩
    obtain ⟨S, -, hScard, hSel⟩ := CFSG.lemma_4_5_a (p := 3) (by norm_num) hnc
    have hSel' := (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 3 S).1 hSel
    have h2 := CFSG.SectionRank.le_pRank (by norm_num : 1 < 3)
      (Subgroup.map_subtype_le S)
      (CFSG.SectionRank.isElemAbelian_map hSel' (P : Subgroup K).subtype)
      (by rw [Subgroup.card_map_of_injective (P : Subgroup K).subtype_injective, hScard])
    omega

theorem burnsideI2a_cover_of_equiv {K S : Type} [Group K] [Group S]
    (e : K ⧸ Subgroup.center K ≃* S) :
    ∃ π : K →* S, Function.Surjective π ∧ π.ker = Subgroup.center K :=
  ⟨e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K)),
    e.surjective.comp (QuotientGroup.mk'_surjective _), by ext g; simp⟩

theorem burnsideI2a_cover_equiv {S : Type} [Group S] [Finite S] [Group.IsPerfect S]
    (hM : IsCyclic (CFSG.RankThree.PerfectCover.hopfMultiplier S))
    [Finite (CFSG.RankThree.PerfectCover.hopfMultiplier S)]
    {E₁ E₂ : Type} [Group E₁] [Group E₂] [Finite E₁] [Finite E₂] [Group.IsPerfect E₁]
    [Group.IsPerfect E₂] (π₁ : E₁ →* S) (π₂ : E₂ →* S) (hπ₁ : Function.Surjective π₁)
    (hπ₂ : Function.Surjective π₂) (hC₁ : π₁.ker ≤ Subgroup.center E₁)
    (hC₂ : π₂.ker ≤ Subgroup.center E₂) (hcard : Nat.card π₁.ker = Nat.card π₂.ker) :
    Nonempty (E₁ ≃* E₂) := by
  haveI : Finite (CFSG.RankThree.PerfectCover.HopfCover S) := by
    refine Nat.finite_of_card_ne_zero ?_
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup
        (CFSG.RankThree.PerfectCover.hopfMultiplier S),
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective
        (CFSG.RankThree.PerfectCover.hopfCoverMap S)
        CFSG.RankThree.PerfectCover.hopfCoverMap_surjective).toEquiv]
    exact Nat.mul_ne_zero Nat.card_pos.ne' Nat.card_pos.ne'
  haveI := hM
  set h₁ := CFSG.RankThree.PerfectCover.hopfLift π₁ hπ₁ hC₁
  set h₂ := CFSG.RankThree.PerfectCover.hopfLift π₂ hπ₂ hC₂
  have hs₁ : Function.Surjective h₁ :=
    CFSG.RankThree.PerfectCover.hopfLift_surjective π₁ hπ₁ hC₁
  have hs₂ : Function.Surjective h₂ :=
    CFSG.RankThree.PerfectCover.hopfLift_surjective π₂ hπ₂ hC₂
  set M := CFSG.RankThree.PerfectCover.hopfMultiplier S
  have hle₁ : h₁.ker ≤ M := fun x hx => by
    change CFSG.RankThree.PerfectCover.hopfCoverMap S x = 1
    rw [← CFSG.RankThree.PerfectCover.comp_hopfLift π₁ hπ₁ hC₁, MonoidHom.comp_apply]
    rw [MonoidHom.mem_ker] at hx
    rw [hx, map_one]
  have hle₂ : h₂.ker ≤ M := fun x hx => by
    change CFSG.RankThree.PerfectCover.hopfCoverMap S x = 1
    rw [← CFSG.RankThree.PerfectCover.comp_hopfLift π₂ hπ₂ hC₂, MonoidHom.comp_apply]
    rw [MonoidHom.mem_ker] at hx
    rw [hx, map_one]
  have hcardE₁ : Nat.card E₁ = Nat.card S * Nat.card π₁.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup π₁.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective π₁ hπ₁).toEquiv]
  have hcardE₂ : Nat.card E₂ = Nat.card S * Nat.card π₂.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup π₂.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective π₂ hπ₂).toEquiv]
  have hcardU₁ : Nat.card (CFSG.RankThree.PerfectCover.HopfCover S) =
      Nat.card E₁ * Nat.card h₁.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup h₁.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective h₁ hs₁).toEquiv]
  have hcardU₂ : Nat.card (CFSG.RankThree.PerfectCover.HopfCover S) =
      Nat.card E₂ * Nat.card h₂.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup h₂.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective h₂ hs₂).toEquiv]
  have hcardN : Nat.card h₁.ker = Nat.card h₂.ker := by
    have hpos : 0 < Nat.card S * Nat.card π₁.ker := Nat.mul_pos Nat.card_pos Nat.card_pos
    have h := hcardU₁.symm.trans hcardU₂
    rw [hcardE₁, hcardE₂, ← hcard] at h
    exact Nat.eq_of_mul_eq_mul_left hpos h
  have hsub : h₁.ker.subgroupOf M = h₂.ker.subgroupOf M := by
    rw [IsCyclic.subgroup_eq_iff_card_eq,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle₁).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle₂).toEquiv]
    exact hcardN
  have hker : h₁.ker = h₂.ker := by
    have := congrArg (Subgroup.map M.subtype) hsub
    rwa [Subgroup.map_subgroupOf_eq_of_le hle₁, Subgroup.map_subgroupOf_eq_of_le hle₂] at this
  exact ⟨((QuotientGroup.quotientKerEquivOfSurjective h₁ hs₁).symm.trans
    (QuotientGroup.quotientMulEquivOfEq hker)).trans
      (QuotientGroup.quotientKerEquivOfSurjective h₂ hs₂)⟩

theorem burnsideI2a_isPerfect_sl2 {F : Type} [Field F] [Finite F] (h4 : 4 ≤ Nat.card F) :
    Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) F) := by
  classical
  haveI : Fintype F := Fintype.ofFinite F
  obtain ⟨a, -, ha⟩ : ∃ a ∈ (Finset.univ : Finset F), a ∉ ({0, 1, -1} : Finset F) :=
    Finset.exists_mem_notMem_of_card_lt_card (by
      rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
      exact lt_of_le_of_lt Finset.card_le_three (by omega))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ha
  obtain ⟨ha0, ha1, ha2⟩ := ha
  refine ⟨Matrix.SL2.commutator_eq_top ha0 fun h => ?_⟩
  rcases sq_eq_one_iff.mp h with h | h
  · exact ha1 h
  · exact ha2 h

theorem burnsideI2a_natCard_center_sl2 {F : Type} [Field F] (h2 : (2 : F) ≠ 0) :
    Nat.card (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)) = 2 := by
  classical
  have hneg : (-1 : Matrix.SpecialLinearGroup (Fin 2) F) ≠ 1 := by
    intro h
    have h1 := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) F =>
      (A : Matrix (Fin 2) (Fin 2) F) 0 0) h
    simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one] at h1
    simp at h1
    exact h2 (by linear_combination -h1)
  have hmem : ∀ A : Matrix.SpecialLinearGroup (Fin 2) F,
      A ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) ↔ A = 1 ∨ A = -1 := by
    intro A
    rw [Matrix.SpecialLinearGroup.mem_center_iff]
    constructor
    · rintro ⟨r, hr, hrA⟩
      rw [Fintype.card_fin] at hr
      rcases sq_eq_one_iff.mp hr with rfl | rfl
      · left
        ext i j
        rw [← hrA]
        fin_cases i <;> fin_cases j <;> simp
      · right
        ext i j
        rw [← hrA]
        fin_cases i <;> fin_cases j <;> simp
    · rintro (rfl | rfl)
      · refine ⟨1, by simp, ?_⟩
        ext i j
        fin_cases i <;> fin_cases j <;> simp
      · refine ⟨-1, by norm_num, ?_⟩
        ext i j
        fin_cases i <;> fin_cases j <;> simp
  rw [Nat.card_eq_two_iff]
  refine ⟨⟨1, (hmem 1).mpr (Or.inl rfl)⟩, ⟨-1, (hmem (-1)).mpr (Or.inr rfl)⟩,
    fun h => hneg (congrArg Subtype.val h).symm, ?_⟩
  ext ⟨A, hA⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
  rcases (hmem A).mp hA with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem burnsideI2a_psl_five_alternating :
    Nonempty
      (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 5) ≃* alternatingGroup (Fin 5)) := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  haveI : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 5)) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by rw [Nat.card_zmod]; norm_num)
  have hSL : Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod 5)) = 120 := by
    rw [Matrix.card_SL_field (𝔽 := ZMod 5) 2, ZMod.card, Fin.prod_univ_two]
    norm_num
  have h60 : Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 5)) = 60 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup
      (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) (ZMod 5)))
    rw [burnsideI2a_natCard_center_sl2 (Ring.two_ne_zero (by
      rw [ZMod.ringChar_zmod_n]; norm_num)), hSL] at h
    change 120 = Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 5)) * 2 at h
    omega
  exact CFSG.QuasithinUnique.nonempty_mulEquiv_alternatingGroup_five_of_card_sixty h60

theorem burnsideI2a_sl2_cover {F : Type} [Field F] (h2 : (2 : F) ≠ 0) {S : Type} [Group S]
    (e : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F ≃* S) :
    ∃ π : Matrix.SpecialLinearGroup (Fin 2) F →* S, Function.Surjective π ∧
      π.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) ∧ Nat.card π.ker = 2 := by
  have hker : (e.toMonoidHom.comp (QuotientGroup.mk'
      (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)))).ker =
      Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) := by
    ext g
    simp
  refine ⟨e.toMonoidHom.comp (QuotientGroup.mk'
      (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F))),
    e.surjective.comp (QuotientGroup.mk'_surjective _), hker.le, ?_⟩
  rw [hker]
  exact burnsideI2a_natCard_center_sl2 h2

theorem burnsideI2a_card_center_eq_two {K : Type} [Group K] [Finite K] [Group.IsPerfect K]
    {d : ℕ} (hd : 5 ≤ d) (π : K →* alternatingGroup (Fin d)) (hπ : Function.Surjective π)
    (hker : π.ker = Subgroup.center K) (h2 : IsPGroup 2 (Subgroup.center K))
    (hZ : Subgroup.center K ≠ ⊥) : Nat.card π.ker = 2 := by
  refine le_antisymm
    (CFSG.LocalAnalysis.ComponentInitial.alternating_perfect_central_two_kernel_order_at_most_two
      hd π hπ hker.le (hker ▸ h2)) ?_
  rw [hker]
  exact (Subgroup.one_lt_card_iff_ne_bot _).mpr hZ

theorem burnsideI2a_I_2_2_one {K : Type} [Group K] [Finite K]
    (hK : CFSG.IsQuasisimple K) (hZ : Subgroup.center K ≠ ⊥) :
    IsPGroup 2 (Subgroup.center K) →
      (Nonempty (K ⧸ Subgroup.center K ≃* alternatingGroup (Fin 5)) →
        Nonempty (K ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 5))) ∧
      (Nonempty (K ⧸ Subgroup.center K ≃* alternatingGroup (Fin 6)) →
        Nonempty (K ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 3 2))) := by
  intro h2
  haveI : Group.IsPerfect K := hK.1
  refine ⟨fun ⟨e⟩ => ?_, fun ⟨e⟩ => ?_⟩
  ·
    haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    obtain ⟨π, hπ, hker⟩ := burnsideI2a_cover_of_equiv e
    have hcard := burnsideI2a_card_center_eq_two (by norm_num) π hπ hker h2 hZ
    obtain ⟨ePSL⟩ := burnsideI2a_psl_five_alternating
    obtain ⟨π', hπ', hker', hcard'⟩ := burnsideI2a_sl2_cover (F := ZMod 5)
      (Ring.two_ne_zero (by rw [ZMod.ringChar_zmod_n]; norm_num)) ePSL
    haveI : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) (ZMod 5)) :=
      burnsideI2a_isPerfect_sl2 (by rw [Nat.card_zmod]; norm_num)
    haveI : Group.IsPerfect (alternatingGroup (Fin 5)) :=
      ⟨commutator_alternatingGroup_eq_top (by simp)⟩
    obtain ⟨hMcyc, hMcard⟩ := CFSG.Alternating.Multipliers.hopfMultiplier_alternatingGroup_five
    haveI : Finite (CFSG.RankThree.PerfectCover.hopfMultiplier (alternatingGroup (Fin 5))) :=
      Nat.finite_of_card_ne_zero (by rw [hMcard]; norm_num)
    exact burnsideI2a_cover_equiv hMcyc π π' hπ hπ' hker.le hker' (hcard.trans hcard'.symm)
  ·
    have hF : Nat.card (GaloisField 3 2) = 9 := by
      rw [GaloisField.card 3 2 (by norm_num)]
      norm_num
    obtain ⟨π, hπ, hker⟩ := burnsideI2a_cover_of_equiv e
    have hcard := burnsideI2a_card_center_eq_two (by norm_num) π hπ hker h2 hZ
    obtain ⟨ePSL⟩ :=
      CFSG.Sporadic.Recognition.JankoWong.nonempty_mulEquiv_alternatingGroup_six_of_card_nine hF
    have h2F : (2 : GaloisField 3 2) ≠ 0 :=
      Ring.two_ne_zero (by rw [ringChar.eq (GaloisField 3 2) 3]; norm_num)
    obtain ⟨π', hπ', hker', hcard'⟩ := burnsideI2a_sl2_cover (F := GaloisField 3 2) h2F ePSL
    haveI : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 3 2)) :=
      burnsideI2a_isPerfect_sl2 (by rw [hF]; norm_num)
    haveI : Group.IsPerfect (alternatingGroup (Fin 6)) :=
      ⟨commutator_alternatingGroup_eq_top (by simp)⟩
    obtain ⟨hMcyc, hMcard⟩ := CFSG.Alternating.Multipliers.hopfMultiplier_alternatingGroup_six
    haveI : Finite (CFSG.RankThree.PerfectCover.hopfMultiplier (alternatingGroup (Fin 6))) :=
      Nat.finite_of_card_ne_zero (by rw [hMcard]; norm_num)
    exact burnsideI2a_cover_equiv hMcyc π π' hπ hπ' hker.le hker' (hcard.trans hcard'.symm)


section

end

end PartBurnsideI2a_part12

section PartBurnsideI22P3_cert

open CFSG.ComponentClassification.GrSLit.L34Facts CFSG.ComponentClassification.PSL3Four
  CFSG.PSL3Four in
structure burnsideI22P3_Pres {K : Type} [Group K] (q : K →* Equiv.Perm (Fin 42)) : Prop where
  mem : ∀ x, q x ∈ S
  surj : ∀ s ∈ S, ∃ x, q x = s
  ker : q.ker = Subgroup.center K

open CFSG.ComponentClassification.PSL3Four in
@[expose] noncomputable def burnsideI22P3_qOf {K : Type} [Group K] (e : K ⧸ Subgroup.center K ≃* ↥S) :
    K →* Equiv.Perm (Fin 42) :=
  S.subtype.comp (e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K)))

open CFSG.ComponentClassification.PSL3Four in
theorem burnsideI22P3_qOf_apply {K : Type} [Group K] (e : K ⧸ Subgroup.center K ≃* ↥S) (x : K) :
    burnsideI22P3_qOf e x = ((e (QuotientGroup.mk x) : ↥S) : Equiv.Perm (Fin 42)) := rfl

open CFSG.ComponentClassification.GrSLit.L34Facts CFSG.ComponentClassification.PSL3Four
  CFSG.PSL3Four in
theorem burnsideI22P3_pres_qOf {K : Type} [Group K] (e : K ⧸ Subgroup.center K ≃* ↥S) :
    burnsideI22P3_Pres (burnsideI22P3_qOf e) := by
  refine ⟨fun x => (e (QuotientGroup.mk' (Subgroup.center K) x)).2, fun s hs => ?_, ?_⟩
  · obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective _ (e.symm ⟨s, hs⟩)
    refine ⟨x, ?_⟩
    rw [burnsideI22P3_qOf_apply]
    change ((e (QuotientGroup.mk' (Subgroup.center K) x) : ↥S) : Equiv.Perm (Fin 42)) = s
    rw [hx]
    simp
  · ext x
    rw [MonoidHom.mem_ker, burnsideI22P3_qOf_apply]
    constructor
    · intro h
      have h1 : e (QuotientGroup.mk x) = 1 := Subtype.ext h
      have h2 := e.injective (h1.trans (map_one e).symm)
      exact (QuotientGroup.eq_one_iff x).1 h2
    · intro h
      have h2 : (QuotientGroup.mk x : K ⧸ Subgroup.center K) = 1 :=
        (QuotientGroup.eq_one_iff x).2 h
      rw [h2]
      simp

open CFSG.ComponentClassification.GrSLit.L34Facts CFSG.ComponentClassification.PSL3Four
  CFSG.PSL3Four in
theorem burnsideI22P3_pres_of_equiv {K : Type} [Group K] (e : K ⧸ Subgroup.center K ≃* ↥S) :
    ∃ q : K →* Equiv.Perm (Fin 42), burnsideI22P3_Pres q :=
  ⟨_, burnsideI22P3_pres_qOf e⟩

open CFSG.ComponentClassification.GrSLit.L34Facts CFSG.ComponentClassification.PSL3Four
  CFSG.PSL3Four in

open CFSG.ComponentClassification.GrSLit.L34Facts CFSG.ComponentClassification.PSL3Four
  CFSG.PSL3Four in
theorem burnsideI22P3_qsetting
    {K : Type} [Group K]
    {q : K →* Equiv.Perm (Fin 42)} (hq : burnsideI22P3_Pres q) (hperf : commutator K = ⊤)
    (hZ2 : IsPGroup 2 (Subgroup.center K)) :
    ∃ l : CFSG.LieType.Multipliers.L34.Cover →* K, IsQSetting q l := by
  obtain ⟨l, hl, hls⟩ := exists_lam hperf q hq.mem hq.surj (hq.ker ▸ le_refl _)
  refine ⟨l, hq.mem, hq.surj, hq.ker, fun e he h3 => ?_, hl, hls⟩
  rw [hq.ker] at he
  obtain ⟨k, hk⟩ := hZ2 ⟨e, he⟩
  have hk' : e ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have hd : orderOf e ∣ 3 := orderOf_dvd_of_pow_eq_one h3
  have hd2 : orderOf e ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
  have : orderOf e ∣ Nat.gcd 3 (2 ^ k) := Nat.dvd_gcd hd hd2
  have hcop : Nat.gcd 3 (2 ^ k) = 1 := by
    apply Nat.Coprime.pow_right
    norm_num
  rw [hcop] at this
  exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 this)

open CFSG.ComponentClassification.GrSLit.L34Facts CFSG.ComponentClassification.PSL3Four
  CFSG.PSL3Four in


open CFSG.ComponentClassification.GrSLit.L34Facts CFSG.ComponentClassification.PSL3Four
  CFSG.PSL3Four in

open CFSG.ComponentClassification.GrSLit.L34Facts CFSG.ComponentClassification.PSL3Four
  CFSG.PSL3Four in

open CFSG.ComponentClassification.GrSLit.L34Facts CFSG.ComponentClassification.PSL3Four
  CFSG.PSL3Four CFSG.ASVolI.ChIJK in


open CFSG.ComponentClassification.GrSLit.L34Facts CFSG.ComponentClassification.PSL3Four
  CFSG.PSL3Four in


open CFSG.ComponentClassification.GrSLit.L34Facts CFSG.ComponentClassification.PSL3Four
  CFSG.PSL3Four in

open CFSG.PSL3Four.Native CFSG.ComponentClassification.GrSLit.L34Facts
  CFSG.ComponentClassification.PSL3Four in

open CFSG.PSL3Four.Native CFSG.ComponentClassification.GrSLit.L34Facts
  CFSG.ComponentClassification.PSL3Four in

open CFSG.PSL3Four.Native CFSG.ComponentClassification.GrSLit.L34Facts
  CFSG.ComponentClassification.PSL3Four in

open CFSG.PSL3Four.Native CFSG.ComponentClassification.GrSLit.L34Facts
  CFSG.ComponentClassification.PSL3Four in

open CFSG.PSL3Four.Native CFSG.ComponentClassification.GrSLit.L34Facts
  CFSG.ComponentClassification.PSL3Four in


open CFSG.PSL3Four.Native CFSG.ComponentClassification.GrSLit.L34Facts
  CFSG.ComponentClassification.PSL3Four in

open CFSG.PSL3Four.Native CFSG.ComponentClassification.GrSLit.L34Facts
  CFSG.ComponentClassification.PSL3Four in


open CFSG.ComponentClassification.GrSLit.L34Facts CFSG.ComponentClassification.PSL3Four
  CFSG.PSL3Four CFSG.ASVolI.ChIJK in


open CFSG.ComponentClassification.GrSLit.L34Facts CFSG.ComponentClassification.PSL3Four
  CFSG.PSL3Four CFSG.ASVolI.ChIJK in

open CFSG.ComponentClassification.GrSLit.L34Facts CFSG.ComponentClassification.PSL3Four
  CFSG.PSL3Four CFSG.ASVolI.ChIJK in

open CFSG.ComponentClassification.GrSLit.L34Facts CFSG.ComponentClassification.PSL3Four
  CFSG.PSL3Four in
theorem burnsideI22P3_conj_T0
    {s : Equiv.Perm (Fin 42)} (hsS : s ∈ S) (hs2 : s * s = 1) (hs1 : s ≠ 1) :
    ∃ g ∈ S, g⁻¹ * s * g ∈ T0 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set a : ↥S := ⟨s, hsS⟩ with ha
  have ha2 : a * a = 1 := Subtype.ext hs2
  have ha1 : a ≠ 1 := fun h => hs1 (congrArg Subtype.val h)
  have hord : orderOf a = 2 := by
    refine orderOf_eq_prime ?_ ha1
    rw [pow_two]
    exact ha2
  have hP : IsPGroup 2 ↥(Subgroup.zpowers a) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord]; norm_num)
  obtain ⟨Q, hQ⟩ := hP.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq S sylowT0 Q
  refine ⟨g, g.2, ?_⟩
  have h1 : a ∈ ((g • sylowT0 : Sylow 2 S) : Subgroup S) := by
    rw [hg]
    exact hQ (Subgroup.mem_zpowers a)
  exact (mem_smul_sylowT0_iff g a).1 h1

open CFSG.ComponentClassification.GrSLit.L34Facts CFSG.ComponentClassification.PSL3Four
  CFSG.PSL3Four CFSG.PSL3Four.Native in
theorem burnsideI22P3_invol_idx {k : ℕ} (hk : k < 64)
    (h : wordPerm (tg k) * wordPerm (tg k) = 1) : k = 0 ∨ ∃ d ∈ sqData, d.1 = k := by
  have hinv := coverParts.invols k hk
  have h1 : comp 42 (wordTab (tg k)) (wordTab (tg k)) = idTab 42 :=
    ((tabRep_wordTab _).comp (tabRep_wordTab _)).tab_eq (h ▸ TabRep.idTab)
  rw [h1, beq_self_eq_true] at hinv
  have h2 := hinv.symm
  simp only [Bool.or_eq_true, beq_iff_eq, List.contains_eq_any_beq, List.any_eq_true,
    List.mem_map] at h2
  rcases h2 with h2 | ⟨x, ⟨d, hd, rfl⟩, hx⟩
  · exact Or.inl h2
  · exact Or.inr ⟨d, hd, by simpa using hx.symm⟩

open CFSG.ComponentClassification.GrSLit.L34Facts CFSG.ComponentClassification.PSL3Four
  CFSG.PSL3Four CFSG.ASVolI.ChIJK in
theorem burnsideI22P3_clause_b1
    {K : Type} [Group K] [Finite K] (hK : CFSG.IsQuasisimple K)
    (hmodel : StatedClassicalModel (K ⧸ Subgroup.center K) .PSL 3 2 2)
    (hZ2 : IsPGroup 2 (Subgroup.center K)) : InvolutionsLift K := by
  obtain ⟨e⟩ := nonempty_equiv_of_stated _ hmodel
  obtain ⟨q, hq⟩ := burnsideI22P3_pres_of_equiv e
  obtain ⟨l, hQ⟩ := burnsideI22P3_qsetting hq hK.1.commutator_eq_top hZ2
  intro t ht2 ht1
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective t
  have hx2 : x * x ∈ Subgroup.center K := by
    have : ((x * x : K) : K ⧸ Subgroup.center K) = 1 := by
      rw [QuotientGroup.mk_mul]
      simpa [pow_two] using ht2
    exact (QuotientGroup.eq_one_iff _).1 this
  have hs2 : q x * q x = 1 := by
    rw [← map_mul]
    have : x * x ∈ q.ker := hq.ker ▸ hx2
    exact this
  have hs1 : q x ≠ 1 := by
    intro h
    apply ht1
    have : x ∈ q.ker := h
    rw [hq.ker] at this
    exact (QuotientGroup.eq_one_iff _).2 this
  obtain ⟨g, hgS, hgT⟩ := burnsideI22P3_conj_T0 (hq.mem x) hs2 hs1
  obtain ⟨k, hk, hkt⟩ := exists_tg hgT
  have hk2 : wordPerm (tg k) * wordPerm (tg k) = 1 := by
    rw [hkt]
    calc g⁻¹ * q x * g * (g⁻¹ * q x * g) = g⁻¹ * (q x * q x) * g := by group
      _ = 1 := by rw [hs2]; group
  rcases burnsideI22P3_invol_idx hk hk2 with rfl | ⟨d, hd, rfl⟩
  · exfalso
    apply hs1
    have h1 : g⁻¹ * q x * g = 1 := by rw [← hkt]; exact wordPerm_tg_zero
    calc q x = g * (g⁻¹ * q x * g) * g⁻¹ := by group
      _ = 1 := by rw [h1]; group
  · obtain ⟨xg, hxg⟩ := hq.surj g hgS
    have hw2 := hQ.ilift_mul_self hd
    have hqw : q (ilift l d) = g⁻¹ * q x * g := by
      rw [hQ.q_ilift (by omega), hkt]
    refine ⟨xg * ilift l d * xg⁻¹, ?_, ?_⟩
    · rw [pow_two]
      calc xg * ilift l d * xg⁻¹ * (xg * ilift l d * xg⁻¹)
          = xg * (ilift l d * ilift l d) * xg⁻¹ := by group
        _ = 1 := by rw [hw2]; group
    · rw [QuotientGroup.eq]
      have : (xg * ilift l d * xg⁻¹)⁻¹ * x ∈ q.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, map_mul, map_mul, map_inv, hxg, hqw]
        group
      rw [hq.ker] at this
      exact this

open scoped commutatorElement in
open CFSG.ComponentClassification.GrSLit.L34Facts CFSG.ComponentClassification.PSL3Four
  CFSG.PSL3Four in

open CFSG.ComponentClassification.GrSLit.L34Facts CFSG.ComponentClassification.PSL3Four
  CFSG.PSL3Four CFSG.ASVolI.ChIJK in

open CFSG.ComponentClassification.GrSLit.L34Facts CFSG.ComponentClassification.PSL3Four
  CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.LieType.Multipliers.L34 in

open CFSG.ComponentClassification.GrSLit.L34Facts CFSG.ComponentClassification.PSL3Four
  CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.LieType.Multipliers.L34 in


open CFSG.ComponentClassification.GrSLit.L34Facts CFSG.ComponentClassification.PSL3Four
  CFSG.ASVolI.ChIJK in

section


end

end PartBurnsideI22P3_cert

section PartBurnsideI22P46

section


end


structure burnsideI22P46_BData {K : Type} [Group K] (t y : K) (φ : K →* Equiv.Perm (Fin 22))
    (S0 : Subgroup (Equiv.Perm (Fin 22))) (h a : Equiv.Perm (Fin 22))
    (Al : Set (Equiv.Perm (Fin 22))) (Ns : Subgroup (Equiv.Perm (Fin 22))) : Prop where
  t_central : t ∈ Subgroup.center K
  t_sq : t * t = 1
  t_ne : t ≠ 1
  center : ∀ x ∈ Subgroup.center K, x = 1 ∨ x = t
  ker : ∀ x, φ x = 1 ↔ x = 1 ∨ x = t
  y_sq : y * y = 1
  S0_range : S0 ≤ φ.range
  S0_card : Nat.card S0 = 128
  S0_cent : ∀ s ∈ S0, s * φ y = φ y * s
  Sy : ∀ p : K, φ p ∈ S0 → p * y = y * p
  Cs_card : Nat.card ↥(φ.range ⊓ Subgroup.centralizer ({φ y} : Set (Equiv.Perm (Fin 22)))) = 384
  h_range : h ∈ φ.range
  h_cent : h * φ y = φ y * h
  h_cube : h * h * h = 1
  h_ne : h ≠ 1
  Al_root : ∀ g ∈ Al, g * g = φ y
  Al_sq : ∀ g ∈ Al, ∀ p : K, φ p = g → p * p = y
  Ns_le : Ns ≤ S0
  Ns_S0 : ∀ s ∈ S0, ∀ n ∈ Ns, s * n * s⁻¹ ∈ Ns
  Ns_h : ∀ n ∈ Ns, h * n * h⁻¹ ∈ Ns
  a_mem : a ∈ Ns
  a_comm : a * h * a⁻¹ * h⁻¹ ∈ Al
  uniq : ∀ g ∈ S0, g * g = φ y → h⁻¹ * g * h ∈ S0 → g ∈ Al

section BData

variable {K : Type} [Group K] {t y : K} {φ : K →* Equiv.Perm (Fin 22)}
  {S0 : Subgroup (Equiv.Perm (Fin 22))} {h a : Equiv.Perm (Fin 22)}
  {Al : Set (Equiv.Perm (Fin 22))} {Ns : Subgroup (Equiv.Perm (Fin 22))}


theorem burnsideI22P46_BData.exists_lift (D : burnsideI22P46_BData t y φ S0 h a Al Ns) :
    ∃ g : K, φ g = h ∧ g * g * g = 1 := by
  obtain ⟨g, hg⟩ := D.h_range
  refine ⟨g ^ 4, ?_, ?_⟩
  · rw [map_pow, hg]
    calc h ^ 4 = h * (h * h * h) := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      _ = h := by rw [D.h_cube, mul_one]
  · have h3 : φ (g ^ 3) = 1 := by
      rw [map_pow, hg]
      calc h ^ 3 = h * h * h := by simp only [pow_succ, pow_zero, one_mul]
        _ = 1 := D.h_cube
    rcases (D.ker _).1 h3 with h1 | h1
    · calc g ^ 4 * g ^ 4 * g ^ 4 = (g ^ 3) ^ 4 := by group
        _ = 1 := by rw [h1]; simp
    · calc g ^ 4 * g ^ 4 * g ^ 4 = (g ^ 3) ^ 4 := by group
        _ = (t * t) * (t * t) := by rw [h1]; simp only [pow_succ, pow_zero, one_mul, mul_assoc]
        _ = 1 := by rw [D.t_sq]; simp


theorem burnsideI22P46_BData.conj (D : burnsideI22P46_BData t y φ S0 h a Al Ns) (c : K) :
    burnsideI22P46_BData t (c * y * c⁻¹) (φ.comp (MulAut.conj c⁻¹).toMonoidHom) S0 h a Al Ns := by
  have hφ' : ∀ p : K, (φ.comp (MulAut.conj c⁻¹).toMonoidHom) p = φ (c⁻¹ * p * c) := by
    intro p; simp [MulAut.conj_apply]
  have hφ'y : (φ.comp (MulAut.conj c⁻¹).toMonoidHom) (c * y * c⁻¹) = φ y := by
    rw [hφ']; congr 1; group
  have hrange' : (φ.comp (MulAut.conj c⁻¹).toMonoidHom).range = φ.range := by
    ext g
    constructor
    · rintro ⟨p, rfl⟩
      exact ⟨_, (hφ' p).symm⟩
    · rintro ⟨q, rfl⟩
      exact ⟨c * q * c⁻¹, by rw [hφ']; congr 1; group⟩
  have htc : ∀ x : K, x * t = t * x := fun x => Subgroup.mem_center_iff.1 D.t_central x
  refine ⟨D.t_central, D.t_sq, D.t_ne, D.center, ?_, ?_, ?_, D.S0_card, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, D.Ns_le, D.Ns_S0, D.Ns_h, D.a_mem, D.a_comm, ?_⟩
  · intro x
    rw [hφ', D.ker]
    constructor
    · rintro (h1 | h1)
      · left
        have : c⁻¹ * x * c = 1 := h1
        calc x = c * (c⁻¹ * x * c) * c⁻¹ := by group
          _ = 1 := by rw [this]; group
      · right
        calc x = c * (c⁻¹ * x * c) * c⁻¹ := by group
          _ = c * t * c⁻¹ := by rw [h1]
          _ = t * c * c⁻¹ := by rw [← htc c]
          _ = t := by group
    · rintro (h1 | h1)
      · left; rw [h1]; group
      · right
        rw [h1]
        calc c⁻¹ * t * c = t * c⁻¹ * c := by rw [← htc c⁻¹]
          _ = t := by group
  · calc c * y * c⁻¹ * (c * y * c⁻¹) = c * (y * y) * c⁻¹ := by group
      _ = 1 := by rw [D.y_sq]; group
  · rw [hrange']; exact D.S0_range
  · rw [hφ'y]; exact D.S0_cent
  · intro p hp
    rw [hφ'] at hp
    have := D.Sy _ hp
    calc p * (c * y * c⁻¹) = c * ((c⁻¹ * p * c) * y) * c⁻¹ := by group
      _ = c * (y * (c⁻¹ * p * c)) * c⁻¹ := by rw [this]
      _ = c * y * c⁻¹ * p := by group
  · rw [hrange', hφ'y]; exact D.Cs_card
  · rw [hrange']; exact D.h_range
  · rw [hφ'y]; exact D.h_cent
  · exact D.h_cube
  · exact D.h_ne
  · intro g hg; rw [hφ'y]; exact D.Al_root g hg
  · intro g hg p hp
    rw [hφ'] at hp
    have := D.Al_sq g hg _ hp
    calc p * p = c * ((c⁻¹ * p * c) * (c⁻¹ * p * c)) * c⁻¹ := by group
      _ = c * y * c⁻¹ := by rw [this]
  · intro g hg hgz hgh
    rw [hφ'y] at hgz
    exact D.uniq g hg hgz hgh

end BData


open CFSG.EvenSporadicStandard.M22Std CFSG.QuasithinUnique.Ch1 CFSG.QuasithinUnique.Ch1.M22Cover
  CFSG.QuasithinUnique.Ch1.TitsCover CFSG.Blueprint in


open CFSG.Sporadic.Recognition.M22Multiplier CFSG.Quasithin.HM22 CFSG.Blueprint
  CFSG.EvenSporadicStandard.M22Std CFSG.QuasithinUnique.Ch1.M22Cover
  CFSG.Sporadic.Recognition.CoverRecipe CFSG.LieType.Multipliers CFSG.CosetTable in

open CFSG.Sporadic.Recognition.M22Multiplier CFSG.Quasithin.HM22 CFSG.Blueprint
  CFSG.EvenSporadicStandard.M22Std CFSG.QuasithinUnique.Ch1.M22Cover
  CFSG.Sporadic.Recognition.CoverRecipe CFSG.LieType.Multipliers CFSG.CosetTable in

open CFSG.Sporadic.Recognition.M22Multiplier CFSG.Quasithin.HM22 CFSG.Blueprint
  CFSG.EvenSporadicStandard.M22Std CFSG.QuasithinUnique.Ch1.M22Cover
  CFSG.Sporadic.Recognition.CoverRecipe CFSG.LieType.Multipliers CFSG.CosetTable in

open CFSG.Sporadic.Recognition.M22Multiplier CFSG.Quasithin.HM22 CFSG.Blueprint
  CFSG.EvenSporadicStandard.M22Std CFSG.QuasithinUnique.Ch1.M22Cover
  CFSG.Sporadic.Recognition.CoverRecipe CFSG.LieType.Multipliers CFSG.CosetTable in


open CFSG.Sporadic.Recognition.M22Multiplier CFSG.Quasithin.HM22 CFSG.Blueprint
  CFSG.EvenSporadicStandard.M22Std CFSG.QuasithinUnique.Ch1.M22Cover
  CFSG.Sporadic.Recognition.CoverRecipe CFSG.LieType.Multipliers CFSG.CosetTable in


open CFSG.ASVolI.ChIJK CFSG.Sporadic.Recognition.M22Multiplier CFSG.Quasithin.HM22
  CFSG.Blueprint CFSG.LieType.Multipliers CFSG.CosetTable
  CFSG.Sporadic.Recognition.CoverTransfer in

section


end

end PartBurnsideI22P46

section PartBurnsideI22P5

theorem burnsideI22P5_card_ker_dvd {K X : Type} [Group K] [Finite K] [Group X] [Finite X]
    [Group.IsPerfect K] [Group.IsPerfect X] (π : K →* X) (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center K) {m : ℕ}
    (hm : Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier X) = m) :
    Nat.card π.ker ∣ m := by
  obtain ⟨-, h, -, -, -, hmap, -⟩ :=
    CFSG.RankThree.PerfectCover.perfect_central_kernel_quotient_of_hopf_multiplier π hπ hker
  rw [← hmap, ← hm]
  exact Subgroup.card_map_dvd _ h

theorem burnsideI22P5_card_center_eq_two {K : Type} [Group K] [Finite K]
    (hK : CFSG.IsQuasisimple K) (hZ : Subgroup.center K ≠ ⊥)
    (hM : Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier (K ⧸ Subgroup.center K)) = 2) :
    Nat.card (Subgroup.center K) = 2 := by
  haveI : Group.IsPerfect K := hK.1
  haveI : Group.IsPerfect (K ⧸ Subgroup.center K) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (Subgroup.center K))
      (QuotientGroup.mk'_surjective _)
  have h := burnsideI22P5_card_ker_dvd (QuotientGroup.mk' (Subgroup.center K))
    (QuotientGroup.mk'_surjective _) (by rw [QuotientGroup.ker_mk']) hM
  rw [QuotientGroup.ker_mk'] at h
  rcases (Nat.dvd_prime Nat.prime_two).1 h with h1 | h1
  · exact absurd (Subgroup.card_eq_one.1 h1) hZ
  · exact h1

theorem burnsideI22P5_exists_t {K : Type} [Group K] (h : Nat.card (Subgroup.center K) = 2) :
    ∃ t : K, orderOf t = 2 ∧ Subgroup.center K = Subgroup.zpowers t := by
  obtain ⟨⟨z, hzc⟩, hz1, hu⟩ := (Nat.card_eq_two_iff' (1 : Subgroup.center K)).1 h
  have hz1' : z ≠ 1 := fun h => hz1 (Subtype.ext h)
  have hz2 : z ^ 2 = 1 := by
    have h1 := pow_card_eq_one' (G := Subgroup.center K) (x := (⟨z, hzc⟩ : Subgroup.center K))
    rw [h] at h1
    exact congrArg Subtype.val h1
  refine ⟨z, orderOf_eq_prime hz2 hz1', ?_⟩
  apply le_antisymm
  · intro k hk
    by_cases hk1 : k = 1
    · rw [hk1]; exact Subgroup.one_mem _
    · have := hu ⟨k, hk⟩ (fun h => hk1 (congrArg Subtype.val h))
      have : k = z := congrArg Subtype.val this
      rw [this]; exact Subgroup.mem_zpowers z
  · rw [Subgroup.zpowers_le]; exact hzc

theorem burnsideI22P5_isTwoCentral_map {G H : Type} [Group G] [Finite G] [Group H] (e : G ≃* H)
    {t : G} (ht : CFSG.ASVolI.ChIJK.IsTwoCentralInvolution t) :
    CFSG.ASVolI.ChIJK.IsTwoCentralInvolution (e t) := by
  obtain ⟨h2, h1, T, hT, hc⟩ := ht
  refine ⟨?_, ?_, Sylow.mapSurjective (f := e.toMonoidHom) e.surjective T, ?_, ?_⟩
  · rw [← map_pow, h2, map_one]
  · rw [Ne, MulEquiv.map_eq_one_iff]; exact h1
  · show e t ∈ (T : Subgroup G).map e.toMonoidHom
    exact ⟨t, hT, rfl⟩
  · intro x hx
    have hx' : x ∈ (T : Subgroup G).map e.toMonoidHom := hx
    obtain ⟨y, hy, rfl⟩ := hx'
    show e y * e t = e t * e y
    rw [← map_mul, ← map_mul, hc y hy]

theorem burnsideI22P5_semidirect_centralizer {N G : Type} [Group N] [Group G] (φ : G →* MulAut N)
    (hφ : ∀ g : G, g ≠ 1 → ∀ c : N, φ g ≠ MulAut.conj c) (x : N ⋊[φ] G)
    (hx : ∀ n : N, SemidirectProduct.inl n * x = x * SemidirectProduct.inl n) :
    ∃ z ∈ Subgroup.center N, x = SemidirectProduct.inl z := by
  have hdec := SemidirectProduct.inl_left_mul_inr_right x
  set c : N := x.left with hc
  set b : G := x.right with hb
  have hcomm : ∀ n : N, c * φ b n = n * c := by
    intro n
    have h1 : (SemidirectProduct.inl n : N ⋊[φ] G) *
        (SemidirectProduct.inl c * SemidirectProduct.inr b) =
        (SemidirectProduct.inl c * SemidirectProduct.inr b) * SemidirectProduct.inl n := by
      rw [hdec]; exact hx n
    have e : (SemidirectProduct.inl (φ b n) : N ⋊[φ] G) =
        SemidirectProduct.inr b * SemidirectProduct.inl n * (SemidirectProduct.inr b)⁻¹ := by
      rw [← map_inv]; exact SemidirectProduct.inl_aut b n
    have h2 : (SemidirectProduct.inl (n * c) : N ⋊[φ] G) * SemidirectProduct.inr b =
        SemidirectProduct.inl (c * φ b n) * SemidirectProduct.inr b := by
      calc (SemidirectProduct.inl (n * c) : N ⋊[φ] G) * SemidirectProduct.inr b
          = SemidirectProduct.inl n * (SemidirectProduct.inl c * SemidirectProduct.inr b) := by
            rw [map_mul, mul_assoc]
        _ = (SemidirectProduct.inl c * SemidirectProduct.inr b) * SemidirectProduct.inl n := h1
        _ = SemidirectProduct.inl c * (SemidirectProduct.inr b * SemidirectProduct.inl n *
              (SemidirectProduct.inr b)⁻¹) * SemidirectProduct.inr b := by
            simp only [mul_assoc, inv_mul_cancel, mul_one]
        _ = SemidirectProduct.inl c * SemidirectProduct.inl (φ b n) * SemidirectProduct.inr b := by
            rw [← e]
        _ = SemidirectProduct.inl (c * φ b n) * SemidirectProduct.inr b := by rw [map_mul]
    exact (SemidirectProduct.inl_injective (mul_right_cancel h2)).symm
  by_cases hb1 : b = 1
  · refine ⟨c, ?_, ?_⟩
    · rw [Subgroup.mem_center_iff]
      intro n
      have := hcomm n
      rw [hb1] at this
      simpa using this.symm
    · rw [← hdec, hb1, map_one, mul_one]
  · exfalso
    apply hφ b hb1 c⁻¹
    ext n
    rw [MulAut.conj_apply]
    calc φ b n = c⁻¹ * (c * φ b n) := by group
      _ = c⁻¹ * (n * c) := by rw [hcomm n]
      _ = _ := by group

theorem burnsideI22P5_exists_ext {K : Type} [Group K] [Finite K] (α : K ≃* K)
    (hα : ∀ k, α (α k) = k) (hα1 : ∀ g : K, α ≠ MulAut.conj g) :
    ∃ (H : Type) (_ : Group H) (_ : Finite H) (L : Subgroup H) (_ : L.Normal) (φ : K ≃* L)
      (p : H), p ∉ L ∧ orderOf p = 2 ∧ (∀ k : K, p * (φ k : H) * p⁻¹ = (φ (α k) : H)) ∧
      ∀ g : H, g ∈ Subgroup.centralizer (L : Set H) ↔
        ∃ z ∈ Subgroup.center K, g = ((φ z : L) : H) := by
  classical
  let A : Subgroup (MulAut K) := Subgroup.zpowers α
  let H := K ⋊[A.subtype] A
  haveI : Finite A := inferInstance
  haveI : Finite H := Finite.of_equiv _ (SemidirectProduct.equivProd (N := K) (G := A)
    (φ := A.subtype)).symm
  let L : Subgroup H := (SemidirectProduct.rightHom (N := K) (G := A) (φ := A.subtype)).ker
  let φ : K ≃* L := (MonoidHom.ofInjective (f := SemidirectProduct.inl (N := K) (G := A)
    (φ := A.subtype)) SemidirectProduct.inl_injective).trans
    (MulEquiv.subgroupCongr SemidirectProduct.range_inl_eq_ker_rightHom)
  have hφ : ∀ k : K, ((φ k : L) : H) = SemidirectProduct.inl k := fun k => rfl
  let a : A := ⟨α, Subgroup.mem_zpowers α⟩
  have haa : a * a = 1 := by
    apply Subtype.ext
    ext k
    exact hα k
  have ha1 : a ≠ 1 := fun h => hα1 1 (by
    have := congrArg Subtype.val h
    rw [show (MulAut.conj (1 : K) : MulEquiv K K) = 1 from by ext k; simp]
    exact this)
  let p : H := SemidirectProduct.inr a
  have hpL : p ∉ L := by
    intro h
    have h1 : SemidirectProduct.rightHom (N := K) (G := A) (φ := A.subtype) p = 1 :=
      MonoidHom.mem_ker.1 h
    apply ha1
    simpa [p] using h1
  have hp2 : p * p = 1 := by
    show SemidirectProduct.inr a * SemidirectProduct.inr a = 1
    rw [← map_mul, haa, map_one]
  have hα2 : α ^ (2 : ℤ) = 1 := by
    rw [zpow_two]
    ext k
    exact hα k
  have hAcases : ∀ b : A, b = 1 ∨ b = a := by
    intro b
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 b.2
    obtain ⟨m, hm | hm⟩ := Int.even_or_odd' n
    · left
      apply Subtype.ext
      rw [← hn, hm, zpow_mul, hα2, one_zpow]
      rfl
    · right
      apply Subtype.ext
      rw [← hn, hm, zpow_add, zpow_mul, hα2, one_zpow, one_mul, zpow_one]
  refine ⟨H, inferInstance, inferInstance, L, inferInstance, φ, p, hpL, ?_, ?_, ?_⟩
  · refine orderOf_eq_prime (by rw [sq]; exact hp2) fun h1 => hpL ?_
    rw [h1]; exact L.one_mem
  · intro k
    rw [hφ, hφ]
    have h := (SemidirectProduct.inl_aut (N := K) (G := A) (φ := A.subtype) a k)
    have hinv : p⁻¹ = SemidirectProduct.inr a⁻¹ := (map_inv _ _).symm
    rw [hinv, ← h]
    rfl
  · intro g
    rw [Subgroup.mem_centralizer_iff]
    have hLmem : ∀ l ∈ (L : Set H), ∃ k : K, l = SemidirectProduct.inl k := by
      intro l hl
      obtain ⟨k, hk⟩ := φ.surjective ⟨l, hl⟩
      exact ⟨k, ((congrArg Subtype.val hk).symm).trans (hφ k)⟩
    constructor
    · intro hg
      obtain ⟨z, hz, hgz⟩ := burnsideI22P5_semidirect_centralizer (φ := A.subtype) (fun b hb c => by
        rcases hAcases b with h | h
        · exact absurd h hb
        · rw [h]
          exact hα1 c) g (fun n => hg (SemidirectProduct.inl n) (by
            show SemidirectProduct.inl n ∈ L
            exact (φ n).2))
      exact ⟨z, hz, by rw [hφ]; exact hgz⟩
    · rintro ⟨z, hz, rfl⟩ h hh
      obtain ⟨k, rfl⟩ := hLmem h hh
      rw [hφ, ← map_mul, ← map_mul]
      congr 1
      exact Subgroup.mem_center_iff.1 hz k

theorem burnsideI22P5_ext {K Q : Type} [Group K] [Finite K] [Group Q] (hK : CFSG.IsQuasisimple K)
    {t : K} (ht : orderOf t = 2) (hZt : Subgroup.center K = Subgroup.zpowers t)
    (π : K →* Q) (hπ : Function.Surjective π) (hker : π.ker = Subgroup.zpowers t)
    (α : K ≃* K) (hα : ∀ k, α (α k) = k) (hα1 : ∀ g : K, α ≠ MulAut.conj g) :
    ∃ (H : Type) (_ : Group H) (_ : Finite H) (L : Subgroup H) (_ : L.Normal) (φ : K ≃* L)
      (p : H) (π' : L →* Q), p ∉ L ∧ orderOf p = 2 ∧
      (∀ k : K, p * (φ k : H) * p⁻¹ = (φ (α k) : H)) ∧
      CFSG.Assembly.IsQuasisimple L ∧ orderOf (φ t) = 2 ∧
      Subgroup.center L = Subgroup.zpowers (φ t) ∧ Function.Surjective π' ∧
      π'.ker = Subgroup.zpowers (φ t) ∧
      Subgroup.centralizer (L : Set H) = Subgroup.zpowers ((φ t : L) : H) ∧
      ∀ k : K, π' (φ k) = π k := by
  obtain ⟨H, hG, hF, L, hN, φ, p, hpL, hp2, hpact, hcent⟩ := burnsideI22P5_exists_ext α hα hα1
  haveI : Group.IsPerfect K := hK.1
  refine ⟨H, hG, hF, L, hN, φ, p, π.comp φ.symm.toMonoidHom, hpL, hp2, hpact, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  ·
    haveI : Group.IsPerfect L := Group.IsPerfect.ofSurjective (f := φ.toMonoidHom) φ.surjective
    refine ⟨Group.IsPerfect.commutator_eq_top, ?_⟩
    have hc : (Subgroup.center K).map φ.toMonoidHom = Subgroup.center L :=
      Subgroup.map_center_eq φ
    exact (MulEquiv.isSimpleGroup_congr (QuotientGroup.congr (Subgroup.center K)
      (Subgroup.center L) φ hc)).1 hK.2.1
  · rw [MulEquiv.orderOf_eq]; exact ht
  · rw [← Subgroup.map_center_eq φ, hZt, MonoidHom.map_zpowers]; rfl
  · intro q
    obtain ⟨k, rfl⟩ := hπ q
    exact ⟨φ k, by simp⟩
  · ext l
    obtain ⟨k, rfl⟩ := φ.surjective l
    rw [MonoidHom.mem_ker]
    have h1 : (π.comp φ.symm.toMonoidHom) (φ k) = π k := by simp
    rw [h1, ← MonoidHom.mem_ker, hker]
    constructor
    · intro hk
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk
      exact Subgroup.mem_zpowers_iff.2 ⟨n, by simp⟩
    · intro hl
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hl
      have hn' : φ (t ^ n) = φ k := by rw [map_zpow]; exact Subtype.ext (by simpa using congrArg Subtype.val hn)
      rw [← φ.injective hn']
      exact Subgroup.zpow_mem_zpowers t n
  · ext g
    rw [hcent, hZt]
    constructor
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
      exact Subgroup.mem_zpowers_iff.2 ⟨n, by simp [Subgroup.coe_zpow]⟩
    · intro hg
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
      exact ⟨t ^ n, Subgroup.zpow_mem_zpowers t n, by simp [Subgroup.coe_zpow]⟩
  · intro k
    simp

open CFSG.ASVolI.ChIJK in
theorem burnsideI22P5_b2_of_sq {K : Type} [Group K] {t : K} (ht : orderOf t = 2)
    (hZt : Subgroup.center K = Subgroup.zpowers t)
    (hstrong : ∀ k : K, IsTwoCentralInvolution (k : K ⧸ Subgroup.center K) → k ^ 2 = 1)
    (α : K ≃* K) {k : K} (hk2 : k ^ 2 = t) (hαk : α k = k⁻¹) :
    ∃ k : K, orderOf k = 4 ∧ (k : K ⧸ Subgroup.center K) ^ 2 = 1 ∧
      (k : K ⧸ Subgroup.center K) ≠ 1 ∧
      ¬ IsTwoCentralInvolution (k : K ⧸ Subgroup.center K) ∧ α k = k⁻¹ := by
  have ht1 : t ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ht
    exact absurd ht (by norm_num)
  have ht2 : t ^ 2 = 1 := by rw [← ht]; exact pow_orderOf_eq_one t
  have hk1 : ¬ k ^ 2 = 1 := by rw [hk2]; exact ht1
  have hk4 : orderOf k = 4 := by
    have h := orderOf_eq_prime_pow (p := 2) (n := 1) (x := k) (by simpa using hk1)
      (by rw [show 2 ^ (1 + 1) = 2 * 2 from rfl, pow_mul, hk2, ht2])
    simpa using h
  have htZ : t ∈ Subgroup.center K := hZt ▸ Subgroup.mem_zpowers t
  have hkZ : (k : K ⧸ Subgroup.center K) ^ 2 = 1 := by
    rw [← QuotientGroup.mk_pow, hk2]
    exact (QuotientGroup.eq_one_iff t).2 htZ
  refine ⟨k, hk4, hkZ, ?_, fun h => hk1 (hstrong k h), hαk⟩
  intro h
  rw [QuotientGroup.eq_one_iff, hZt] at h
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 h
  apply hk1
  rw [← hn, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]
  simp [ht2]

open CFSG.ASVolI.ChIJK in
theorem burnsideI22P5_isTwoCentral_iff_card {G : Type} [Group G] [Finite G] (S : Sylow 2 G)
    {t : G} (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1) :
    IsTwoCentralInvolution t ↔ Nat.card S ∣ Nat.card (Subgroup.centralizer ({t} : Set G)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS : Nat.card S = 2 ^ (Nat.card G).factorization 2 := Sylow.card_eq_multiplicity S
  constructor
  · rintro ⟨-, -, T, htT, hTc⟩
    have hT : Nat.card T = 2 ^ (Nat.card G).factorization 2 := Sylow.card_eq_multiplicity T
    have hle : (T : Subgroup G) ≤ Subgroup.centralizer ({t} : Set G) := by
      intro x hx
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hTc x hx
    rw [hS, ← hT]
    exact Subgroup.card_dvd_of_le hle
  · intro hdvd
    set C : Subgroup G := Subgroup.centralizer ({t} : Set G) with hC
    have htC : t ∈ C := by
      rw [Subgroup.mem_centralizer_singleton_iff]
    let t' : C := ⟨t, htC⟩
    have hP₀ : IsPGroup 2 (Subgroup.zpowers t') := by
      refine IsPGroup.of_card (n := 1) ?_
      rw [Nat.card_zpowers, pow_one]
      apply orderOf_eq_prime
      · apply Subtype.ext; simpa using ht2
      · intro h; exact ht1 (congrArg Subtype.val h)
    obtain ⟨D', hD'⟩ := hP₀.exists_le_sylow
    have hD'card : Nat.card D' = 2 ^ (Nat.card C).factorization 2 :=
      Sylow.card_eq_multiplicity D'
    have hv : (Nat.card G).factorization 2 = (Nat.card C).factorization 2 := by
      have h1 : 2 ^ (Nat.card G).factorization 2 ∣ Nat.card C := hS ▸ hdvd
      have h2 : (Nat.card G).factorization 2 ≤ (Nat.card C).factorization 2 :=
        (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').1 h1
      have h3 : Nat.card C ∣ Nat.card G := Subgroup.card_subgroup_dvd_card C
      have h4 : (Nat.card C).factorization 2 ≤ (Nat.card G).factorization 2 :=
        (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').2 h3 2
      omega
    let D : Subgroup G := (D' : Subgroup C).map C.subtype
    have hDcard : Nat.card D = 2 ^ (Nat.card G).factorization 2 := by
      rw [hv, ← hD'card]
      exact Subgroup.card_map_of_injective C.subtype_injective
    let SD : Sylow 2 G := Sylow.ofCard D hDcard
    refine ⟨ht2, ht1, SD, ?_, ?_⟩
    · show t ∈ D
      exact ⟨t', hD' (Subgroup.mem_zpowers t'), rfl⟩
    · intro x hx
      have hx' : x ∈ D := hx
      obtain ⟨y, -, rfl⟩ := hx'
      have := y.2
      rw [Subgroup.mem_centralizer_singleton_iff] at this
      exact this

theorem burnsideI22P5_lift_eq {K : Type} [Group K] {t : K} (ht : orderOf t = 2)
    (hZt : Subgroup.center K = Subgroup.zpowers t) {a b : K}
    (h : (a : K ⧸ Subgroup.center K) = (b : K ⧸ Subgroup.center K)) : b = a ∨ b = a * t := by
  rw [QuotientGroup.eq, hZt] at h
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 h
  have ht2 : t ^ 2 = 1 := by rw [← ht]; exact pow_orderOf_eq_one t
  have hn' : a⁻¹ * b = t ^ (n % 2) := by
    rw [← hn]
    conv_lhs => rw [← Int.emod_add_mul_ediv n 2, zpow_add, zpow_mul]
    have : t ^ (2 : ℤ) = 1 := by rw [zpow_two, ← sq]; exact ht2
    rw [this, one_zpow, mul_one]
  rcases Int.emod_two_eq_zero_or_one n with h0 | h1
  · left
    rw [h0, zpow_zero] at hn'
    calc b = a * (a⁻¹ * b) := by group
      _ = a := by rw [hn', mul_one]
  · right
    rw [h1, zpow_one] at hn'
    calc b = a * (a⁻¹ * b) := by group
      _ = a * t := by rw [hn']

noncomputable def burnsideI22P5_ind {K X : Type} [Group K] [Group X]
    (e : K ⧸ Subgroup.center K ≃* X) : MulAut K →* MulAut X :=
  (MulAut.congr e).toMonoidHom.comp
    (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom K)

theorem burnsideI22P5_ind_apply {K X : Type} [Group K] [Group X]
    (e : K ⧸ Subgroup.center K ≃* X) (β : MulAut K) (k : K) :
    burnsideI22P5_ind e β (e (k : K ⧸ Subgroup.center K)) = e ((β k : K) : K ⧸ Subgroup.center K) := by
  show e ((CFSG.ComponentClassification.PerfectAutomorphisms.onCenterQuotient β)
    (e.symm (e (k : K ⧸ Subgroup.center K)))) = _
  rw [MulEquiv.symm_apply_apply]
  exact congrArg e (CFSG.ComponentClassification.PerfectAutomorphisms.onCenterQuotient_apply_mk β k)

theorem burnsideI22P5_ind_conj {K X : Type} [Group K] [Group X]
    (e : K ⧸ Subgroup.center K ≃* X) (g : K) :
    burnsideI22P5_ind e (MulAut.conj g) = MulAut.conj (e (g : K ⧸ Subgroup.center K)) := by
  ext x
  obtain ⟨k, rfl⟩ := e.surjective x
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective k
  rw [burnsideI22P5_ind_apply, MulAut.conj_apply, MulAut.conj_apply, QuotientGroup.mk_mul,
    QuotientGroup.mk_mul, QuotientGroup.mk_inv, map_mul, map_mul, map_inv]

theorem burnsideI22P5_ind_injective {K X : Type} [Group K] [Group X] [Group.IsPerfect K]
    (e : K ⧸ Subgroup.center K ≃* X) : Function.Injective (burnsideI22P5_ind e) := by
  intro a b hab
  apply CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom_injective K
  exact (MulAut.congr e).injective hab

open CFSG.ComponentClassification CFSG.ComponentClassification.J2Cover
  CFSG.ComponentClassification.J2Cover.Models in
theorem burnsideI22P5_J2_table_center :
    ∀ k < 128, (∀ j < 128, mulIdx j k = mulIdx k j) → k = 0 ∨ k = 4 := by
  decide +kernel

open CFSG.ComponentClassification CFSG.ComponentClassification.J2Cover
  CFSG.ComponentClassification.J2Cover.Models in
theorem burnsideI22P5_J2_table_central_four : ∀ j < 128, mulIdx j 4 = mulIdx 4 j := by
  decide +kernel

open CFSG.ComponentClassification CFSG.ComponentClassification.J2Cover
  CFSG.ComponentClassification.J2Cover.Models in
theorem burnsideI22P5_J2_center_S
    {s : Perm315} (hs : s ∈ S) (hc : ∀ s' ∈ S, s' * s = s * s') :
    s = 1 ∨ s = ((elt 4 : S) : Perm315) := by
  obtain ⟨x, hx, rfl⟩ := exists_elt hs
  have hj : ∀ j < 128, mulIdx j x = mulIdx x j := by
    intro j hj
    have h1 := hc ((elt j : S) : Perm315) (elt j).2
    obtain ⟨hm1, hm2⟩ := mulIdx_spec (a := j) hx
    obtain ⟨hm3, hm4⟩ := mulIdx_spec (a := x) hj
    have h2 : elt (mulIdx j x) = elt (mulIdx x j) := by
      apply Subtype.ext
      have e1 : ((elt (mulIdx j x) : S) : Perm315) = (elt j : Perm315) * elt x :=
        congrArg Subtype.val hm2
      have e2 : ((elt (mulIdx x j) : S) : Perm315) = (elt x : Perm315) * elt j :=
        congrArg Subtype.val hm4
      rw [e1, e2]
      exact h1
    exact elt_injective hm1 hm3 h2
  rcases burnsideI22P5_J2_table_center x hx hj with rfl | rfl
  · left
    rw [elt_zero]; rfl
  · right; rfl

open CFSG.ComponentClassification CFSG.ComponentClassification.J2Cover
  CFSG.ComponentClassification.J2Cover.Models in
theorem burnsideI22P5_J2_elt4_central
    {s : Perm315} (hs : s ∈ S) :
    s * ((elt 4 : S) : Perm315) = ((elt 4 : S) : Perm315) * s := by
  obtain ⟨j, hj, rfl⟩ := exists_elt hs
  obtain ⟨hm1, hm2⟩ := mulIdx_spec (a := j) (b := 4) (by norm_num)
  obtain ⟨hm3, hm4⟩ := mulIdx_spec (a := 4) (b := j) hj
  have e := burnsideI22P5_J2_table_central_four j hj
  have e1 : ((elt (mulIdx j 4) : S) : Perm315) = (elt j : Perm315) * elt 4 :=
    congrArg Subtype.val hm2
  have e2 : ((elt (mulIdx 4 j) : S) : Perm315) = (elt 4 : Perm315) * elt j :=
    congrArg Subtype.val hm4
  rw [← e1, ← e2, e]

open CFSG.ComponentClassification CFSG.ComponentClassification.J2Cover
  CFSG.ComponentClassification.J2Cover.Models CFSG.ASVolI.ChIJK in
theorem burnsideI22P5_J2_isTwoCentral_iff
    (q : Models.P) (hq : orderOf q = 2) :
    IsTwoCentralInvolution q ↔ fixCount (q : Perm315) = 11 := by
  obtain ⟨-, hconj, -, hord4, hfix4, -, -⟩ := ctss_j2_involutions
  have hq2 : q ^ 2 = 1 := by rw [← hq]; exact pow_orderOf_eq_one q
  have hq1 : q ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hq
    exact absurd hq (by norm_num)
  let c : Models.P := incl (elt 4)
  have hcS : ((c : Models.P) : Perm315) = ((elt 4 : S) : Perm315) := incl_coe _
  have hc2 : orderOf c = 2 := by
    rw [show c = incl (elt 4) from rfl, orderOf_injective incl
      (fun a b h => Subtype.ext (by simpa using congrArg Subtype.val h)) (elt 4)]
    exact hord4
  have hcfix : fixCount (c : Perm315) = 11 := by rw [hcS]; exact hfix4
  constructor
  · rintro ⟨-, -, T, hqT, hTc⟩
    obtain ⟨Q, hQ⟩ := exists_sylow_eq_S
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Models.P Q T
    have hqT' : q ∈ ((g • Q : Sylow 2 Models.P) : Subgroup Models.P) := by rw [hg]; exact hqT
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hqT'
    obtain ⟨s, hsQ, hsq⟩ := hqT'
    have hsq' : g * s * g⁻¹ = q := hsq
    have hsS : (s : Perm315) ∈ S := by
      have : s ∈ (Q : Subgroup Models.P) := hsQ
      rw [hQ, Subgroup.mem_subgroupOf] at this
      exact this
    have hsc : ∀ s' ∈ S, s' * (s : Perm315) = (s : Perm315) * s' := by
      intro s' hs'
      let x' : Models.P := ⟨s', S_le_P hs'⟩
      have hx'Q : x' ∈ (Q : Subgroup Models.P) := by
        rw [hQ, Subgroup.mem_subgroupOf]; exact hs'
      have hxT : g * x' * g⁻¹ ∈ (T : Subgroup Models.P) := by
        rw [← hg]
        rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
        exact ⟨x', hx'Q, rfl⟩
      have h := hTc _ hxT
      rw [← hsq'] at h
      have h2 : x' * s = s * x' := by
        have := congrArg (fun y => g⁻¹ * y * g) h
        simpa [mul_assoc] using this
      exact congrArg Subtype.val h2
    have hs1 : (s : Perm315) ≠ 1 := by
      intro h
      apply hq1
      have : s = 1 := Subtype.ext h
      rw [← hsq', this]; group
    rcases burnsideI22P5_J2_center_S hsS hsc with h | h
    · exact absurd h hs1
    · have hfq : (q : Perm315) = (g : Perm315) * s * (g : Perm315)⁻¹ := by
        rw [← hsq']; rfl
      rw [hfq, fixCount_conj, h]
      exact hfix4
  · intro h11
    obtain ⟨g, hg⟩ := hconj q c hq hc2 (by rw [h11, hcfix])
    have hcc : IsTwoCentralInvolution c := by
      refine ⟨by rw [← hc2]; exact pow_orderOf_eq_one c, ?_, sylowS, ?_, ?_⟩
      · intro h
        rw [h, orderOf_one] at hc2
        exact absurd hc2 (by norm_num)
      · show c ∈ (sylowS : Subgroup Models.P)
        rw [coe_sylowS, Subgroup.mem_subgroupOf, hcS]
        exact (elt 4).2
      · intro x hx
        have hx' : x ∈ (sylowS : Subgroup Models.P) := hx
        rw [coe_sylowS, Subgroup.mem_subgroupOf] at hx'
        apply Subtype.ext
        change (x : Perm315) * (c : Perm315) = (c : Perm315) * (x : Perm315)
        rw [hcS]
        exact burnsideI22P5_J2_elt4_central hx'
    have hmap := burnsideI22P5_isTwoCentral_map (MulAut.conj g⁻¹ : Models.P ≃* Models.P) hcc
    have : (MulAut.conj g⁻¹ : Models.P ≃* Models.P) c = q := by
      rw [← hg, MulAut.conj_apply]
      group
    rwa [this] at hmap

open CFSG.ComponentClassification CFSG.ComponentClassification.J2Cover
  CFSG.ComponentClassification.J2Cover.Models in
theorem burnsideI22P5_J2_setup
    {K : Type} [Group K] [Finite K]
    (hK : CFSG.IsQuasisimple K) (hZ : Subgroup.center K ≠ ⊥)
    (h : CFSG.Blueprint.NativeSporadic.IsSporadic (K ⧸ Subgroup.center K) .J2) :
    Nat.card (Subgroup.center K) = 2 ∧ Nonempty (K ⧸ Subgroup.center K ≃* Models.P) := by
  obtain ⟨e⟩ := h
  have e' : K ⧸ Subgroup.center K ≃* CFSG.Blueprint.NativeSporadic.J2 := e
  refine ⟨burnsideI22P5_card_center_eq_two hK hZ ?_, ⟨e'.trans (nativeEquivP.trans Lift.toModels)⟩⟩
  rw [CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.card_hopfMultiplier_eq_of_mulEquiv
    e']
  exact CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.nativeRow_J2

open CFSG.ComponentClassification CFSG.ComponentClassification.J2Cover
  CFSG.ComponentClassification.J2Cover.Models in
theorem burnsideI22P5_J2_lift
    {K : Type} [Group K] [Finite K] (hK : CFSG.IsQuasisimple K)
    (hZ2 : Nat.card (Subgroup.center K) = 2) (e : K ⧸ Subgroup.center K ≃* Models.P) :
    ∃ t : K, orderOf t = 2 ∧ Subgroup.center K = Subgroup.zpowers t ∧
      (∀ k : K, orderOf (e (k : K ⧸ Subgroup.center K)) = 2 →
        fixCount ((e (k : K ⧸ Subgroup.center K) : Models.P) : Perm315) = 11 → orderOf k = 2) ∧
      (∀ k : K, orderOf (e (k : K ⧸ Subgroup.center K)) = 2 →
        fixCount ((e (k : K ⧸ Subgroup.center K) : Models.P) : Perm315) = 15 →
          k ^ 2 = t ∧ orderOf k = 4) := by
  obtain ⟨t, ht, hZt⟩ := burnsideI22P5_exists_t hZ2
  let π : K →* Models.P := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K))
  have hπ : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : π.ker = Subgroup.zpowers t := by
    rw [← hZt]
    ext l
    simp only [π, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hext : CFSG.ComponentClassification.CentralCover.IsCentralDoubleExt π t :=
    ⟨hπ, hZt ▸ Subgroup.mem_zpowers t, ht, hker⟩
  haveI : Group.IsPerfect K := hK.1
  obtain ⟨-, h11, h15⟩ := Lift.native_sylow_map_and_lift_orders (Group.IsPerfect.commutator_eq_top)
    hext
  exact ⟨t, ht, hZt, fun k => h11 k, fun k => h15 k⟩

open CFSG.ComponentClassification CFSG.ComponentClassification.J2Cover
  CFSG.ComponentClassification.J2Cover.Models CFSG.ASVolI.ChIJK in
theorem burnsideI22P5_J2_strong
    {K : Type} [Group K] [Finite K]
    (hK : CFSG.IsQuasisimple K) (hZ2 : Nat.card (Subgroup.center K) = 2)
    (e : K ⧸ Subgroup.center K ≃* Models.P) :
    ∀ k : K, IsTwoCentralInvolution (k : K ⧸ Subgroup.center K) → k ^ 2 = 1 := by
  obtain ⟨t, ht, hZt, h11, -⟩ := burnsideI22P5_J2_lift hK hZ2 e
  intro k hk
  have hq2 : orderOf (e (k : K ⧸ Subgroup.center K)) = 2 := by
    rw [MulEquiv.orderOf_eq]
    exact orderOf_eq_prime hk.1 hk.2.1
  have hfix := (burnsideI22P5_J2_isTwoCentral_iff _ hq2).1 (burnsideI22P5_isTwoCentral_map e hk)
  have := h11 k hq2 hfix
  rw [← this]
  exact pow_orderOf_eq_one k

open CFSG.ComponentClassification CFSG.ComponentClassification.J2Cover
  CFSG.ComponentClassification.J2Cover.Models CFSG.ASVolI.ChIJK in
theorem burnsideI22P5_J2_a
    {K : Type} [Group K] [Finite K]
    (hK : CFSG.IsQuasisimple K) (hZ : Subgroup.center K ≠ ⊥)
    (h : CFSG.Blueprint.NativeSporadic.IsSporadic (K ⧸ Subgroup.center K) .J2) :
    TwoCentralInvolutionsLift K := by
  obtain ⟨hZ2, ⟨e⟩⟩ := burnsideI22P5_J2_setup hK hZ h
  intro t' ht'
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective t'
  exact ⟨k, burnsideI22P5_J2_strong hK hZ2 e k ht', rfl⟩

open CFSG.ComponentClassification CFSG.ComponentClassification.J2Cover
  CFSG.ComponentClassification.J2Cover.Models CFSG.ASVolI.ChIJK in
theorem burnsideI22P5_J2_b1
    {K : Type} [Group K] [Finite K]
    (hK : CFSG.IsQuasisimple K) (hZ : Subgroup.center K ≠ ⊥)
    (h : CFSG.Blueprint.NativeSporadic.IsSporadic (K ⧸ Subgroup.center K) .J2) :
    NonTwoCentralInvolutionsLiftToOrderFour K := by
  obtain ⟨hZ2, ⟨e⟩⟩ := burnsideI22P5_J2_setup hK hZ h
  obtain ⟨t, ht, hZt, -, h15⟩ := burnsideI22P5_J2_lift hK hZ2 e
  intro t' ht2 ht1 hnc
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective t'
  have hq2 : orderOf (e (k : K ⧸ Subgroup.center K)) = 2 := by
    rw [MulEquiv.orderOf_eq]
    exact orderOf_eq_prime ht2 ht1
  have hne : ¬ fixCount ((e (k : K ⧸ Subgroup.center K) : Models.P) : Perm315) = 11 := by
    intro hfix
    apply hnc
    have := burnsideI22P5_isTwoCentral_map e.symm
      ((burnsideI22P5_J2_isTwoCentral_iff _ hq2).2 hfix)
    simpa using this
  obtain ⟨hcases, -⟩ := ctss_j2_involutions
  have h15' : fixCount ((e (k : K ⧸ Subgroup.center K) : Models.P) : Perm315) = 15 := by
    rcases hcases _ hq2 with h | h
    · exact absurd h hne
    · exact h
  obtain ⟨-, hk4⟩ := h15 k hq2 h15'
  exact ⟨k, hk4, rfl⟩

open CFSG.ComponentClassification CFSG.ComponentClassification.J2Cover
  CFSG.ComponentClassification.J2Cover.Models CFSG.ASVolI.ChIJK in
theorem burnsideI22P5_J2_b2
    {K : Type} [Group K] [Finite K]
    (hK : CFSG.IsQuasisimple K) (hZ : Subgroup.center K ≠ ⊥)
    (h : CFSG.Blueprint.NativeSporadic.IsSporadic (K ⧸ Subgroup.center K) .J2) :
    OuterInvolutionsInvertOrderFour K := by
  intro α hα hα1
  obtain ⟨hZ2, ⟨e⟩⟩ := burnsideI22P5_J2_setup hK hZ h
  obtain ⟨t, ht, hZt, h11, h15⟩ := burnsideI22P5_J2_lift hK hZ2 e
  let eP : K ⧸ Subgroup.center K ≃* J2Cover.P := e.trans Lift.toModels.symm
  let πK : K →* J2Cover.P := eP.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K))
  have hπK : Function.Surjective πK := eP.surjective.comp (QuotientGroup.mk'_surjective _)
  have hkerK : πK.ker = Subgroup.zpowers t := by
    rw [← hZt]
    ext l
    simp only [πK, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  obtain ⟨H, hG, hF, L, hN, φ, p, π', hpL, hp2, hpact, hLq, ht', hZL, hπ', hker', hCL, hπφ⟩ :=
    burnsideI22P5_ext hK ht hZt πK hπK hkerK α hα hα1
  haveI : Finite H := hF
  have hkerZL : π'.ker = Subgroup.center L := by rw [hker', hZL]
  obtain ⟨-, hfix⟩ :=
    ctss_j2_actual_double_cover_external_conjugacy_and_exact_fixed_section hLq ht' hZL π' hπ'
      hker' hCL
  have hact := CFSG.ComponentClassification.CentralCover.fullAction_apply π' hπ' hkerZL p
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, c, -, -, -, -, hc⟩ :=
    hfix p hpL hp2 _ hact
  obtain ⟨v, hv⟩ := hπ' c
  obtain ⟨hv2, hpv, -⟩ := hc v hv
  obtain ⟨k, rfl⟩ := φ.surjective v
  have hk2 : k ^ 2 = t := by
    apply φ.injective
    rw [map_pow]
    exact hv2
  have hαk : α k = k⁻¹ := by
    have h1 : (φ (α k) : H) = ((φ k : L) : H) * ((φ t : L) : H) := by
      rw [← hpact]; exact hpv
    have h2 : φ (α k) = φ (k * t) := by
      apply Subtype.ext
      rw [h1, map_mul]; rfl
    have h3 : α k = k * t := φ.injective h2
    have ht2 : t ^ 2 = 1 := by rw [← ht]; exact pow_orderOf_eq_one t
    rw [h3]
    have : k⁻¹ = k * t := by
      apply inv_eq_of_mul_eq_one_right
      calc k * (k * t) = k ^ 2 * t := by rw [sq, mul_assoc]
        _ = t * t := by rw [hk2]
        _ = 1 := by rw [← sq]; exact ht2
    exact this.symm
  exact burnsideI22P5_b2_of_sq ht hZt (burnsideI22P5_J2_strong hK hZ2 e) α hk2 hαk

open CFSG.ComponentClassification CFSG.ComponentClassification.M12Cover
  CFSG.ComponentClassification.M12Cover.SylowTable in
theorem burnsideI22P5_M12_table_center :
    ∀ k < 64, (∀ j < 64, mulIdx j k = mulIdx k j) → k = 0 ∨ k = 22 := by
  decide +kernel

open CFSG.ComponentClassification CFSG.ComponentClassification.M12Cover
  CFSG.ComponentClassification.M12Cover.SylowTable in
theorem burnsideI22P5_M12_table_central_22 : ∀ j < 64, mulIdx j 22 = mulIdx 22 j := by
  decide +kernel

open CFSG.ComponentClassification CFSG.ComponentClassification.M12Cover
  CFSG.ComponentClassification.M12Cover.SylowTable in
theorem burnsideI22P5_M12_code22 :
    code 22 = [6, 5, 11, 4, 3, 1, 0, 7, 8, 9, 10, 2] := by
  decide +kernel

open CFSG.ComponentClassification CFSG.ComponentClassification.M12Cover
  CFSG.ComponentClassification.M12Cover.SylowTable in
theorem burnsideI22P5_M12_center_S {s : Equiv.Perm (Fin 12)} (hs : s ∈ S)
    (hc : ∀ s' ∈ S, s' * s = s * s') :
    s = 1 ∨ s = ((elt 22 : S) : Equiv.Perm (Fin 12)) := by
  obtain ⟨x, hx, rfl⟩ := exists_elt hs
  have hj : ∀ j < 64, mulIdx j x = mulIdx x j := by
    intro j hj
    have h1 := hc ((elt j : S) : Equiv.Perm (Fin 12)) (elt j).2
    obtain ⟨hm1, hm2⟩ := mulIdx_spec (a := j) hj hx
    obtain ⟨hm3, hm4⟩ := mulIdx_spec (a := x) hx hj
    have h2 : elt (mulIdx j x) = elt (mulIdx x j) := by
      apply Subtype.ext
      have e1 : ((elt (mulIdx j x) : S) : Equiv.Perm (Fin 12)) = (elt j : Equiv.Perm (Fin 12)) *
          elt x := congrArg Subtype.val hm2
      have e2 : ((elt (mulIdx x j) : S) : Equiv.Perm (Fin 12)) = (elt x : Equiv.Perm (Fin 12)) *
          elt j := congrArg Subtype.val hm4
      rw [e1, e2]
      exact h1
    exact elt_injective hm1 hm3 h2
  rcases burnsideI22P5_M12_table_center x hx hj with rfl | rfl
  · left
    rw [elt_zero]; rfl
  · right; rfl

open CFSG.ComponentClassification CFSG.ComponentClassification.M12Cover
  CFSG.ComponentClassification.M12Cover.SylowTable in
theorem burnsideI22P5_M12_elt22_central {s : Equiv.Perm (Fin 12)} (hs : s ∈ S) :
    s * ((elt 22 : S) : Equiv.Perm (Fin 12)) = ((elt 22 : S) : Equiv.Perm (Fin 12)) * s := by
  obtain ⟨j, hj, rfl⟩ := exists_elt hs
  obtain ⟨hm1, hm2⟩ := mulIdx_spec (a := j) (b := 22) hj (by norm_num)
  obtain ⟨hm3, hm4⟩ := mulIdx_spec (a := 22) (b := j) (by norm_num) hj
  have e := burnsideI22P5_M12_table_central_22 j hj
  have e1 : ((elt (mulIdx j 22) : S) : Equiv.Perm (Fin 12)) =
      (elt j : Equiv.Perm (Fin 12)) * elt 22 := congrArg Subtype.val hm2
  have e2 : ((elt (mulIdx 22 j) : S) : Equiv.Perm (Fin 12)) =
      (elt 22 : Equiv.Perm (Fin 12)) * elt j := congrArg Subtype.val hm4
  rw [← e1, ← e2, e]

open CFSG.ComponentClassification CFSG.ComponentClassification.M12Cover
  CFSG.ComponentClassification.M12Cover.SylowTable in
theorem burnsideI22P5_M12_fix22 :
    (Finset.univ.filter fun i : Fin 12 => ((elt 22 : S) : Equiv.Perm (Fin 12)) i = i).card = 4 := by
  have hc := isCode_elt 22 (by norm_num)
  rw [burnsideI22P5_M12_code22] at hc
  have h : ∀ i : Fin 12, ((elt 22 : S) : Equiv.Perm (Fin 12)) i = i ↔
      (nth 0 [6, 5, 11, 4, 3, 1, 0, 7, 8, 9, 10, 2] (i : ℕ) = (i : ℕ)) := by
    intro i
    rw [hc.2 i, Fin.ext_iff]
  rw [Finset.filter_congr (fun i _ => h i)]
  decide +kernel

open CFSG.ComponentClassification CFSG.ComponentClassification.M12Cover
  CFSG.ComponentClassification.M12Cover.SylowTable in
theorem burnsideI22P5_M12_elt22_sq :
    ((elt 22 : S) : Equiv.Perm (Fin 12)) * ((elt 22 : S) : Equiv.Perm (Fin 12)) = 1 := by
  have hc := isCode_elt 22 (by norm_num)
  have h := hc.mul hc
  rw [burnsideI22P5_M12_code22] at h
  have h1 : comp [6, 5, 11, 4, 3, 1, 0, 7, 8, 9, 10, 2] [6, 5, 11, 4, 3, 1, 0, 7, 8, 9, 10, 2] =
      List.range 12 := by decide +kernel
  rw [h1] at h
  exact h.perm_eq isCode_one

open CFSG.ComponentClassification CFSG.ComponentClassification.M12Cover
  CFSG.ComponentClassification.M12Cover.SylowTable in
@[expose] noncomputable def burnsideI22P5_M12_c0 : CFSG.Blueprint.NativeSporadic.M12 :=
  ⟨((elt 22 : S) : Equiv.Perm (Fin 12)), S_le_M12 (elt 22).2⟩

open CFSG.ComponentClassification CFSG.ComponentClassification.M12Cover
  CFSG.ComponentClassification.M12Cover.SylowTable in
theorem burnsideI22P5_M12_c0_fix : fixedCount burnsideI22P5_M12_c0 = 4 :=
  burnsideI22P5_M12_fix22

open CFSG.ComponentClassification CFSG.ComponentClassification.M12Cover
  CFSG.ComponentClassification.M12Cover.SylowTable in
theorem burnsideI22P5_M12_c0_order : orderOf burnsideI22P5_M12_c0 = 2 := by
  have hsq : burnsideI22P5_M12_c0 ^ 2 = 1 := by
    apply Subtype.ext
    exact (sq _).trans burnsideI22P5_M12_elt22_sq
  refine orderOf_eq_prime hsq fun h => ?_
  have := burnsideI22P5_M12_c0_fix
  rw [h] at this
  change (Finset.univ.filter fun i : Fin 12 => (1 : Equiv.Perm (Fin 12)) i = i).card = 4 at this
  simp at this

open CFSG.ComponentClassification CFSG.ComponentClassification.M12Cover
  CFSG.ComponentClassification.M12Cover.SylowTable CFSG.ASVolI.ChIJK in
theorem burnsideI22P5_M12_isTwoCentral_iff
    (q : CFSG.Blueprint.NativeSporadic.M12)
    (hq : orderOf q = 2) : IsTwoCentralInvolution q ↔ fixedCount q = 4 := by
  have hq2 : q ^ 2 = 1 := by rw [← hq]; exact pow_orderOf_eq_one q
  have hq1 : q ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hq
    exact absurd hq (by norm_num)
  have hcc : IsTwoCentralInvolution burnsideI22P5_M12_c0 := by
    refine ⟨by rw [← burnsideI22P5_M12_c0_order]; exact pow_orderOf_eq_one _, ?_, sylow, ?_, ?_⟩
    · intro h
      have := burnsideI22P5_M12_c0_order
      rw [h, orderOf_one] at this
      exact absurd this (by norm_num)
    · show burnsideI22P5_M12_c0 ∈ (sylow : Subgroup CFSG.Blueprint.NativeSporadic.M12)
      rw [coe_sylow, Subgroup.mem_subgroupOf]
      exact (elt 22).2
    · intro x hx
      have hx' : x ∈ (sylow : Subgroup CFSG.Blueprint.NativeSporadic.M12) := hx
      rw [coe_sylow, Subgroup.mem_subgroupOf] at hx'
      apply Subtype.ext
      exact burnsideI22P5_M12_elt22_central hx'
  constructor
  · rintro ⟨-, -, T, hqT, hTc⟩
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq CFSG.Blueprint.NativeSporadic.M12 sylow T
    have hqT' : q ∈ ((g • sylow : Sylow 2 CFSG.Blueprint.NativeSporadic.M12) :
        Subgroup CFSG.Blueprint.NativeSporadic.M12) := by rw [hg]; exact hqT
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hqT'
    obtain ⟨s, hsQ, hsq⟩ := hqT'
    have hsq' : g * s * g⁻¹ = q := hsq
    have hsS : (s : Equiv.Perm (Fin 12)) ∈ S := by
      have : s ∈ (sylow : Subgroup CFSG.Blueprint.NativeSporadic.M12) := hsQ
      rw [coe_sylow, Subgroup.mem_subgroupOf] at this
      exact this
    have hsc : ∀ s' ∈ S, s' * (s : Equiv.Perm (Fin 12)) = (s : Equiv.Perm (Fin 12)) * s' := by
      intro s' hs'
      let x' : CFSG.Blueprint.NativeSporadic.M12 := ⟨s', S_le_M12 hs'⟩
      have hx'Q : x' ∈ (sylow : Subgroup CFSG.Blueprint.NativeSporadic.M12) := by
        rw [coe_sylow, Subgroup.mem_subgroupOf]; exact hs'
      have hxT : g * x' * g⁻¹ ∈ (T : Subgroup CFSG.Blueprint.NativeSporadic.M12) := by
        rw [← hg]
        rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
        exact ⟨x', hx'Q, rfl⟩
      have h := hTc _ hxT
      rw [← hsq'] at h
      have h2 : x' * s = s * x' := by
        have := congrArg (fun y => g⁻¹ * y * g) h
        simpa [mul_assoc] using this
      exact congrArg Subtype.val h2
    have hs1 : (s : Equiv.Perm (Fin 12)) ≠ 1 := by
      intro h
      apply hq1
      have : s = 1 := Subtype.ext h
      rw [← hsq', this]; group
    rcases burnsideI22P5_M12_center_S hsS hsc with h | h
    · exact absurd h hs1
    · have hs : s = burnsideI22P5_M12_c0 := Subtype.ext h
      rw [← hsq', hs, fixedCount_conj]
      exact burnsideI22P5_M12_c0_fix
  · intro h4
    obtain ⟨g₂, hg₂⟩ := conj_elemR_of_fixedCount_four q hq h4
    obtain ⟨g₁, hg₁⟩ := conj_elemR_of_fixedCount_four burnsideI22P5_M12_c0
      burnsideI22P5_M12_c0_order burnsideI22P5_M12_c0_fix
    have hmap := burnsideI22P5_isTwoCentral_map
      (MulAut.conj (g₂ * g₁⁻¹) : CFSG.Blueprint.NativeSporadic.M12 ≃*
        CFSG.Blueprint.NativeSporadic.M12) hcc
    have : (MulAut.conj (g₂ * g₁⁻¹) : CFSG.Blueprint.NativeSporadic.M12 ≃*
        CFSG.Blueprint.NativeSporadic.M12) burnsideI22P5_M12_c0 = q := by
      rw [← hg₂, ← hg₁, MulAut.conj_apply]
      group
    rwa [this] at hmap

open CFSG.ComponentClassification CFSG.ComponentClassification.M12Cover
  CFSG.ComponentClassification.M12Cover.SylowTable in
theorem burnsideI22P5_M12_setup {K : Type} [Group K] [Finite K]
    (hK : CFSG.IsQuasisimple K) (hZ : Subgroup.center K ≠ ⊥)
    (h : CFSG.Blueprint.NativeSporadic.IsSporadic (K ⧸ Subgroup.center K) .M12) :
    Nat.card (Subgroup.center K) = 2 ∧
      Nonempty (K ⧸ Subgroup.center K ≃* CFSG.Blueprint.NativeSporadic.M12) := by
  obtain ⟨e⟩ := h
  have e' : K ⧸ Subgroup.center K ≃* CFSG.Blueprint.NativeSporadic.M12 := e
  refine ⟨burnsideI22P5_card_center_eq_two hK hZ ?_, ⟨e'⟩⟩
  rw [CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.card_hopfMultiplier_eq_of_mulEquiv
    e']
  exact CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.nativeRow_M12

open CFSG.ComponentClassification CFSG.ComponentClassification.M12Cover
  CFSG.ComponentClassification.M12Cover.SylowTable in
theorem burnsideI22P5_M12_lift
    {K : Type} [Group K] [Finite K] (hK : CFSG.IsQuasisimple K)
    (hZ2 : Nat.card (Subgroup.center K) = 2)
    (e : K ⧸ Subgroup.center K ≃* CFSG.Blueprint.NativeSporadic.M12) :
    ∃ t : K, orderOf t = 2 ∧ Subgroup.center K = Subgroup.zpowers t ∧
      (∀ k : K, orderOf (e (k : K ⧸ Subgroup.center K)) = 2 →
        fixedCount (e (k : K ⧸ Subgroup.center K)) = 4 → orderOf k = 2) ∧
      (∀ k : K, orderOf (e (k : K ⧸ Subgroup.center K)) = 2 →
        fixedCount (e (k : K ⧸ Subgroup.center K)) = 0 → k ^ 2 = t ∧ orderOf k = 4) := by
  obtain ⟨t, ht, hZt⟩ := burnsideI22P5_exists_t hZ2
  let π : K →* CFSG.Blueprint.NativeSporadic.M12 :=
    e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K))
  have hπ : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : π.ker = Subgroup.zpowers t := by
    rw [← hZt]
    ext l
    simp only [π, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  haveI : Group.IsPerfect K := hK.1
  obtain ⟨-, h4, h0⟩ := m12_double_cover_involution_lift_orders
    (⟨Group.IsPerfect.commutator_eq_top, hK.2.1⟩ : CFSG.Assembly.IsQuasisimple K) ht hZt π hπ hker
  exact ⟨t, ht, hZt, fun k => h4 k, fun k => h0 k⟩

open CFSG.ComponentClassification CFSG.ComponentClassification.M12Cover
  CFSG.ComponentClassification.M12Cover.SylowTable CFSG.ASVolI.ChIJK in
theorem burnsideI22P5_M12_strong
    {K : Type} [Group K] [Finite K]
    (hK : CFSG.IsQuasisimple K) (hZ2 : Nat.card (Subgroup.center K) = 2)
    (e : K ⧸ Subgroup.center K ≃* CFSG.Blueprint.NativeSporadic.M12) :
    ∀ k : K, IsTwoCentralInvolution (k : K ⧸ Subgroup.center K) → k ^ 2 = 1 := by
  obtain ⟨t, ht, hZt, h4, -⟩ := burnsideI22P5_M12_lift hK hZ2 e
  intro k hk
  have hq2 : orderOf (e (k : K ⧸ Subgroup.center K)) = 2 := by
    rw [MulEquiv.orderOf_eq]
    exact orderOf_eq_prime hk.1 hk.2.1
  have hfix := (burnsideI22P5_M12_isTwoCentral_iff _ hq2).1 (burnsideI22P5_isTwoCentral_map e hk)
  have := h4 k hq2 hfix
  rw [← this]
  exact pow_orderOf_eq_one k

open CFSG.ComponentClassification CFSG.ComponentClassification.M12Cover
  CFSG.ComponentClassification.M12Cover.SylowTable CFSG.ASVolI.ChIJK in
theorem burnsideI22P5_M12_a
    {K : Type} [Group K] [Finite K]
    (hK : CFSG.IsQuasisimple K) (hZ : Subgroup.center K ≠ ⊥)
    (h : CFSG.Blueprint.NativeSporadic.IsSporadic (K ⧸ Subgroup.center K) .M12) :
    TwoCentralInvolutionsLift K := by
  obtain ⟨hZ2, ⟨e⟩⟩ := burnsideI22P5_M12_setup hK hZ h
  intro t' ht'
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective t'
  exact ⟨k, burnsideI22P5_M12_strong hK hZ2 e k ht', rfl⟩

open CFSG.ComponentClassification CFSG.ComponentClassification.M12Cover
  CFSG.ComponentClassification.M12Cover.SylowTable CFSG.ASVolI.ChIJK in
theorem burnsideI22P5_M12_b1
    {K : Type} [Group K] [Finite K]
    (hK : CFSG.IsQuasisimple K) (hZ : Subgroup.center K ≠ ⊥)
    (h : CFSG.Blueprint.NativeSporadic.IsSporadic (K ⧸ Subgroup.center K) .M12) :
    NonTwoCentralInvolutionsLiftToOrderFour K := by
  obtain ⟨hZ2, ⟨e⟩⟩ := burnsideI22P5_M12_setup hK hZ h
  obtain ⟨t, ht, hZt, -, h0⟩ := burnsideI22P5_M12_lift hK hZ2 e
  intro t' ht2 ht1 hnc
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective t'
  have hq2 : orderOf (e (k : K ⧸ Subgroup.center K)) = 2 := by
    rw [MulEquiv.orderOf_eq]
    exact orderOf_eq_prime ht2 ht1
  have hne : ¬ fixedCount (e (k : K ⧸ Subgroup.center K)) = 4 := by
    intro hfix
    apply hnc
    have := burnsideI22P5_isTwoCentral_map e.symm
      ((burnsideI22P5_M12_isTwoCentral_iff _ hq2).2 hfix)
    simpa using this
  have h0' : fixedCount (e (k : K ⧸ Subgroup.center K)) = 0 := by
    rcases fixedCount_of_orderOf_eq_two _ hq2 with h | h
    · exact absurd h hne
    · exact h
  obtain ⟨-, hk4⟩ := h0 k hq2 h0'
  exact ⟨k, hk4, rfl⟩

open CFSG.ComponentClassification CFSG.ComponentClassification.M12Cover
  CFSG.ComponentClassification.M12Cover.SylowTable CFSG.ASVolI.ChIJK in
theorem burnsideI22P5_M12_b2
    {K : Type} [Group K] [Finite K]
    (hK : CFSG.IsQuasisimple K) (hZ : Subgroup.center K ≠ ⊥)
    (h : CFSG.Blueprint.NativeSporadic.IsSporadic (K ⧸ Subgroup.center K) .M12) :
    OuterInvolutionsInvertOrderFour K := by
  intro α hα hα1
  obtain ⟨hZ2, ⟨e⟩⟩ := burnsideI22P5_M12_setup hK hZ h
  obtain ⟨t, ht, hZt, -, -⟩ := burnsideI22P5_M12_lift hK hZ2 e
  let πK : K →* CFSG.Blueprint.NativeSporadic.M12 :=
    e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K))
  have hπK : Function.Surjective πK := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hkerK : πK.ker = Subgroup.zpowers t := by
    rw [← hZt]
    ext l
    simp only [πK, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  obtain ⟨H, hG, hF, L, hN, φ, p, π', hpL, hp2, hpact, hLq, ht', hZL, hπ', hker', hCL, hπφ⟩ :=
    burnsideI22P5_ext hK ht hZt πK hπK hkerK α hα hα1
  haveI : Finite H := hF
  have hkerZL : π'.ker = Subgroup.center L := by rw [hker', hZL]
  obtain ⟨hkey, -⟩ := ctss_m12_central_double_cover_external_involution_conjugacy_frontier hLq ht'
    hZL ⟨CFSG.ComponentClassification.CentralCover.quotientEquivOfKerEqCenter π' hπ' hkerZL⟩ hCL
  obtain ⟨v, hv2, hvp, -⟩ := hkey p hpL hp2
  obtain ⟨k, rfl⟩ := φ.surjective v
  have hk2 : k ^ 2 = t := by
    apply φ.injective
    rw [map_pow]
    exact hv2
  have hαk : α k = k⁻¹ := by
    have hvv : ((φ t : L) : H) = ((φ k : L) : H) * ((φ k : L) : H) := by
      rw [← hk2, sq, map_mul]; rfl
    rw [hvv] at hvp
    have h1 : p * ((φ k : L) : H) * p⁻¹ = (((φ k : L) : H))⁻¹ := by
      have e1 : p * ((φ k : L) : H)⁻¹ = ((φ k : L) : H) * p := by
        have := hvp
        calc p * ((φ k : L) : H)⁻¹ = ((φ k : L) : H)⁻¹ * (((φ k : L) : H) * p *
            ((φ k : L) : H)⁻¹) := by group
          _ = ((φ k : L) : H)⁻¹ * (((φ k : L) : H) * ((φ k : L) : H) * p) := by rw [this]
          _ = ((φ k : L) : H) * p := by group
      calc p * ((φ k : L) : H) * p⁻¹ = (p * ((φ k : L) : H)⁻¹ * p⁻¹)⁻¹ := by group
        _ = (((φ k : L) : H) * p * p⁻¹)⁻¹ := by rw [e1]
        _ = _ := by group
    have h2 : φ (α k) = φ k⁻¹ := by
      apply Subtype.ext
      rw [← hpact, h1, map_inv, Subgroup.coe_inv]
    exact φ.injective h2
  exact burnsideI22P5_b2_of_sq ht hZt (burnsideI22P5_M12_strong hK hZ2 e) α hk2 hαk

open CFSG.ASVolI.ChIJK in
theorem burnsideI22P5_HS_isTwoCentral_iff
    {Y : Type} [Group Y]
    (hY : CFSG.Blueprint.NativeSporadic.IsSporadic Y .HS) (y : Y) (hy : orderOf y = 2) :
    IsTwoCentralInvolution y ↔ Nat.card (Subgroup.centralizer ({y} : Set Y)) = 7680 := by
  have hcard := CFSG.EvenSporadicStandard.HSStd.Zassenhaus.card_eq_of_isSporadic_hs hY
  haveI : Finite Y := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hy2 : y ^ 2 = 1 := by rw [← hy]; exact pow_orderOf_eq_one y
  have hy1 : y ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hy
    exact absurd hy (by norm_num)
  let S : Sylow 2 Y := default
  have hS : Nat.card S = 512 := by
    rw [Sylow.card_eq_multiplicity S, hcard]
    have : (44352000 : ℕ).factorization 2 = 9 := by
      rw [show (44352000 : ℕ) = 2 ^ 9 * 86625 by norm_num,
        Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
        Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
        Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
    rw [this]
    norm_num
  rw [burnsideI22P5_isTwoCentral_iff_card S hy2 hy1, hS]
  rcases CFSG.EvenSporadicStandard.HSStd.Zassenhaus.card_centralizer_of_involution_hs hY y hy with
    h | h
  · rw [h]; norm_num
  · rw [h]; norm_num

open CFSG.ASVolI.ChIJK in
theorem burnsideI22P5_HS_strong
    {K : Type} [Group K] [Finite K]
    (hK : CFSG.IsQuasisimple K) (hZ : Subgroup.center K ≠ ⊥)
    (h : CFSG.Blueprint.NativeSporadic.IsSporadic (K ⧸ Subgroup.center K) .HS) :
    ∀ k : K, IsTwoCentralInvolution (k : K ⧸ Subgroup.center K) → k ^ 2 = 1 := by
  haveI : Group.IsPerfect K := hK.1
  have hZ2 := CFSG.EvenSporadicStandard.HSStd.Zassenhaus.card_center_eq_two_of_ne_bot this h hZ
  intro k hk
  have hq2 : orderOf (k : K ⧸ Subgroup.center K) = 2 := orderOf_eq_prime hk.1 hk.2.1
  have hC := (burnsideI22P5_HS_isTwoCentral_iff h _ hq2).1 hk
  exact CFSG.EvenSporadicStandard.HSStd.PumpHS.sq_eq_one_of_card_centralizer this hZ2 h hq2 hC

open CFSG.ASVolI.ChIJK in
theorem burnsideI22P5_HS_a
    {K : Type} [Group K] [Finite K]
    (hK : CFSG.IsQuasisimple K) (hZ : Subgroup.center K ≠ ⊥)
    (h : CFSG.Blueprint.NativeSporadic.IsSporadic (K ⧸ Subgroup.center K) .HS) :
    TwoCentralInvolutionsLift K := by
  intro t' ht'
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective t'
  exact ⟨k, burnsideI22P5_HS_strong hK hZ h k ht', rfl⟩

open CFSG.ASVolI.ChIJK in
theorem burnsideI22P5_HS_b1
    {K : Type} [Group K] [Finite K]
    (hK : CFSG.IsQuasisimple K) (hZ : Subgroup.center K ≠ ⊥)
    (h : CFSG.Blueprint.NativeSporadic.IsSporadic (K ⧸ Subgroup.center K) .HS) :
    NonTwoCentralInvolutionsLiftToOrderFour K := by
  haveI : Group.IsPerfect K := hK.1
  have hZ2 := CFSG.EvenSporadicStandard.HSStd.Zassenhaus.card_center_eq_two_of_ne_bot this h hZ
  obtain ⟨t, ht, hZt⟩ := burnsideI22P5_exists_t hZ2
  obtain ⟨e⟩ := h
  let eH : K ⧸ Subgroup.center K ≃* CFSG.Sporadic.Schreier.hsP :=
    (e : K ⧸ Subgroup.center K ≃* CFSG.Blueprint.NativeSporadic.HS).trans
      CFSG.Sporadic.Schreier.hsPermEquiv
  let ρ : K →* CFSG.Sporadic.Schreier.hsP :=
    eH.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K))
  have hρ : Function.Surjective ρ := eH.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : ρ.ker = Subgroup.zpowers t := by
    rw [← hZt]
    ext l
    simp only [ρ, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  intro t' ht2 ht1 hnc
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective t'
  have hq2 : orderOf (k : K ⧸ Subgroup.center K) = 2 := orderOf_eq_prime ht2 ht1
  have hC : ¬ Nat.card (Subgroup.centralizer ({(k : K ⧸ Subgroup.center K)} :
      Set (K ⧸ Subgroup.center K))) = 7680 := fun hC =>
    hnc ((burnsideI22P5_HS_isTwoCentral_iff ⟨e⟩ _ hq2).2 hC)
  have hC' : Nat.card (Subgroup.centralizer ({(k : K ⧸ Subgroup.center K)} :
      Set (K ⧸ Subgroup.center K))) = 2880 := by
    rcases CFSG.EvenSporadicStandard.HSStd.Zassenhaus.card_centralizer_of_involution_hs ⟨e⟩ _ hq2
      with h | h
    · exact absurd h hC
    · exact h
  let y : CFSG.Sporadic.Schreier.hsP := eH (k : K ⧸ Subgroup.center K)
  have hy2 : orderOf y = 2 := by rw [MulEquiv.orderOf_eq]; exact hq2
  have hCy : Nat.card (Subgroup.centralizer ({y} : Set CFSG.Sporadic.Schreier.hsP)) = 2880 :=
    (CFSG.EvenSporadicStandard.HSStd.Zassenhaus.card_centralizer_equiv eH _).trans hC'
  obtain ⟨hmem2, hord2⟩ := CFSG.EvenSporadicStandard.HSStd.hsT2_mem_ord
  let b : CFSG.Sporadic.Schreier.hsP := ⟨CFSG.Sporadic.SmallOddCore.hsT2, hmem2⟩
  have hb2 : orderOf b = 2 := by rw [← Subgroup.orderOf_coe]; exact hord2
  have hCb : Nat.card (Subgroup.centralizer ({b} : Set CFSG.Sporadic.Schreier.hsP)) = 2880 := by
    rw [CFSG.EvenSporadicStandard.HSStd.Zassenhaus.card_centralizer_hsP]
    exact (CFSG.Sporadic.SmallOddCore.hs_reps).2.2.2.1
  have hconj : IsConj y b :=
    CFSG.EvenSporadicStandard.HSStd.Zassenhaus.hsInvolutionData_hsP.isConj_of_card_eq hy2 hb2
      (hCy.trans hCb.symm)
  obtain ⟨c, hc⟩ := isConj_iff.1 hconj
  have hW : ((ρ k : CFSG.Sporadic.Schreier.hsP) : Equiv.Perm (Fin 3850)) =
      ((c⁻¹ : CFSG.Sporadic.Schreier.hsP) : Equiv.Perm (Fin 3850)) *
        CFSG.Sporadic.SmallOddCore.hsT2 *
        ((c⁻¹ : CFSG.Sporadic.Schreier.hsP) : Equiv.Perm (Fin 3850))⁻¹ := by
    have h1 : ρ k = c⁻¹ * b * c := by
      show y = c⁻¹ * b * c
      rw [← hc]; group
    rw [h1]
    simp [b]
  have hsq := CFSG.ComponentClassification.GSThmB.CovHS.sq_lift
    (⟨Group.IsPerfect.commutator_eq_top, hK.2.1⟩ : CFSG.Assembly.IsQuasisimple K) ht hZt ρ hρ
    hker (c⁻¹).2 hW
  have ht1' : t ≠ 1 := by
    intro h; rw [h, orderOf_one] at ht; exact absurd ht (by norm_num)
  have ht2' : t ^ 2 = 1 := by rw [← ht]; exact pow_orderOf_eq_one t
  refine ⟨k, ?_, rfl⟩
  have hk2 : k ^ 2 = t := by rw [sq]; exact hsq
  have h := orderOf_eq_prime_pow (p := 2) (n := 1) (x := k) (by simpa using (by rw [hk2]; exact ht1' : ¬ k ^ 2 = 1))
    (by rw [show 2 ^ (1 + 1) = 2 * 2 from rfl, pow_mul, hk2, ht2'])
  simpa using h

theorem burnsideI22P5_norm_inv {K : Type} [Group K] (α : K ≃* K) (hα : ∀ k, α (α k) = k)
    (g : K) : α (g * (α g)⁻¹) = (g * (α g)⁻¹)⁻¹ := by
  rw [map_mul, map_inv, hα]
  group

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore
  CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Schreier CFSG.EvenSporadicStandard.TwoHS in
theorem burnsideI22P5_HS_outer_witness
    {x g₀ : Equiv.Perm (Fin 3850)} (hg₀ : g₀ ∈ hsP) {r : ClassRow} (hr : r ∈ hsRows)
    (hout : r.outer = true) (hxg : x = g₀ * tp 3850 r.rep * g₀⁻¹) :
    ∃ h₀ ∈ hsP, ∃ g₁ ∈ hsP, h₀ * x * h₀⁻¹ * x⁻¹ = g₁ * hsT2 * g₁⁻¹ := by
  have hperm := hsRows_permOK
  have ht₁ : Rep 3850 (hsCentTbl 5) (tp 3850 (hsCentTbl 5)) := by
    obtain ⟨r', hr', hrep⟩ : ∃ r' ∈ hsRows, r'.rep = hsCentTbl 5 := by
      refine ⟨_, List.mem_cons_self, ?_⟩
      simp
    have h := rep_tp (hperm r' hr')
    rw [hrep] at h
    exact h
  have ht₂ : Rep 3850 (hsCentTbl 12) hsT2 := by
    obtain ⟨r', hr', hrep⟩ : ∃ r' ∈ hsRows, r'.rep = hsCentTbl 12 := by
      refine ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩
      simp
    have h := rep_tp (hperm r' hr')
    rw [hrep] at h
    exact h
  have key : ∀ c : ℕ, harFourOK c = true → r.rep = harRho c →
      ∃ h₀ ∈ hsP, ∃ g₁ ∈ hsP, h₀ * x * h₀⁻¹ * x⁻¹ = g₁ * hsT2 * g₁⁻¹ := by
    intro c hc hrep
    have hρ : Rep 3850 (harRho c) (tp 3850 (harRho c)) := by
      have h := rep_tp (hperm r hr)
      rw [hrep] at h
      exact h
    rw [hrep] at hxg
    obtain ⟨⟨x', c₂, c₃, hc₂, hc₃, hx', -, h3⟩, -⟩ := harFour_spec hc hρ ht₁ ht₂
    refine ⟨g₀ * c₃ * g₀⁻¹, hsP.mul_mem (hsP.mul_mem hg₀ hc₃) (hsP.inv_mem hg₀), g₀ * c₂,
      hsP.mul_mem hg₀ hc₂, ?_⟩
    have e1 : c₃ * tp 3850 (harRho c) * c₃⁻¹ * (tp 3850 (harRho c))⁻¹ = x' := by
      rw [h3]; group
    rw [hxg]
    calc g₀ * c₃ * g₀⁻¹ * (g₀ * tp 3850 (harRho c) * g₀⁻¹) * (g₀ * c₃ * g₀⁻¹)⁻¹ *
          (g₀ * tp 3850 (harRho c) * g₀⁻¹)⁻¹
        = g₀ * (c₃ * tp 3850 (harRho c) * c₃⁻¹ * (tp 3850 (harRho c))⁻¹) * g₀⁻¹ := by group
      _ = g₀ * (c₂ * hsT2 * c₂⁻¹) * g₀⁻¹ := by rw [e1, hx']
      _ = g₀ * c₂ * hsT2 * (g₀ * c₂)⁻¹ := by group
  simp only [hsRows, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact absurd hout (by simp)
  · exact absurd hout (by simp)
  · exact key 0 harFourOK_true.1 (by simp [harRho])
  · exact key 1 harFourOK_true.2 (by simp [harRho])

open CFSG.ASVolI.ChIJK CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Schreier in
theorem burnsideI22P5_HS_b2
    {K : Type} [Group K] [Finite K]
    (hK : CFSG.IsQuasisimple K) (hZ : Subgroup.center K ≠ ⊥)
    (h : CFSG.Blueprint.NativeSporadic.IsSporadic (K ⧸ Subgroup.center K) .HS) :
    OuterInvolutionsInvertOrderFour K := by
  intro α hα hα1
  haveI : Group.IsPerfect K := hK.1
  have hZ2 := CFSG.EvenSporadicStandard.HSStd.Zassenhaus.card_center_eq_two_of_ne_bot this h hZ
  obtain ⟨t, ht, hZt⟩ := burnsideI22P5_exists_t hZ2
  have hstrong := burnsideI22P5_HS_strong hK hZ h
  obtain ⟨e⟩ := h
  let eH : K ⧸ Subgroup.center K ≃* hsP :=
    (e : K ⧸ Subgroup.center K ≃* CFSG.Blueprint.NativeSporadic.HS).trans hsPermEquiv
  let ρ : K →* hsP := eH.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K))
  have hρ : Function.Surjective ρ := eH.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : ρ.ker = Subgroup.zpowers t := by
    rw [← hZt]
    ext l
    simp only [ρ, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  let β : MulAut hsP := burnsideI22P5_ind eH α
  have hβ : ∀ k, ρ (α k) = β (ρ k) := fun k => (burnsideI22P5_ind_apply eH α k).symm
  obtain ⟨eAut, heAut, -⟩ := hs_full_automorphism_model
  obtain ⟨x, hx⟩ := eAut.surjective β
  have hxι : ∀ z : hsP, ((β z : hsP) : Equiv.Perm (Fin 3850)) =
      (x : Equiv.Perm (Fin 3850)) * z * (x : Equiv.Perm (Fin 3850))⁻¹ := fun z => by
    rw [← hx, heAut x z, Subgroup.coe_inv]
  have hββ : β * β = 1 := by
    refine MulEquiv.ext fun z => ?_
    obtain ⟨y, rfl⟩ := hρ z
    rw [MulAut.mul_apply, ← hβ, ← hβ, hα]
    rfl
  have hxx : x * x = 1 := eAut.injective (by rw [map_mul, hx, hββ, map_one])
  have hxP : (x : Equiv.Perm (Fin 3850)) ∉ hsP := by
    intro hxP
    obtain ⟨X, hX⟩ := hρ ⟨x, hxP⟩
    have hβc : ∀ z, β z = ⟨x, hxP⟩ * z * (⟨x, hxP⟩ : hsP)⁻¹ := fun z =>
      Subtype.ext (by rw [hxι, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv])
    have hαX : α = MulAut.conj X :=
      CFSG.ComponentClassification.GSThmB.Cov.eq_conj_of_comp ‹Group.IsPerfect K› ρ
        (by rw [hker, hZt]) α X fun y => by rw [hβ, hβc, hX]
    exact hα1 X hαX
  have hxo : orderOf (x : Equiv.Perm (Fin 3850)) = 2 := by
    have hx2 : (x : Equiv.Perm (Fin 3850)) ^ 2 = 1 := by
      have := congrArg Subtype.val hxx
      simpa [sq] using this
    exact orderOf_eq_prime hx2 fun h1 => hxP (h1 ▸ hsP.one_mem)
  obtain ⟨-, -, -, hrows, hcover, -⟩ := hs_involution_centralizers
  obtain ⟨r, hr, g₀, hg₀, hxg⟩ := hcover (x : Equiv.Perm (Fin 3850)) x.2 hxo
  have hout : r.outer = true := by
    by_contra hne
    have hrP : tp 3850 r.rep ∈ hsP := by
      by_contra hn
      exact hne (((hrows r hr).2.2.1).2 hn)
    exact hxP (by rw [hxg]; exact hsP.mul_mem (hsP.mul_mem hg₀ hrP) (hsP.inv_mem hg₀))
  obtain ⟨h₀, hh₀, g₁, hg₁, hcomm⟩ := burnsideI22P5_HS_outer_witness hg₀ hr hout hxg
  obtain ⟨ĥ, hĥ⟩ := hρ ⟨h₀, hh₀⟩
  have hρk : ((ρ (ĥ * (α ĥ)⁻¹) : hsP) : Equiv.Perm (Fin 3850)) = g₁ * hsT2 * g₁⁻¹ := by
    rw [map_mul, map_inv, hβ, hĥ, Subgroup.coe_mul, Subgroup.coe_inv, hxι]
    rw [← hcomm]
    simp only [Subgroup.coe_mk]
    group
  have hsq := CFSG.ComponentClassification.GSThmB.CovHS.sq_lift
    (⟨Group.IsPerfect.commutator_eq_top, hK.2.1⟩ : CFSG.Assembly.IsQuasisimple K) ht hZt ρ hρ
    hker hg₁ hρk
  exact burnsideI22P5_b2_of_sq ht hZt hstrong α (by rw [sq]; exact hsq)
    (burnsideI22P5_norm_inv α hα ĥ)

open CFSG.Blueprint CFSG.Blueprint.Chevalley in
theorem burnsideI22P5_G2_data
    {G : Type} [Group G] (h : ChevalleyExceptionalModel G .G2 2 2) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 4 ∧
      Nonempty (G ≃* adjointGroup .G2 F) := by
  obtain ⟨-, hm⟩ := h
  obtain ⟨F, hF, hFf, hcard, ⟨e⟩⟩ :=
    CFSG.RankThree.Chevalley.exists_mulEquiv_adjointGroup_of_untwisted hm
  exact ⟨F, hF, hFf, by simpa using hcard, ⟨e.symm⟩⟩

open CFSG.Blueprint CFSG.Blueprint.Chevalley in
theorem burnsideI22P5_G2_card_center
    {K : Type} [Group K] [Finite K] (hK : CFSG.IsQuasisimple K)
    (hZ : Subgroup.center K ≠ ⊥) {F : Type} [Field F] (hF : Nat.card F = 4)
    (e : K ⧸ Subgroup.center K ≃* adjointGroup .G2 F) :
    Nat.card (Subgroup.center K) = 2 := by
  refine burnsideI22P5_card_center_eq_two hK hZ ?_
  rw [CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.card_hopfMultiplier_eq_of_mulEquiv e,
    ← Nat.card_congr (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess _).toEquiv]
  exact (CFSG.LieType.Multipliers.G24.multiplier_G2_four hF).1

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley.G2FieldFour
  CFSG.EvenSmallLie.GTwoFour in
theorem burnsideI22P5_G2_sylow
    {F : Type} [Field F] [Finite F] (hF : Nat.card F = 4) :
    ∃ P : Sylow 2 (adjointGroup .G2 F), (P : Subgroup (adjointGroup .G2 F)) = posU F := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hUC : posUnipotent .G2 F ≤ adjointGroup .G2 F :=
    CFSG.GH74.GLS.IVK.Proofs2.Ivk47.posUnipotent_le_adjointGroup' .G2 F
  have hcardU : Nat.card (posUnipotent .G2 F) = Nat.card F ^ 6 := by
    rw [CFSG.LieType.Chevalley.card_posUnipotent, CFSG.GH74.GLS.IVK.Proofs2.Ivk47.ncard_posRoots_G2]
  have hcardPU : Nat.card (posU F) = 2 ^ (Nat.card (adjointGroup .G2 F)).factorization 2 := by
    have h1 : Nat.card (posU F) = Nat.card (posUnipotent .G2 F) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUC).toEquiv
    have h2 : Nat.card (adjointGroup .G2 F) = 251596800 := by
      rw [CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_G2, hF]
      norm_num [CFSG.Open.ordG2]
    have h3 : (251596800 : ℕ).factorization 2 = 12 := by
      rw [show (251596800 : ℕ) = 2 ^ 12 * 61425 by norm_num,
        Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
        Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
        Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
    rw [h1, hcardU, hF, h2, h3]
    norm_num
  exact ⟨Sylow.ofCard (posU F) hcardPU, Sylow.coe_ofCard _ _⟩

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley.G2FieldFour
  CFSG.EvenSmallLie.GTwoFour CFSG.LieType.Steinberg.CentralExt.G2Four in
theorem burnsideI22P5_G2_isTwoCentral_iff
    {F : Type} [Field F] [Finite F] (hF : Nat.card F = 4)
    (z : adjointGroup .G2 F) (hz : orderOf z = 2) :
    CFSG.ASVolI.ChIJK.IsTwoCentralInvolution z ↔ IsConj z (rootX rootC (1 : F)) := by
  haveI : CharP F 2 := CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour.charP_two_of_card_eq_four hF
  obtain ⟨P, hP⟩ := burnsideI22P5_G2_sylow hF
  have hz2 : z ^ 2 = 1 := by rw [← hz]; exact pow_orderOf_eq_one z
  have hz1 : z ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hz
    exact absurd hz (by norm_num)
  set c₁ : adjointGroup .G2 F := rootX rootC (1 : F) with hc₁
  have hc₁sq : c₁ ^ 2 = 1 := by
    rw [sq, hc₁, ← rootX_add, CharTwo.add_self_eq_zero, rootX_zero]
  have hc₁ne : c₁ ≠ 1 := rootX_ne_one rootC one_ne_zero
  have hc₁U : c₁ ∈ posU F := rootX_mem_posU rootC_mem 1
  have hc₁cent : ∀ u ∈ posU F, u * c₁ = c₁ * u := by
    intro u hu
    have hu' : (u : ModGL .G2 F) ∈ posUnipotent .G2 F := Subgroup.mem_subgroupOf.1 hu
    have := (CFSG.ComponentClassification.UnbalancedCatalog.commute_pinnedX_c_of_mem_posUnipotent
      (1 : F) hu').eq
    exact Subtype.ext this.symm
  constructor
  · rintro ⟨-, -, T, hzT, hTc⟩
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (adjointGroup .G2 F) P T
    have hzT' : z ∈ ((g • P : Sylow 2 (adjointGroup .G2 F)) : Subgroup (adjointGroup .G2 F)) := by
      rw [hg]; exact hzT
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hzT'
    obtain ⟨s, hsP, hsz⟩ := hzT'
    have hsz' : g * s * g⁻¹ = z := hsz
    have hsU : s ∈ posU F := by rw [← hP]; exact hsP
    have hsc : ∀ s' ∈ posU F, s' * s = s * s' := by
      intro s' hs'
      have hx'P : s' ∈ (P : Subgroup (adjointGroup .G2 F)) := by rw [hP]; exact hs'
      have hxT : g * s' * g⁻¹ ∈ (T : Subgroup (adjointGroup .G2 F)) := by
        rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
        exact ⟨s', hx'P, rfl⟩
      have h := hTc _ hxT
      rw [← hsz'] at h
      have := congrArg (fun y => g⁻¹ * y * g) h
      simpa [mul_assoc] using this
    obtain ⟨F', hF'⟩ := eq_rootX_c_of_commute hsU
      (hsc _ (rootX_mem_posU rootR_mem 1)).symm (hsc _ (rootX_mem_posU rootV_mem 1)).symm
      (hsc _ (rootX_mem_posU rootA_mem 1)).symm
    have hF'0 : F' ≠ 0 := by
      rintro rfl
      apply hz1
      rw [← hsz', hF', rootX_zero]; group
    have hconj : IsConj s c₁ := by
      rw [hF']
      exact isConj_rootX_long (by simp [longRoots]) hF'0
    have : IsConj z s := isConj_iff.2 ⟨g⁻¹, by rw [← hsz']; group⟩
    exact this.trans hconj
  · intro hconj
    obtain ⟨g, hg⟩ := isConj_iff.1 hconj
    have hcc : CFSG.ASVolI.ChIJK.IsTwoCentralInvolution c₁ := by
      refine ⟨hc₁sq, hc₁ne, P, ?_, ?_⟩
      · show c₁ ∈ (P : Subgroup (adjointGroup .G2 F))
        rw [hP]; exact hc₁U
      · intro x hx
        have hx' : x ∈ posU F := by rw [← hP]; exact hx
        exact hc₁cent x hx'
    have hmap := burnsideI22P5_isTwoCentral_map (MulAut.conj g⁻¹ : _ ≃* _) hcc
    have : (MulAut.conj g⁻¹ : adjointGroup .G2 F ≃* adjointGroup .G2 F) c₁ = z := by
      rw [← hg, MulAut.conj_apply]
      group
    rwa [this] at hmap

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley.G2FieldFour
  CFSG.EvenSmallLie.GTwoFour CFSG.LieType.Steinberg.CentralExt.G2Four CFSG.ASVolI.ChIJK in
theorem burnsideI22P5_G2_strong
    {K : Type} [Group K] [Finite K] {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 4) (hZ2 : Nat.card (Subgroup.center K) = 2)
    (e : K ⧸ Subgroup.center K ≃* adjointGroup .G2 F) :
    ∀ k : K, IsTwoCentralInvolution (k : K ⧸ Subgroup.center K) → k ^ 2 = 1 := by
  intro k hk
  have hz2 : orderOf (e (k : K ⧸ Subgroup.center K)) = 2 := by
    rw [MulEquiv.orderOf_eq]
    exact orderOf_eq_prime hk.1 hk.2.1
  have hconj := (burnsideI22P5_G2_isTwoCentral_iff hF _ hz2).1 (burnsideI22P5_isTwoCentral_map e hk)
  have := orderOf_eq_two_of_isConj_long_of_quotient hZ2 hF e (γ := rootC) (by simp [longRoots])
    (s := (1 : F)) one_ne_zero (x := k) hconj
  rw [← this]
  exact pow_orderOf_eq_one k

open CFSG.ASVolI.ChIJK in
theorem burnsideI22P5_G2_a
    {K : Type} [Group K] [Finite K] (hK : CFSG.IsQuasisimple K)
    (hZ : Subgroup.center K ≠ ⊥)
    (h : CFSG.Blueprint.ChevalleyExceptionalModel (K ⧸ Subgroup.center K) .G2 2 2) :
    TwoCentralInvolutionsLift K := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := burnsideI22P5_G2_data h
  have hZ2 := burnsideI22P5_G2_card_center hK hZ hF e
  intro t' ht'
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective t'
  exact ⟨k, burnsideI22P5_G2_strong hF hZ2 e k ht', rfl⟩

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley.G2FieldFour
  CFSG.EvenSmallLie.GTwoFour CFSG.LieType.Steinberg.CentralExt.G2Four CFSG.ASVolI.ChIJK in
theorem burnsideI22P5_G2_b1
    {K : Type} [Group K] [Finite K] (hK : CFSG.IsQuasisimple K)
    (hZ : Subgroup.center K ≠ ⊥)
    (h : ChevalleyExceptionalModel (K ⧸ Subgroup.center K) .G2 2 2) :
    NonTwoCentralInvolutionsLiftToOrderFour K := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := burnsideI22P5_G2_data h
  have hZ2 := burnsideI22P5_G2_card_center hK hZ hF e
  haveI : CharP F 2 := CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour.charP_two_of_card_eq_four hF
  haveI : Group.IsPerfect K := hK.1
  intro t' ht2 ht1 hnc
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective t'
  have hz2 : orderOf (e (k : K ⧸ Subgroup.center K)) = 2 := by
    rw [MulEquiv.orderOf_eq]
    exact orderOf_eq_prime ht2 ht1
  have hnconj : ¬ IsConj (e (k : K ⧸ Subgroup.center K)) (rootX rootC (1 : F)) := by
    intro hc
    apply hnc
    have := burnsideI22P5_isTwoCentral_map e.symm
      ((burnsideI22P5_G2_isTwoCentral_iff hF _ hz2).2 hc)
    simpa using this
  have hshort : IsConj (e (k : K ⧸ Subgroup.center K)) (rootX rootV (1 : F)) := by
    rcases CFSG.ComponentClassification.UnbalancedCatalog.even_G2_involutions_conjugate_to_root_elements
      F (ringChar.eq F 2) (e (k : K ⧸ Subgroup.center K)) hz2 with h | h
    · exact absurd h hnconj
    · exact h
  exact ⟨k, orderOf_eq_four_of_isConj_short_of_quotient hZ2 hF e (γ := rootV)
    (by simp [shortRoots]) (s := (1 : F)) one_ne_zero (x := k) hshort, rfl⟩

theorem burnsideI22P5_F4_omega {F : Type} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 4) :
    ∃ ω : F, ω ≠ 0 ∧ ω ≠ 1 ∧ ω ^ 2 = 1 + ω := by
  classical
  haveI := Fintype.ofFinite F
  have hc : Fintype.card F = 4 := by rw [← Nat.card_eq_fintype_card]; exact hF
  have hlt : ({0, 1} : Finset F).card < (Finset.univ : Finset F).card := by
    rw [Finset.card_univ, hc]
    exact lt_of_le_of_lt Finset.card_le_two (by norm_num)
  obtain ⟨ω, -, hω⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hω
  obtain ⟨hω0, hω1⟩ := hω
  refine ⟨ω, hω0, hω1, ?_⟩
  have hpow : ω ^ 4 = ω := by
    have := FiniteField.pow_card ω
    rwa [hc] at this
  have h1 : ω * ((ω - 1) * (ω ^ 2 + ω + 1)) = 0 := by linear_combination hpow
  have h2 : ω ^ 2 + ω + 1 = 0 := by
    rcases mul_eq_zero.1 h1 with h | h
    · exact absurd h hω0
    · rcases mul_eq_zero.1 h with h | h
      · exact absurd (sub_eq_zero.1 h) hω1
      · exact h
  have h2' : (2 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 2
  linear_combination h2 - (ω + 1) * h2'

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley.G2FieldFour in
theorem burnsideI22P5_G2_b2_core
    {K : Type} [Group K] {F : Type} [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = 4) {t : K} (ht : orderOf t = 2)
    (hZt : Subgroup.center K = Subgroup.zpowers t)
    (e : K ⧸ Subgroup.center K ≃* adjointGroup .G2 F)
    (hshort : ∀ y : K, e (y : K ⧸ Subgroup.center K) = rootX rootV (1 : F) → y * y = t)
    (α : K ≃* K) (hα : ∀ k, α (α k) = k)
    (hfrob : ∀ (k : K) (s : F), e (k : K ⧸ Subgroup.center K) = rootX rootV s →
      e ((α k : K) : K ⧸ Subgroup.center K) = rootX rootV (s ^ 2)) :
    ∃ k : K, k ^ 2 = t ∧ α k = k⁻¹ := by
  have ht1 : t ≠ 1 := by
    intro h; rw [h, orderOf_one] at ht; exact absurd ht (by norm_num)
  have ht2 : t * t = 1 := by rw [← sq, ← ht]; exact pow_orderOf_eq_one t
  have htZ : t ∈ Subgroup.center K := hZt ▸ Subgroup.mem_zpowers t
  have hαt : α t = t := by
    have hmem : α t ∈ Subgroup.center K := by
      have := (Subgroup.characteristic_iff_map_eq.mp (inferInstance : (Subgroup.center K).Characteristic)
        (α : MulAut K))
      rw [← this]; exact ⟨t, htZ, rfl⟩
    rw [hZt] at hmem
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hmem
    have h := burnsideI22P5_lift_eq ht hZt (a := (1 : K)) (b := α t) (by
      rw [QuotientGroup.eq, hZt]; simpa using hmem)
    rcases h with h | h
    · exact absurd (α.injective (h.trans α.map_one.symm)) ht1
    · rw [h]; group
  obtain ⟨ω, hω0, hω1, hω2⟩ := burnsideI22P5_F4_omega hF
  obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (e.symm (rootX rootV (1 : F)))
  obtain ⟨j, hj⟩ := QuotientGroup.mk_surjective (e.symm (rootX rootV ω))
  have hm' : e (m : K ⧸ Subgroup.center K) = rootX rootV (1 : F) := by rw [hm]; simp
  have hj' : e (j : K ⧸ Subgroup.center K) = rootX rootV ω := by rw [hj]; simp
  have hmm : m * m = t := hshort m hm'
  have hmj : e ((m * j : K) : K ⧸ Subgroup.center K) = rootX rootV (1 + ω) := by
    rw [QuotientGroup.mk_mul, map_mul, hm', hj', ← rootX_add]
  have hαm : e ((α m : K) : K ⧸ Subgroup.center K) = rootX rootV (1 : F) := by
    have := hfrob m 1 hm'; simpa using this
  have hαj : e ((α j : K) : K ⧸ Subgroup.center K) = rootX rootV (1 + ω) := by
    have := hfrob j ω hj'; rwa [hω2] at this
  have hαm' : α m = m ∨ α m = m * t :=
    burnsideI22P5_lift_eq ht hZt (a := m) (b := α m) (e.injective (by rw [hm', hαm]))
  have hαj' : α j = m * j ∨ α j = m * j * t :=
    burnsideI22P5_lift_eq ht hZt (a := m * j) (b := α j) (e.injective (by rw [hmj, hαj]))
  refine ⟨m, by rw [sq]; exact hmm, ?_⟩
  have hminv : m⁻¹ = m * t := by
    apply inv_eq_of_mul_eq_one_right
    rw [← mul_assoc, hmm, ht2]
  rcases hαm' with h | h
  · exfalso
    have hαα := hα j
    rcases hαj' with h' | h'
    · rw [h', map_mul, h, h'] at hαα
      have : t * j = j := by
        calc t * j = (m * m) * j := by rw [hmm]
          _ = m * (m * j) := by rw [mul_assoc]
          _ = j := hαα
      exact ht1 (by simpa using this)
    · rw [h', map_mul, map_mul, h, h', hαt] at hαα
      have : t * j = j := by
        calc t * j = (m * m) * j * (t * t) := by rw [hmm, ht2, mul_one]
          _ = m * (m * j * t) * t := by group
          _ = j := hαα
      exact ht1 (by simpa using this)
  · rw [h, hminv]

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.G2FieldFour CFSG.EvenSmallLie.GTwoFour
  CFSG.LieType.Steinberg.CentralExt.G2Four CFSG.ASVolI.ChIJK in
theorem burnsideI22P5_G2_b2
    {K : Type} [Group K] [Finite K] (hK : CFSG.IsQuasisimple K)
    (hZ : Subgroup.center K ≠ ⊥)
    (h : ChevalleyExceptionalModel (K ⧸ Subgroup.center K) .G2 2 2) :
    OuterInvolutionsInvertOrderFour K := by
  intro α hα hα1
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := burnsideI22P5_G2_data h
  have hZ2 := burnsideI22P5_G2_card_center hK hZ hF e
  haveI : CharP F 2 :=
    CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour.charP_two_of_card_eq_four hF
  haveI : Group.IsPerfect K := hK.1
  obtain ⟨t, ht, hZt⟩ := burnsideI22P5_exists_t hZ2
  have ht1 : t ≠ 1 := by
    intro h; rw [h, orderOf_one] at ht; exact absurd ht (by norm_num)
  have ht2 : t * t = 1 := by rw [← sq, ← ht]; exact pow_orderOf_eq_one t
  let X := adjointGroup .G2 F
  let αX : MulAut X := burnsideI22P5_ind e α
  have hαX2 : orderOf αX = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · have : αX * αX = 1 := by
        refine MulEquiv.ext fun x => ?_
        obtain ⟨k, rfl⟩ := e.surjective x
        obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective k
        show αX (αX (e (k : K ⧸ Subgroup.center K))) = e (k : K ⧸ Subgroup.center K)
        rw [show αX = burnsideI22P5_ind e α from rfl, burnsideI22P5_ind_apply,
          burnsideI22P5_ind_apply, hα]
      rw [sq]; exact this
    · intro h1
      apply hα1 1
      apply burnsideI22P5_ind_injective e
      rw [burnsideI22P5_ind_conj]
      refine h1.trans ?_
      refine MulEquiv.ext fun x => ?_
      simp
  have hαXout : αX ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner X := by
    rintro ⟨x, hx⟩
    obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective (e.symm x)
    apply hα1 g
    apply burnsideI22P5_ind_injective e
    rw [burnsideI22P5_ind_conj]
    have : e (g : K ⧸ Subgroup.center K) = x := by rw [hg]; simp
    rw [this]
    exact hx.symm
  obtain ⟨x, hx⟩ := CFSG.EvenSmallLie.GTwoFour.exists_conj_eq_frobenius hF (frobenius F 2)
    (fun c => by simp [frobenius_def]) hαX2 hαXout
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective (e.symm x)
  have hgx : e (g : K ⧸ Subgroup.center K) = x := by rw [hg]; simp
  let α' : MulAut K := MulAut.conj g * α * (MulAut.conj g)⁻¹
  have hα'k : ∀ k, α' k = g * α (g⁻¹ * k * g) * g⁻¹ := by
    intro k
    simp [α', MulAut.mul_apply, MulAut.conj_apply, MulAut.inv_apply, MulAut.conj_symm_apply]
  have hα'α' : ∀ k, α' (α' k) = k := by
    intro k
    rw [hα'k, hα'k k]
    have : g⁻¹ * (g * α (g⁻¹ * k * g) * g⁻¹) * g = α (g⁻¹ * k * g) := by group
    rw [this, hα, show g * (g⁻¹ * k * g) * g⁻¹ = k by group]
  have hindα' : burnsideI22P5_ind e α' = MulAut.conj x * αX * (MulAut.conj x)⁻¹ := by
    simp only [α', map_mul, map_inv, burnsideI22P5_ind_conj, hgx]
    rfl
  have hfrob' : ∀ (k : K) (s : F), e (k : K ⧸ Subgroup.center K) = rootX rootV s →
      e ((α' k : K) : K ⧸ Subgroup.center K) = rootX rootV (s ^ 2) := by
    intro k s hk
    rw [← burnsideI22P5_ind_apply, hindα', hk]
    apply Subtype.ext
    rw [hx]
    show Units.map (entrywiseHom (frobenius F 2)) (pinnedX .G2 F rootV s) = pinnedX .G2 F rootV (s ^ 2)
    rw [show pinnedX .G2 F rootV (s ^ 2) = pinnedX .G2 F rootV (frobenius F 2 s) by
      rw [frobenius_def]]
    exact Units.ext (entrywise_pinnedX (frobenius F 2) rootV s)
  let πK : K →* adjointGroup .G2 F := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K))
  have hπK : Function.Surjective πK := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hπker : ∀ k, πK k = 1 ↔ k = 1 ∨ k = t := by
    intro k
    show e (k : K ⧸ Subgroup.center K) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff, hZt]
    constructor
    · intro hk
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hk
      have := burnsideI22P5_lift_eq ht hZt (a := (1 : K)) (b := k) (by
        rw [QuotientGroup.eq, hZt]; simpa using hk)
      rcases this with h | h
      · exact Or.inl h
      · exact Or.inr (by rw [h]; group)
    · rintro (h | h)
      · rw [h]; exact Subgroup.one_mem _
      · rw [h]; exact Subgroup.mem_zpowers t
  have hshort : ∀ y : K, e (y : K ⧸ Subgroup.center K) = rootX rootV (1 : F) → y * y = t := by
    intro y hy
    exact mul_self_eq_of_isConj_rootX_v (π := πK) (z := t) ht1 hπker hF hπK
      (fun k hk => by
        have := (hπker k).1 hk
        rw [hZt]
        rcases this with h | h
        · rw [h]; exact Subgroup.one_mem _
        · rw [h]; exact Subgroup.mem_zpowers t) (m := y) (by rw [show πK y = rootX rootV 1 from hy])
  obtain ⟨k', hk'2, hk'⟩ := burnsideI22P5_G2_b2_core hF ht hZt e hshort α' hα'α' hfrob'
  have htc : ∀ y : K, y * t = t * y := fun y => Subgroup.mem_center_iff.1 (hZt ▸ Subgroup.mem_zpowers t) y
  have hk2 : (g⁻¹ * k' * g) ^ 2 = t := by
    have h1 : (g⁻¹ * k' * g) ^ 2 = g⁻¹ * (k' ^ 2) * g := by simp only [sq]; group
    rw [h1, hk'2, htc g⁻¹, mul_assoc, inv_mul_cancel, mul_one]
  have hαk : α (g⁻¹ * k' * g) = (g⁻¹ * k' * g)⁻¹ := by
    have h1 := hα'k k'
    rw [hk'] at h1
    have : α (g⁻¹ * k' * g) = g⁻¹ * k'⁻¹ * g := by
      have h2 : α (g⁻¹ * k' * g) = g⁻¹ * (g * α (g⁻¹ * k' * g) * g⁻¹) * g := by group
      rw [h2, ← h1]
    rw [this]; group
  exact burnsideI22P5_b2_of_sq ht hZt (burnsideI22P5_G2_strong hF hZ2 e) α hk2 hαk

open CFSG.ASVolI.ChIJK in
theorem burnsideI22P5_twoResidual_le {G : Type} [Group G] (H : Subgroup G) :
    twoResidual H ≤ H :=
  Subgroup.map_subtype_le _

open CFSG.ASVolI.ChIJK in
theorem burnsideI22P5_twoResidual_le_of_index {G : Type} [Group G] (H : Subgroup G)
    (M : Subgroup H) (hM : M.Normal) (n : ℕ) (hn : M.index = 2 ^ n) :
    twoResidual H ≤ M.map H.subtype :=
  Subgroup.map_mono (sInf_le ⟨hM, n, hn⟩)

@[expose] def burnsideI22P5_twoResidualIn {G : Type} [Group G] (H : Subgroup G) : Subgroup H :=
  sInf {N : Subgroup H | N.Normal ∧ ∃ n : ℕ, N.index = 2 ^ n}

open CFSG.ASVolI.ChIJK in
theorem burnsideI22P5_twoResidual_eq {G : Type} [Group G] (H : Subgroup G) :
    twoResidual H = (burnsideI22P5_twoResidualIn H).map H.subtype := rfl

theorem burnsideI22P5_twoResidualIn_normal {G : Type} [Group G] (H : Subgroup G) :
    (burnsideI22P5_twoResidualIn H).Normal := by
  refine ⟨fun x hx g => ?_⟩
  rw [burnsideI22P5_twoResidualIn, Subgroup.mem_sInf] at hx ⊢
  intro N hN
  exact hN.1.conj_mem x (hx N hN) g

theorem burnsideI22P5_twoResidualIn_index {G : Type} [Group G] [Finite G] (H : Subgroup G) :
    ∃ n : ℕ, (burnsideI22P5_twoResidualIn H).index = 2 ^ n := by
  classical
  let S : Set (Subgroup H) := {N : Subgroup H | N.Normal ∧ ∃ n : ℕ, N.index = 2 ^ n}
  have hfin : S.Finite := Set.toFinite S
  have hne : S.Nonempty := ⟨⊤, inferInstance, 0, by simp⟩
  have hclosed : ∀ x ∈ S, ∀ y ∈ S, x ⊓ y ∈ S := by
    intro x hx y hy
    obtain ⟨hxn, a, ha⟩ := hx
    obtain ⟨hyn, b, hb⟩ := hy
    haveI := hxn
    haveI := hyn
    refine ⟨inferInstance, ?_⟩
    have hdvd : (x ⊓ y).index ∣ 2 ^ (a + b) := by
      rw [pow_add, ← ha, ← hb, Subgroup.index_inf]
      exact Nat.mul_dvd_mul (Subgroup.relIndex_dvd_index_of_normal x y) dvd_rfl
    obtain ⟨c, -, hc⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
    exact ⟨c, hc⟩
  have key : sInf S ∈ S := by
    have h := Finset.inf'_mem S hclosed hfin.toFinset (by simpa using hne) id
      (fun i hi => by simpa using hi)
    rwa [Finset.inf'_eq_inf, Finset.inf_id_eq_sInf, Set.Finite.coe_toFinset] at h
  obtain ⟨-, n, hn⟩ := key
  exact ⟨n, hn⟩

theorem burnsideI22P5_odd_mem_twoResidualIn {G : Type} [Group G] [Finite G] (H : Subgroup G)
    (x : H) (hx : Odd (orderOf x)) : x ∈ burnsideI22P5_twoResidualIn H := by
  rw [burnsideI22P5_twoResidualIn, Subgroup.mem_sInf]
  rintro N ⟨hN, n, hn⟩
  haveI := hN
  have h1 : orderOf (x : H ⧸ N) ∣ orderOf x := orderOf_map_dvd (QuotientGroup.mk' N) x
  have h2 : orderOf (x : H ⧸ N) ∣ 2 ^ n := by
    rw [← hn, Subgroup.index_eq_card]
    exact orderOf_dvd_natCard _
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h2
  have hk0 : k = 0 := by
    by_contra hne
    have heven : Even (orderOf (x : H ⧸ N)) := by
      rw [hk]; exact (Nat.even_pow.2 ⟨even_two, hne⟩)
    have hodd : Odd (orderOf (x : H ⧸ N)) := Odd.of_dvd_nat hx h1
    exact (Nat.not_even_iff_odd.2 hodd) heven
  rw [hk0, pow_zero, orderOf_eq_one_iff] at hk
  exact (QuotientGroup.eq_one_iff x).1 hk

@[expose] def burnsideI22P5_conjEquiv {G : Type} [Group G] (H : Subgroup G) (g : G)
    (hg : ∀ h : G, h ∈ H ↔ g * h * g⁻¹ ∈ H) : H ≃* H where
  toFun x := ⟨g * x * g⁻¹, (hg x).1 x.2⟩
  invFun x := ⟨g⁻¹ * x * g, (hg (g⁻¹ * x * g)).2 (by simpa [mul_assoc] using x.2)⟩
  left_inv x := by ext; simp [mul_assoc]
  right_inv x := by ext; simp [mul_assoc]
  map_mul' x y := by ext; simp [mul_assoc]

theorem burnsideI22P5_pCoreOf_conj {G : Type} [Group G] (H : Subgroup G) (g : G)
    (hg : ∀ h : G, h ∈ H ↔ g * h * g⁻¹ ∈ H) {x : G} (hx : x ∈ pCoreOf 2 H) :
    g * x * g⁻¹ ∈ pCoreOf 2 H := by
  obtain ⟨x', hx', rfl⟩ := hx
  have hmem : burnsideI22P5_conjEquiv H g hg x' ∈ (CFSG.pCore 2 ↥H).map
      (burnsideI22P5_conjEquiv H g hg).toMonoidHom := ⟨x', hx', rfl⟩
  rw [(Subgroup.characteristic_iff_map_eq.1 (inferInstance : (CFSG.pCore 2 ↥H).Characteristic))
    (burnsideI22P5_conjEquiv H g hg)] at hmem
  exact ⟨_, hmem, rfl⟩

theorem burnsideI22P5_pCoreOf_le {G : Type} [Group G] (H : Subgroup G) : pCoreOf 2 H ≤ H :=
  Subgroup.map_subtype_le _

theorem burnsideI22P5_pCoreOf_isPGroup {G : Type} [Group G] (H : Subgroup G) :
    IsPGroup 2 (pCoreOf 2 H) :=
  (CFSG.pCore_isPGroup (p := 2) (G := H)).map H.subtype

theorem burnsideI22P5_le_pCoreOf {G : Type} [Group G] (H M : Subgroup G) (hMH : M ≤ H)
    (hM : (M.subgroupOf H).Normal) (hp : IsPGroup 2 M) : M ≤ pCoreOf 2 H := by
  have hp' : IsPGroup 2 (M.subgroupOf H) :=
    IsPGroup.of_injective hp (Subgroup.subgroupOfEquivOfLe hMH).toMonoidHom
      (MulEquiv.injective _)
  have h1 : M.subgroupOf H ≤ CFSG.pCore 2 ↥H := le_sSup ⟨hM, hp'⟩
  have h2 := Subgroup.map_mono (f := H.subtype) h1
  rwa [Subgroup.map_subgroupOf_eq_of_le hMH] at h2

theorem burnsideI22P5_pCoreOf_conj_of_normal {G : Type} [Group G] (C N : Subgroup G)
    (hN : ∀ c ∈ C, ∀ n ∈ N, c * n * c⁻¹ ∈ N) :
    ∀ c ∈ C, ∀ q ∈ pCoreOf 2 N, c * q * c⁻¹ ∈ pCoreOf 2 N := by
  intro c hc q hq
  refine burnsideI22P5_pCoreOf_conj N c (fun h => ⟨hN c hc h, fun h' => ?_⟩) hq
  have := hN c⁻¹ (C.inv_mem hc) _ h'
  simpa [mul_assoc] using this

open CFSG.ASVolI.ChIJK in
theorem burnsideI22P5_twoResidual_conj {G : Type} [Group G] (C : Subgroup G) :
    ∀ c ∈ C, ∀ n ∈ twoResidual C, c * n * c⁻¹ ∈ twoResidual C := by
  intro c hc n hn
  obtain ⟨n', hn', rfl⟩ := hn
  exact ⟨⟨c, hc⟩ * n' * ⟨c, hc⟩⁻¹,
    (burnsideI22P5_twoResidualIn_normal C).conj_mem n' hn' ⟨c, hc⟩, rfl⟩

open CFSG.ASVolI.ChIJK in
theorem burnsideI22P5_odd_mem_twoResidual {G : Type} [Group G] [Finite G] (C : Subgroup G)
    {x : G} (hx : x ∈ C) (hodd : Odd (orderOf x)) : x ∈ twoResidual C := by
  refine ⟨⟨x, hx⟩, burnsideI22P5_odd_mem_twoResidualIn C ⟨x, hx⟩ ?_, rfl⟩
  rw [Subgroup.orderOf_mk]
  exact hodd

theorem burnsideI22P5_mem_zpowers_two {K : Type} [Group K] {t : K} (ht : orderOf t = 2) {x : K}
    (hx : x ∈ Subgroup.zpowers t) : x = 1 ∨ x = t := by
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
  have ht2 : t ^ (2 : ℤ) = 1 := by
    rw [zpow_two, ← sq, ← ht]; exact pow_orderOf_eq_one t
  have hn : t ^ n = t ^ (n % 2) := by
    conv_lhs => rw [← Int.emod_add_mul_ediv n 2, zpow_add, zpow_mul]
    rw [ht2, one_zpow, mul_one]
  rcases Int.emod_two_eq_zero_or_one n with h0 | h1
  · left; rw [hn, h0, zpow_zero]
  · right; rw [hn, h1, zpow_one]

theorem burnsideI22P5_eq_or_mul {K X : Type} [Group K] [Group X] (π : K →* X) {t : K}
    (ht : orderOf t = 2) (hker : π.ker = Subgroup.zpowers t) {a b : K} (h : π a = π b) :
    b = a ∨ b = a * t := by
  have hmem : a⁻¹ * b ∈ Subgroup.zpowers t := by
    rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]
  rcases burnsideI22P5_mem_zpowers_two ht hmem with h1 | h1
  · left
    rw [inv_mul_eq_one] at h1
    exact h1.symm
  · right
    rw [← h1]
    group

theorem burnsideI22P5_centralizer_eq_comap {K X : Type} [Group K] [Finite K] [Group X]
    (π : K →* X) (hπ : Function.Surjective π) {t : K} (ht : orderOf t = 2)
    (htc : ∀ y : K, y * t = t * y) (hker : π.ker = Subgroup.zpowers t) (u : K) (S : Subgroup X)
    (hSodd : ¬ 2 ∣ S.index) (hTu : ∀ y : K, π y ∈ S → y * u = u * y) :
    Subgroup.centralizer ({u} : Set K) = (Subgroup.centralizer ({π u} : Set X)).comap π := by
  classical
  set C : Subgroup K := Subgroup.centralizer ({u} : Set K) with hC
  set D : Subgroup K := (Subgroup.centralizer ({π u} : Set X)).comap π with hD
  set T : Subgroup K := S.comap π with hT
  have hmemC : ∀ y : K, y ∈ C ↔ y * u * y⁻¹ = u := fun y => by
    rw [hC, Subgroup.mem_centralizer_singleton_iff, mul_inv_eq_iff_eq_mul]
  have hmemD : ∀ y : K, y ∈ D ↔ π y * π u = π u * π y := fun y => by
    rw [hD, Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
  have hCD : C ≤ D := fun y hy => by
    rw [hmemD, ← map_mul, ← map_mul]
    have := (hmemC y).1 hy
    rw [mul_inv_eq_iff_eq_mul] at this
    rw [this]
  have hTC : T ≤ C := fun y hy => by
    rw [hmemC, mul_inv_eq_iff_eq_mul]; exact hTu y hy
  have ht1 : t ≠ 1 := by
    intro h; rw [h, orderOf_one] at ht; exact absurd ht (by norm_num)
  have ht2 : t * t = 1 := by rw [← sq, ← ht]; exact pow_orderOf_eq_one t
  have hflip : ∀ y ∈ D, y * u * y⁻¹ = u ∨ y * u * y⁻¹ = u * t := by
    intro y hy
    have h1 : π (y * u * y⁻¹) = π u := by
      have := (hmemD y).1 hy
      rw [map_mul, map_mul, map_inv, this, mul_inv_cancel_right]
    exact burnsideI22P5_eq_or_mul π ht hker h1.symm
  have hnotC : ∀ y ∈ D, y ∉ C → y * u * y⁻¹ = u * t := by
    intro y hy hyC
    rcases hflip y hy with h | h
    · exact absurd ((hmemC y).2 h) hyC
    · exact h
  have hle2 : C.relIndex D ≤ 2 := by
    rw [Subgroup.relIndex, Subgroup.index_eq_card]
    let f : D ⧸ C.subgroupOf D → Bool :=
      Quotient.lift (fun y : D => decide ((y : K) * u * (y : K)⁻¹ = u)) (by
        intro a b hab
        have hab := QuotientGroup.leftRel_apply.1 hab
        have hab' : ((a : K)⁻¹ * b) ∈ C := by simpa [Subgroup.mem_subgroupOf] using hab
        have h1 := (hmemC _).1 hab'
        have e : (b : K) * u * (b : K)⁻¹ = (a : K) * u * (a : K)⁻¹ := by
          calc (b : K) * u * (b : K)⁻¹ = (a : K) * ((a : K)⁻¹ * b * u * ((a : K)⁻¹ * b)⁻¹) *
                (a : K)⁻¹ := by group
            _ = (a : K) * u * (a : K)⁻¹ := by rw [h1]
        simp only [e])
    have hf : Function.Injective f := by
      intro p q
      refine Quotient.inductionOn₂ p q (fun a b hab => ?_)
      refine Quotient.sound (QuotientGroup.leftRel_apply.2 ?_)
      rw [Subgroup.mem_subgroupOf]
      simp only [f, Quotient.lift_mk, decide_eq_decide] at hab
      show (a : K)⁻¹ * b ∈ C
      rw [hmemC]
      have hta : ∀ y : K, y⁻¹ * t * y = t := fun y => by
        rw [mul_assoc, ← htc y]; group
      by_cases ha : (a : K) ∈ C
      · have hb : (b : K) ∈ C := by
          rw [hmemC]; exact hab.1 ((hmemC _).1 ha)
        have ha' := (hmemC _).1 ha
        have hb' := (hmemC _).1 hb
        calc (a : K)⁻¹ * b * u * ((a : K)⁻¹ * b)⁻¹ = (a : K)⁻¹ * ((b : K) * u * (b : K)⁻¹) * a := by
              group
          _ = (a : K)⁻¹ * u * a := by rw [hb']
          _ = (a : K)⁻¹ * ((a : K) * u * (a : K)⁻¹) * a := by rw [ha']
          _ = u := by group
      · have hb : (b : K) ∉ C := fun hb => ha (by
          rw [hmemC]; exact hab.2 ((hmemC _).1 hb))
        have ha' := hnotC a a.2 ha
        have hb' := hnotC b b.2 hb
        have e1 : (a : K)⁻¹ * u * a = u * t := by
          calc (a : K)⁻¹ * u * a = (a : K)⁻¹ * (((a : K) * u * (a : K)⁻¹) * t) * a := by
                rw [ha', mul_assoc u t t, ht2, mul_one]
            _ = u * ((a : K)⁻¹ * t * a) := by group
            _ = u * t := by rw [hta]
        calc (a : K)⁻¹ * b * u * ((a : K)⁻¹ * b)⁻¹ = (a : K)⁻¹ * ((b : K) * u * (b : K)⁻¹) * a := by
              group
          _ = (a : K)⁻¹ * (u * t) * a := by rw [hb']
          _ = ((a : K)⁻¹ * u * a) * ((a : K)⁻¹ * t * a) := by group
          _ = (u * t) * t := by rw [e1, hta]
          _ = u := by rw [mul_assoc, ht2, mul_one]
    calc Nat.card (D ⧸ C.subgroupOf D) ≤ Nat.card Bool := Nat.card_le_card_of_injective f hf
      _ = 2 := by simp
  have hrel0 : C.relIndex D ≠ 0 := by
    rw [Subgroup.relIndex]
    exact Subgroup.index_ne_zero_of_finite
  have h1 := Subgroup.relIndex_mul_index hTC
  have h2 := Subgroup.relIndex_mul_index hCD
  have hTidx : T.index = S.index := Subgroup.index_comap_of_surjective S hπ
  have hodd : ¬ 2 ∣ C.relIndex D := fun hd => hSodd (by
    rw [← hTidx, ← h1, ← h2]
    exact Dvd.dvd.mul_left (Dvd.dvd.mul_right hd _) _)
  have hrel1 : C.relIndex D = 1 := by omega
  exact le_antisymm hCD (Subgroup.relIndex_eq_one.1 hrel1)

theorem burnsideI22P5_comap_isPGroup {K X : Type} [Group K] [Group X] (π : K →* X) {t : K}
    (ht : orderOf t = 2) (hker : π.ker = Subgroup.zpowers t) (S : Subgroup X)
    (hS : IsPGroup 2 S) : IsPGroup 2 (S.comap π) := by
  intro y
  obtain ⟨k, hk⟩ := hS ⟨π y, y.2⟩
  have h1 : π ((y : K) ^ (2 ^ k)) = 1 := by
    have := congrArg Subtype.val hk
    simpa [map_pow] using this
  have h2 : (y : K) ^ (2 ^ k) ∈ Subgroup.zpowers t := by
    rw [← hker]; exact h1
  have h3 : ((y : K) ^ (2 ^ k)) ^ 2 = 1 := by
    have ht2 : t ^ 2 = 1 := by rw [← ht]; exact pow_orderOf_eq_one t
    rcases burnsideI22P5_mem_zpowers_two ht h2 with h | h
    · rw [h]; exact one_pow 2
    · rw [h]; exact ht2
  refine ⟨k + 1, Subtype.ext ?_⟩
  show (y : K) ^ (2 ^ (k + 1)) = 1
  rw [pow_succ, pow_mul]
  exact h3

theorem burnsideI22P5_Q_le {K : Type} [Group K] [Finite K] (C T : Subgroup K) (hTC : T ≤ C)
    (hT2 : IsPGroup 2 T) (hTodd : ¬ 2 ∣ T.index) :
    pCoreOf 2 (CFSG.ASVolI.ChIJK.twoResidual C) ≤ T := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := CFSG.ASVolI.ChIJK.twoResidual C with hN
  set Q := pCoreOf 2 N with hQ
  have hNC : N ≤ C := burnsideI22P5_twoResidual_le C
  have hQC : Q ≤ C := (burnsideI22P5_pCoreOf_le N).trans hNC
  have hTp : IsPGroup 2 (T.subgroupOf C) :=
    IsPGroup.of_injective hT2 (Subgroup.subgroupOfEquivOfLe hTC).toMonoidHom (MulEquiv.injective _)
  have hTi : ¬ 2 ∣ (T.subgroupOf C).index := by
    intro hd
    apply hTodd
    rw [← Subgroup.relIndex_mul_index hTC]
    exact Dvd.dvd.mul_right hd _
  let P : Sylow 2 C := hTp.toSylow hTi
  have hQp : IsPGroup 2 (Q.subgroupOf C) :=
    IsPGroup.of_injective (burnsideI22P5_pCoreOf_isPGroup N)
      (Subgroup.subgroupOfEquivOfLe hQC).toMonoidHom (MulEquiv.injective _)
  have hconj : ∀ c ∈ C, ∀ q ∈ Q, c * q * c⁻¹ ∈ Q :=
    burnsideI22P5_pCoreOf_conj_of_normal C N (burnsideI22P5_twoResidual_conj C)
  haveI : (Q.subgroupOf C).Normal := ⟨fun x hx g => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact hconj g g.2 x hx⟩
  have hle := hQp.le_sylow_of_normal P
  intro q hq
  have : (⟨q, hQC hq⟩ : C) ∈ P := hle (by rw [Subgroup.mem_subgroupOf]; exact hq)
  exact this

theorem burnsideI22P5_odd_lift {K X : Type} [Group K] [Group X] (π : K →* X) {t : K}
    (ht : orderOf t = 2) (hker : π.ker = Subgroup.zpowers t) {a : X} (hodd : Odd (orderOf a))
    (y : K) (hy : π y = a) : ∃ y' : K, π y' = a ∧ Odd (orderOf y') := by
  have ht2 : t ^ 2 = 1 := by rw [← ht]; exact pow_orderOf_eq_one t
  set m := orderOf a with hm
  have ham : a ^ m = 1 := pow_orderOf_eq_one a
  refine ⟨y ^ (m + 1), ?_, ?_⟩
  · rw [map_pow, hy, pow_succ, ham, one_mul]
  · have h1 : y ^ m ∈ Subgroup.zpowers t := by
      rw [← hker, MonoidHom.mem_ker, map_pow, hy]; exact ham
    have h2 : (y ^ m) ^ 2 = 1 := by
      rcases burnsideI22P5_mem_zpowers_two ht h1 with h | h
      · rw [h]; exact one_pow 2
      · rw [h]; exact ht2
    obtain ⟨k, hk⟩ := hodd.add_one
    have h3 : (y ^ (m + 1)) ^ m = 1 := by
      calc (y ^ (m + 1)) ^ m = (y ^ m) ^ (m + 1) := by rw [← pow_mul, ← pow_mul, mul_comm]
        _ = ((y ^ m) ^ 2) ^ k := by rw [hk, ← two_mul, pow_mul]
        _ = 1 := by rw [h2, one_pow]
    exact Odd.of_dvd_nat hodd (orderOf_dvd_of_pow_eq_one h3)

open CFSG.ASVolI.ChIJK in
theorem burnsideI22P5_unique_square_of_data {K X : Type} [Group K] [Finite K] [Group X]
    (π : K →* X) (hπ : Function.Surjective π) {t : K} (ht : orderOf t = 2)
    (hZt : Subgroup.center K = Subgroup.zpowers t) (hker : π.ker = Subgroup.zpowers t)
    (u : K) (S : Subgroup X) (hS2 : IsPGroup 2 S) (hSodd : ¬ 2 ∣ S.index)
    (hTu : ∀ y : K, π y ∈ S → y * u = u * y)
    (W : Subgroup X) (hW2 : IsPGroup 2 W)
    (hWn : ∀ c ∈ Subgroup.centralizer ({π u} : Set X), ∀ w ∈ W, c * w * c⁻¹ ∈ W)
    (hWodd : W ≤ Subgroup.closure
      {a : X | a ∈ Subgroup.centralizer ({π u} : Set X) ∧ Odd (orderOf a)})
    (w₀ : X) (hw₀ : w₀ ∈ W) (hw₀sq : w₀ ^ 2 = π u)
    (gs : Set X) (hgs : ∀ g ∈ gs, g ∈ Subgroup.centralizer ({π u} : Set X))
    (hU : ∀ x y : K, π x ∈ S → π y ∈ S → (∀ g ∈ gs, g * π x * g⁻¹ ∈ S) →
      (∀ g ∈ gs, g * π y * g⁻¹ ∈ S) → x ^ 2 = u → y ^ 2 = u * t → False) :
    UniqueSquareInCoset K u := by
  classical
  have htc : ∀ y : K, y * t = t * y := fun y =>
    Subgroup.mem_center_iff.1 (hZt ▸ Subgroup.mem_zpowers t) y
  have ht1 : t ≠ 1 := by
    intro h; rw [h, orderOf_one] at ht; exact absurd ht (by norm_num)
  have ht2 : t * t = 1 := by rw [← sq, ← ht]; exact pow_orderOf_eq_one t
  set C : Subgroup K := Subgroup.centralizer ({u} : Set K) with hC
  have hCeq : C = (Subgroup.centralizer ({π u} : Set X)).comap π :=
    burnsideI22P5_centralizer_eq_comap π hπ ht htc hker u S hSodd hTu
  have hmemC : ∀ y : K, y ∈ C ↔ π y ∈ Subgroup.centralizer ({π u} : Set X) := fun y => by
    rw [hCeq, Subgroup.mem_comap]
  set N : Subgroup K := twoResidual C with hN
  set Q : Subgroup K := pCoreOf 2 N with hQ
  have hNC : N ≤ C := burnsideI22P5_twoResidual_le C
  have hQN : Q ≤ N := burnsideI22P5_pCoreOf_le N
  set T : Subgroup K := S.comap π with hT
  have hTC : T ≤ C := fun y hy => by
    rw [hC, Subgroup.mem_centralizer_singleton_iff]; exact hTu y hy
  have hT2 : IsPGroup 2 T := burnsideI22P5_comap_isPGroup π ht hker S hS2
  have hTodd : ¬ 2 ∣ T.index := by
    rw [hT, Subgroup.index_comap_of_surjective S hπ]; exact hSodd
  have hQT : Q ≤ T := burnsideI22P5_Q_le C T hTC hT2 hTodd
  have hNconj : ∀ c ∈ C, ∀ n ∈ N, c * n * c⁻¹ ∈ N := burnsideI22P5_twoResidual_conj C
  have hQconj : ∀ c ∈ C, ∀ q ∈ Q, c * q * c⁻¹ ∈ Q :=
    burnsideI22P5_pCoreOf_conj_of_normal C N hNconj
  have hmapN : W ≤ N.map π := by
    refine hWodd.trans ((Subgroup.closure_le _).2 ?_)
    rintro a ⟨haC, hodd⟩
    obtain ⟨y, hy⟩ := hπ a
    obtain ⟨y', hy'a, hy'odd⟩ := burnsideI22P5_odd_lift π ht hker hodd y hy
    have hy'C : y' ∈ C := (hmemC y').2 (by rw [hy'a]; exact haC)
    exact ⟨y', burnsideI22P5_odd_mem_twoResidual C hy'C hy'odd, hy'a⟩
  obtain ⟨n, hnN, hnπ⟩ := hmapN hw₀
  set M : Subgroup K := N ⊓ W.comap π with hM
  have hMp : IsPGroup 2 M :=
    (burnsideI22P5_comap_isPGroup π ht hker W hW2).to_le inf_le_right
  have hMn : (M.subgroupOf N).Normal := ⟨fun x hx g => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    obtain ⟨hxN, hxW⟩ := hx
    have hx' : π (x : K) ∈ W := Subgroup.mem_comap.1 hxW
    refine ⟨N.mul_mem (N.mul_mem g.2 hxN) (N.inv_mem g.2), Subgroup.mem_comap.2 ?_⟩
    show π ((g : K) * (x : K) * (g : K)⁻¹) ∈ W
    rw [map_mul, map_mul, map_inv]
    exact hWn _ ((hmemC _).1 (hNC g.2)) _ hx'⟩
  have hMQ : M ≤ Q := burnsideI22P5_le_pCoreOf N M inf_le_left hMn hMp
  have hnQ : n ∈ Q := hMQ (Subgroup.mem_inf.2 ⟨hnN, Subgroup.mem_comap.2 (hnπ ▸ hw₀)⟩)
  have hn2 : n ^ 2 = u ∨ n ^ 2 = u * t := by
    have h1 : π u = π (n ^ 2) := by rw [map_pow, hnπ, hw₀sq]
    rcases burnsideI22P5_eq_or_mul π ht hker h1 with h | h
    · exact Or.inl h
    · exact Or.inr h
  have hQuniq : ∀ x ∈ Q, ∀ y ∈ Q, x ^ 2 = u → y ^ 2 = u * t → False := by
    intro x hx y hy hx2 hy2
    refine hU x y (hQT hx) (hQT hy) (fun g hg => ?_) (fun g hg => ?_) hx2 hy2
    · obtain ⟨ĝ, hĝ⟩ := hπ g
      have hĝC : ĝ ∈ C := (hmemC ĝ).2 (by rw [hĝ]; exact hgs g hg)
      have := hQT (hQconj ĝ hĝC x hx)
      simpa [hT, hĝ] using this
    · obtain ⟨ĝ, hĝ⟩ := hπ g
      have hĝC : ĝ ∈ C := (hmemC ĝ).2 (by rw [hĝ]; exact hgs g hg)
      have := hQT (hQconj ĝ hĝC y hy)
      simpa [hT, hĝ] using this
  have hzmem : ∀ v : K, (∃ z ∈ Subgroup.center K, v = u * z) → v = u ∨ v = u * t := by
    rintro v ⟨z, hz, rfl⟩
    rw [hZt] at hz
    rcases burnsideI22P5_mem_zpowers_two ht hz with h | h
    · left; rw [h, mul_one]
    · right; rw [h]
  refine ⟨n ^ 2, ⟨?_, n, hnQ, rfl⟩, ?_⟩
  · rcases hn2 with h | h
    · exact ⟨1, Subgroup.one_mem _, by rw [h, mul_one]⟩
    · exact ⟨t, hZt ▸ Subgroup.mem_zpowers t, h⟩
  · rintro v ⟨hv, x, hxQ, rfl⟩
    rcases hn2 with h | h
    · rcases hzmem _ hv with h' | h'
      · rw [h', h]
      · exact (hQuniq n hnQ x hxQ h h').elim
    · rcases hzmem _ hv with h' | h'
      · exact (hQuniq x hxQ n hnQ h' h).elim
      · rw [h', h]

open CFSG.ASVolI.ChIJK in
theorem burnsideI22P5_twoResidual_map_le {G : Type} [Group G] [Finite G] (φ : G ≃* G)
    (H : Subgroup G) : twoResidual (H.map φ.toMonoidHom) ≤ (twoResidual H).map φ.toMonoidHom := by
  set e : H ≃* H.map φ.toMonoidHom :=
    Subgroup.equivMapOfInjective H φ.toMonoidHom φ.injective with he
  obtain ⟨n, hn⟩ := burnsideI22P5_twoResidualIn_index H
  have hnorm : ((burnsideI22P5_twoResidualIn H).map e.toMonoidHom).Normal :=
    Subgroup.Normal.map (burnsideI22P5_twoResidualIn_normal H) e.toMonoidHom e.surjective
  have hindex : ((burnsideI22P5_twoResidualIn H).map e.toMonoidHom).index = 2 ^ n := by
    rw [Subgroup.index_map_of_bijective e.bijective, hn]
  have key := burnsideI22P5_twoResidual_le_of_index (H.map φ.toMonoidHom) _ hnorm n hindex
  refine key.trans (le_of_eq ?_)
  rw [burnsideI22P5_twoResidual_eq, Subgroup.map_map, Subgroup.map_map]
  congr 1

open CFSG.ASVolI.ChIJK in
theorem burnsideI22P5_twoResidual_map {G : Type} [Group G] [Finite G] (φ : G ≃* G)
    (H : Subgroup G) : twoResidual (H.map φ.toMonoidHom) = (twoResidual H).map φ.toMonoidHom := by
  refine le_antisymm (burnsideI22P5_twoResidual_map_le φ H) ?_
  have h := burnsideI22P5_twoResidual_map_le φ.symm (H.map φ.toMonoidHom)
  have hH : (H.map φ.toMonoidHom).map φ.symm.toMonoidHom = H := by
    rw [Subgroup.map_map]
    ext x; simp
  rw [hH] at h
  have h2 := Subgroup.map_mono (f := φ.toMonoidHom) h
  rw [Subgroup.map_map] at h2
  have : (φ.toMonoidHom.comp φ.symm.toMonoidHom) = MonoidHom.id G := by
    ext x; simp
  rwa [this, Subgroup.map_id] at h2

theorem burnsideI22P5_pCoreOf_map {G : Type} [Group G] (φ : G ≃* G) (H : Subgroup G) :
    pCoreOf 2 (H.map φ.toMonoidHom) = (pCoreOf 2 H).map φ.toMonoidHom := by
  set e : H ≃* H.map φ.toMonoidHom :=
    Subgroup.equivMapOfInjective H φ.toMonoidHom φ.injective with he
  have h1 := CFSG.pCore_map_iso 2 e
  unfold pCoreOf
  rw [← h1, Subgroup.map_map, Subgroup.map_map]
  congr 1

open CFSG.ASVolI.ChIJK in
theorem burnsideI22P5_unique_square_conj {K : Type} [Group K] [Finite K] (a u : K)
    (h : UniqueSquareInCoset K u) : UniqueSquareInCoset K (a * u * a⁻¹) := by
  set φ : K ≃* K := MulAut.conj a with hφ
  have hφapply : ∀ x, φ x = a * x * a⁻¹ := fun x => MulAut.conj_apply a x
  have hcent : Subgroup.centralizer ({a * u * a⁻¹} : Set K) =
      (Subgroup.centralizer ({u} : Set K)).map φ.toMonoidHom := by
    ext y
    rw [Subgroup.mem_map_equiv, Subgroup.mem_centralizer_singleton_iff,
      Subgroup.mem_centralizer_singleton_iff]
    have : φ.symm y = a⁻¹ * y * a := by
      rw [MulEquiv.symm_apply_eq, hφapply]; group
    rw [this]
    constructor
    · intro hy
      calc (a⁻¹ * y * a) * u = a⁻¹ * (y * (a * u * a⁻¹)) * a := by group
        _ = a⁻¹ * ((a * u * a⁻¹) * y) * a := by rw [hy]
        _ = u * (a⁻¹ * y * a) := by group
    · intro hy
      calc y * (a * u * a⁻¹) = a * ((a⁻¹ * y * a) * u) * a⁻¹ := by group
        _ = a * (u * (a⁻¹ * y * a)) * a⁻¹ := by rw [hy]
        _ = (a * u * a⁻¹) * y := by group
  have hQ : pCoreOf 2 (twoResidual (Subgroup.centralizer ({a * u * a⁻¹} : Set K))) =
      (pCoreOf 2 (twoResidual (Subgroup.centralizer ({u} : Set K)))).map φ.toMonoidHom := by
    rw [hcent, burnsideI22P5_twoResidual_map, burnsideI22P5_pCoreOf_map]
  have hcenter : ∀ z ∈ Subgroup.center K, φ z = z := fun z hz => by
    rw [hφapply, Subgroup.mem_center_iff.1 hz a, mul_inv_cancel_right]
  obtain ⟨v₀, ⟨⟨z₀, hz₀, hv₀⟩, x₀, hx₀, hx₀v⟩, huniq⟩ := h
  refine ⟨φ v₀, ⟨⟨z₀, hz₀, ?_⟩, φ x₀, ?_, ?_⟩, ?_⟩
  · rw [hv₀, map_mul, hcenter z₀ hz₀, hφapply u]
  · rw [hQ]; exact ⟨x₀, hx₀, rfl⟩
  · rw [← map_pow, hx₀v]
  · rintro v' ⟨⟨z, hz, hv'⟩, x, hx, hxv⟩
    rw [hQ] at hx
    obtain ⟨x₁, hx₁, rfl⟩ := hx
    have h1 : v' = φ (u * z) := by
      rw [map_mul, hcenter z hz, hφapply u]; exact hv'
    have hxv' : (φ x₁) ^ 2 = v' := hxv
    have := huniq (u * z) ⟨⟨z, hz, rfl⟩, x₁, hx₁, φ.injective (by
      rw [map_pow, hxv', h1])⟩
    rw [h1, this]

open CFSG.Blueprint CFSG.ComponentClassification.M12Cover
  CFSG.ComponentClassification.M12Cover.InternalSylow CFSG.ComponentClassification.CentralCover in
@[expose] def burnsideI22P5_M12c_Widx : List ℕ :=
  [0, 1, 2, 3, 8, 9, 12, 13, 20, 21, 22, 23, 24, 25, 26, 27, 32, 33, 36, 37, 42, 43, 46, 47, 50,
    51, 54, 55, 60, 61, 62, 63]

open CFSG.Blueprint CFSG.ComponentClassification.M12Cover
  CFSG.ComponentClassification.M12Cover.InternalSylow CFSG.ComponentClassification.CentralCover in
theorem burnsideI22P5_M12c_Widx_mul :
    ∀ i j : Fin 64, (i : ℕ) ∈ burnsideI22P5_M12c_Widx → (j : ℕ) ∈ burnsideI22P5_M12c_Widx →
      ((mTab i j : Fin 64) : ℕ) ∈ burnsideI22P5_M12c_Widx := by
  decide +kernel

open CFSG.Blueprint CFSG.ComponentClassification.M12Cover
  CFSG.ComponentClassification.M12Cover.InternalSylow CFSG.ComponentClassification.CentralCover in
theorem burnsideI22P5_M12c_Widx_inv :
    ∀ i : Fin 64, (i : ℕ) ∈ burnsideI22P5_M12c_Widx → invIdx i ∈ burnsideI22P5_M12c_Widx := by
  decide +kernel

open CFSG.Blueprint CFSG.ComponentClassification.M12Cover
  CFSG.ComponentClassification.M12Cover.InternalSylow CFSG.ComponentClassification.CentralCover in
@[expose] def burnsideI22P5_M12c_W : Subgroup NativeSporadic.M12 where
  carrier := {x | ∃ k : Fin 64, (k : ℕ) ∈ burnsideI22P5_M12c_Widx ∧
    ((d k : InternalSylow.S) : NativeSporadic.M12) = x}
  mul_mem' := by
    rintro _ _ ⟨i, hi, rfl⟩ ⟨j, hj, rfl⟩
    refine ⟨mTab i j, burnsideI22P5_M12c_Widx_mul i j hi hj, ?_⟩
    rw [d_mul]; rfl
  one_mem' := ⟨0, by decide, by rw [d_zero]; rfl⟩
  inv_mem' := by
    rintro _ ⟨i, hi, rfl⟩
    refine ⟨⟨invIdx i, packEntry_lt _ 6 _⟩, burnsideI22P5_M12c_Widx_inv i hi, ?_⟩
    rw [← Subgroup.coe_inv, ← d_inv]

open CFSG.Blueprint CFSG.ComponentClassification.M12Cover
  CFSG.ComponentClassification.M12Cover.InternalSylow CFSG.ComponentClassification.CentralCover in
theorem burnsideI22P5_M12c_mem_W {k : Fin 64} (hk : (k : ℕ) ∈ burnsideI22P5_M12c_Widx) :
    ((d k : InternalSylow.S) : NativeSporadic.M12) ∈ burnsideI22P5_M12c_W := ⟨k, hk, rfl⟩

open CFSG.Blueprint CFSG.ComponentClassification.M12Cover
  CFSG.ComponentClassification.M12Cover.InternalSylow CFSG.ComponentClassification.CentralCover in
theorem burnsideI22P5_M12c_W_le_S : burnsideI22P5_M12c_W ≤ InternalSylow.S := by
  rintro _ ⟨k, -, rfl⟩
  exact (d k).2

open CFSG.Blueprint CFSG.ComponentClassification.M12Cover
  CFSG.ComponentClassification.M12Cover.InternalSylow CFSG.ComponentClassification.CentralCover in
theorem burnsideI22P5_M12c_S_conj_idx :
    ∀ i k : Fin 64, (k : ℕ) ∈ burnsideI22P5_M12c_Widx →
      ((mTab (mTab i k) ⟨invIdx i, packEntry_lt _ 6 _⟩ : Fin 64) : ℕ) ∈ burnsideI22P5_M12c_Widx := by
  decide +kernel

open CFSG.Blueprint CFSG.ComponentClassification.M12Cover
  CFSG.ComponentClassification.M12Cover.InternalSylow CFSG.ComponentClassification.CentralCover in
theorem burnsideI22P5_M12c_S_conj {s w : NativeSporadic.M12} (hs : s ∈ InternalSylow.S)
    (hw : w ∈ burnsideI22P5_M12c_W) : s * w * s⁻¹ ∈ burnsideI22P5_M12c_W := by
  obtain ⟨i, hi⟩ := d_surjective ⟨s, hs⟩
  obtain ⟨k, hk, rfl⟩ := hw
  have hi' : ((d i : InternalSylow.S) : NativeSporadic.M12) = s := congrArg Subtype.val hi
  rw [← hi']
  refine ⟨mTab (mTab i k) ⟨invIdx i, packEntry_lt _ 6 _⟩,
    burnsideI22P5_M12c_S_conj_idx i k hk, ?_⟩
  rw [d_mul, d_mul, ← d_inv]
  rfl

open CFSG.Blueprint CFSG.ComponentClassification.M12Cover
  CFSG.ComponentClassification.M12Cover.InternalSylow CFSG.ComponentClassification.CentralCover in
@[expose] def burnsideI22P5_M12c_gWord : List ℕ :=
  [2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2]

open CFSG.Blueprint CFSG.ComponentClassification.M12Cover
  CFSG.ComponentClassification.M12Cover.InternalSylow CFSG.ComponentClassification.CentralCover in
@[expose] def burnsideI22P5_M12c_g : NativeSporadic.M12 :=
  ⟨evalWord burnsideI22P5_M12c_gWord, evalWord_mem _⟩

open CFSG.Blueprint CFSG.ComponentClassification.M12Cover
  CFSG.ComponentClassification.M12Cover.InternalSylow CFSG.ComponentClassification.CentralCover in
@[expose] def burnsideI22P5_M12c_gCode : List ℕ := [9, 1, 7, 2, 10, 5, 6, 3, 0, 8, 11, 4]

open CFSG.Blueprint CFSG.ComponentClassification.M12Cover
  CFSG.ComponentClassification.M12Cover.InternalSylow CFSG.ComponentClassification.CentralCover in
@[expose] def burnsideI22P5_M12c_giCode : List ℕ := [8, 1, 3, 7, 11, 5, 6, 2, 9, 0, 4, 10]

open CFSG.Blueprint CFSG.ComponentClassification.M12Cover
  CFSG.ComponentClassification.M12Cover.InternalSylow CFSG.ComponentClassification.CentralCover in
theorem burnsideI22P5_M12c_isFCode_g :
    IsFCode (SylowTable.nth 0 burnsideI22P5_M12c_gCode)
      (burnsideI22P5_M12c_g : Equiv.Perm (Fin 12)) := by
  refine (isFCode_evalWord burnsideI22P5_M12c_gWord).congr fun p hp => ?_
  revert p
  decide +kernel

open CFSG.Blueprint CFSG.ComponentClassification.M12Cover
  CFSG.ComponentClassification.M12Cover.InternalSylow CFSG.ComponentClassification.CentralCover in
theorem burnsideI22P5_M12c_isFCode_gi :
    IsFCode (SylowTable.nth 0 burnsideI22P5_M12c_giCode)
      ((burnsideI22P5_M12c_g : Equiv.Perm (Fin 12))⁻¹) :=
  burnsideI22P5_M12c_isFCode_g.inv (by decide +kernel) (by decide +kernel)

open CFSG.Blueprint CFSG.ComponentClassification.M12Cover
  CFSG.ComponentClassification.M12Cover.InternalSylow CFSG.ComponentClassification.CentralCover in
@[expose] def burnsideI22P5_M12c_gconj (k : ℕ) : ℕ :=
  SylowTable.nth 0 [0, 24, 26, 2, 0, 0, 0, 0, 55, 47, 0, 0, 43, 51, 0, 0, 0, 0, 0, 0, 37, 13, 9, 33, 25, 1, 3, 27, 0, 0, 0, 0, 46, 54, 0, 0, 50, 42, 0, 0, 0, 0, 20, 60, 0, 0, 62, 22, 0, 0, 61, 21, 0, 0, 23, 63, 0, 0, 0, 0, 12, 36, 32, 8] k

open CFSG.Blueprint CFSG.ComponentClassification.M12Cover
  CFSG.ComponentClassification.M12Cover.InternalSylow CFSG.ComponentClassification.CentralCover in
@[expose] def burnsideI22P5_M12c_giconj (k : ℕ) : ℕ :=
  SylowTable.nth 0 [0, 25, 3, 26, 0, 0, 0, 0, 63, 22, 0, 0, 60, 21, 0, 0, 0, 0, 0, 0, 42, 51, 47, 54, 1, 24, 2, 27, 0, 0, 0, 0, 62, 23, 0, 0, 61, 20, 0, 0, 0, 0, 37, 12, 0, 0, 32, 9, 0, 0, 36, 13, 0, 0, 33, 8, 0, 0, 0, 0, 43, 50, 46, 55] k

open CFSG.Blueprint CFSG.ComponentClassification.M12Cover
  CFSG.ComponentClassification.M12Cover.InternalSylow CFSG.ComponentClassification.CentralCover in
theorem burnsideI22P5_M12c_gconj_check :
    ∀ k : Fin 64, (k : ℕ) ∈ burnsideI22P5_M12c_Widx →
      burnsideI22P5_M12c_gconj k ∈ burnsideI22P5_M12c_Widx ∧ burnsideI22P5_M12c_gconj k < 64 ∧
      ∀ p < 12, dCode (burnsideI22P5_M12c_gconj k) p =
        SylowTable.nth 0 burnsideI22P5_M12c_gCode
          (dCode k (SylowTable.nth 0 burnsideI22P5_M12c_giCode p)) := by
  decide +kernel

open CFSG.Blueprint CFSG.ComponentClassification.M12Cover
  CFSG.ComponentClassification.M12Cover.InternalSylow CFSG.ComponentClassification.CentralCover in
theorem burnsideI22P5_M12c_giconj_check :
    ∀ k : Fin 64, (k : ℕ) ∈ burnsideI22P5_M12c_Widx →
      burnsideI22P5_M12c_giconj k ∈ burnsideI22P5_M12c_Widx ∧ burnsideI22P5_M12c_giconj k < 64 ∧
      ∀ p < 12, dCode (burnsideI22P5_M12c_giconj k) p =
        SylowTable.nth 0 burnsideI22P5_M12c_giCode
          (dCode k (SylowTable.nth 0 burnsideI22P5_M12c_gCode p)) := by
  decide +kernel

open CFSG.Blueprint CFSG.ComponentClassification.M12Cover
  CFSG.ComponentClassification.M12Cover.InternalSylow CFSG.ComponentClassification.CentralCover in
theorem burnsideI22P5_card_centralizer_conj {G : Type} [Group G] (x a : G) :
    Nat.card (Subgroup.centralizer ({x * a * x⁻¹} : Set G)) =
      Nat.card (Subgroup.centralizer ({a} : Set G)) := by
  have hcent : Subgroup.centralizer ({x * a * x⁻¹} : Set G) =
      (Subgroup.centralizer ({a} : Set G)).map (MulAut.conj x).toMonoidHom := by
    ext y
    rw [Subgroup.mem_map_equiv, Subgroup.mem_centralizer_singleton_iff,
      Subgroup.mem_centralizer_singleton_iff]
    have : (MulAut.conj x).symm y = x⁻¹ * y * x := by
      rw [MulEquiv.symm_apply_eq, MulAut.conj_apply]; group
    rw [this]
    constructor
    · intro hy
      calc (x⁻¹ * y * x) * a = x⁻¹ * (y * (x * a * x⁻¹)) * x := by group
        _ = x⁻¹ * ((x * a * x⁻¹) * y) * x := by rw [hy]
        _ = a * (x⁻¹ * y * x) := by group
    · intro hy
      calc y * (x * a * x⁻¹) = x * ((x⁻¹ * y * x) * a) * x⁻¹ := by group
        _ = x * (a * (x⁻¹ * y * x)) * x⁻¹ := by rw [hy]
        _ = (x * a * x⁻¹) * y := by group
  rw [hcent]
  exact Subgroup.card_map_of_injective (MulAut.conj x).injective

open CFSG.Blueprint CFSG.ComponentClassification.M12Cover
  CFSG.ComponentClassification.M12Cover.InternalSylow CFSG.ComponentClassification.CentralCover in

open CFSG.Blueprint CFSG.ComponentClassification.M12Cover
  CFSG.ComponentClassification.M12Cover.InternalSylow CFSG.ComponentClassification.CentralCover in
theorem burnsideI22P5_M12c_fixed_A1 :
    fixedCount elemA1 = 0 := by
  unfold fixedCount
  have h : ∀ i, (elemA1 : Equiv.Perm (Fin 12)) i =
      ![1, 0, 3, 2, 11, 6, 5, 8, 7, 10, 9, 4] i := permA1_apply
  simp only [h]
  decide +kernel

open CFSG.Blueprint CFSG.ComponentClassification.M12Cover
  CFSG.ComponentClassification.M12Cover.InternalSylow CFSG.ComponentClassification.CentralCover in
theorem burnsideI22P5_M12c_card_centralizer
    (x : NativeSporadic.M12) (hx : orderOf x = 2)
    (h4 : fixedCount x = 4) : Nat.card (Subgroup.centralizer ({x} : Set NativeSporadic.M12)) = 192 := by
  obtain ⟨c, h | h⟩ := m12_involution_conj_a0_a1 x hx
  · rw [h, burnsideI22P5_card_centralizer_conj]
    exact card_centralizer_elemA0
  · exfalso
    rw [h, fixedCount_conj, burnsideI22P5_M12c_fixed_A1] at h4
    norm_num at h4

open CFSG.Blueprint CFSG.ComponentClassification.M12Cover
  CFSG.ComponentClassification.M12Cover.InternalSylow CFSG.ComponentClassification.CentralCover in
theorem burnsideI22P5_M12c_g_comm :
    burnsideI22P5_M12c_g * ((d 27 : InternalSylow.S) : NativeSporadic.M12) =
      ((d 27 : InternalSylow.S) : NativeSporadic.M12) * burnsideI22P5_M12c_g := by
  apply Subtype.ext
  have h1 := burnsideI22P5_M12c_isFCode_g.mul (isFCode_d 27)
  have h2 := (isFCode_d 27).mul burnsideI22P5_M12c_isFCode_g
  rw [Subgroup.coe_mul, Subgroup.coe_mul]
  refine h1.perm_eq (h2.congr fun p hp => ?_)
  revert p
  decide +kernel

open CFSG.Blueprint CFSG.ComponentClassification.M12Cover
  CFSG.ComponentClassification.M12Cover.InternalSylow CFSG.ComponentClassification.CentralCover in
theorem burnsideI22P5_M12c_g_cube :
    burnsideI22P5_M12c_g * burnsideI22P5_M12c_g * burnsideI22P5_M12c_g = 1 := by
  apply Subtype.ext
  have h1 := burnsideI22P5_M12c_isFCode_g.mul
    (burnsideI22P5_M12c_isFCode_g.mul burnsideI22P5_M12c_isFCode_g)
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_one, ← mul_assoc] at *
  refine h1.perm_eq (IsFCode.one.congr fun p hp => ?_)
  revert p
  decide +kernel

open CFSG.Blueprint CFSG.ComponentClassification.M12Cover
  CFSG.ComponentClassification.M12Cover.InternalSylow CFSG.ComponentClassification.CentralCover in
theorem burnsideI22P5_M12c_g_ne_one : burnsideI22P5_M12c_g ≠ 1 := by
  intro h
  have h0 := burnsideI22P5_M12c_isFCode_g ⟨0, by norm_num⟩
  rw [h] at h0
  simp [burnsideI22P5_M12c_gCode, SylowTable.nth] at h0

open CFSG.Blueprint CFSG.ComponentClassification.M12Cover
  CFSG.ComponentClassification.M12Cover.InternalSylow CFSG.ComponentClassification.CentralCover in
theorem burnsideI22P5_M12c_g_order : orderOf burnsideI22P5_M12c_g = 3 :=
  orderOf_eq_prime (by rw [pow_succ, pow_two]; exact burnsideI22P5_M12c_g_cube)
    burnsideI22P5_M12c_g_ne_one

open CFSG.Blueprint CFSG.ComponentClassification.M12Cover
  CFSG.ComponentClassification.M12Cover.InternalSylow CFSG.ComponentClassification.CentralCover in
theorem burnsideI22P5_M12c_g_conj {w : NativeSporadic.M12} (hw : w ∈ burnsideI22P5_M12c_W) :
    burnsideI22P5_M12c_g * w * burnsideI22P5_M12c_g⁻¹ ∈ burnsideI22P5_M12c_W := by
  obtain ⟨k, hk, rfl⟩ := hw
  obtain ⟨hm, hlt, hc⟩ := burnsideI22P5_M12c_gconj_check k hk
  refine ⟨⟨burnsideI22P5_M12c_gconj k, hlt⟩, hm, ?_⟩
  apply Subtype.ext
  have h := (burnsideI22P5_M12c_isFCode_g.mul (isFCode_d k)).mul burnsideI22P5_M12c_isFCode_gi
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
  exact (isFCode_d _).perm_eq (h.congr fun p hp => hc p hp)

open CFSG.Blueprint CFSG.ComponentClassification.M12Cover
  CFSG.ComponentClassification.M12Cover.InternalSylow CFSG.ComponentClassification.CentralCover in
theorem burnsideI22P5_M12c_gi_conj {w : NativeSporadic.M12} (hw : w ∈ burnsideI22P5_M12c_W) :
    burnsideI22P5_M12c_g⁻¹ * w * burnsideI22P5_M12c_g⁻¹⁻¹ ∈ burnsideI22P5_M12c_W := by
  obtain ⟨k, hk, rfl⟩ := hw
  obtain ⟨hm, hlt, hc⟩ := burnsideI22P5_M12c_giconj_check k hk
  refine ⟨⟨burnsideI22P5_M12c_giconj k, hlt⟩, hm, ?_⟩
  apply Subtype.ext
  have h := (burnsideI22P5_M12c_isFCode_gi.mul (isFCode_d k)).mul burnsideI22P5_M12c_isFCode_g
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]
  exact (isFCode_d _).perm_eq (h.congr fun p hp => hc p hp)

open CFSG.Blueprint CFSG.ComponentClassification.M12Cover
  CFSG.ComponentClassification.M12Cover.InternalSylow CFSG.ComponentClassification.CentralCover in
theorem burnsideI22P5_M12c_closure_le_normalizer :
    Subgroup.closure ((InternalSylow.S : Set NativeSporadic.M12) ∪ {burnsideI22P5_M12c_g}) ≤
      Subgroup.normalizer (burnsideI22P5_M12c_W : Set NativeSporadic.M12) := by
  rw [Subgroup.closure_le]
  rintro x (hx | hx)
  · rw [SetLike.mem_coe, Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh; exact burnsideI22P5_M12c_S_conj hx hh
    · intro hh
      have := burnsideI22P5_M12c_S_conj (InternalSylow.S.inv_mem hx) hh
      simpa [mul_assoc] using this
  · rw [Set.mem_singleton_iff] at hx
    subst hx
    rw [SetLike.mem_coe, Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh; exact burnsideI22P5_M12c_g_conj hh
    · intro hh
      have := burnsideI22P5_M12c_gi_conj hh
      simpa [mul_assoc] using this

open CFSG.Blueprint CFSG.ComponentClassification.M12Cover
  CFSG.ComponentClassification.M12Cover.InternalSylow CFSG.ComponentClassification.CentralCover in
theorem burnsideI22P5_M12c_d27_order : orderOf ((d 27 : InternalSylow.S) : NativeSporadic.M12) = 2 := by
  rw [Subgroup.orderOf_coe]; exact orderOf_d27

open CFSG.Blueprint CFSG.ComponentClassification.M12Cover
  CFSG.ComponentClassification.M12Cover.InternalSylow CFSG.ComponentClassification.CentralCover in
theorem burnsideI22P5_M12c_d27_fixed :
    fixedCount ((d 27 : InternalSylow.S) : NativeSporadic.M12) = 4 := card_fixed_d27

open CFSG.Blueprint CFSG.ComponentClassification.M12Cover
  CFSG.ComponentClassification.M12Cover.InternalSylow CFSG.ComponentClassification.CentralCover in
theorem burnsideI22P5_M12c_C_eq :
    Subgroup.centralizer ({((d 27 : InternalSylow.S) : NativeSporadic.M12)} :
        Set NativeSporadic.M12) =
      Subgroup.closure ((InternalSylow.S : Set NativeSporadic.M12) ∪ {burnsideI22P5_M12c_g}) := by
  set c0 : NativeSporadic.M12 := ((d 27 : InternalSylow.S) : NativeSporadic.M12) with hc0
  set C := Subgroup.centralizer ({c0} : Set NativeSporadic.M12) with hC
  set D := Subgroup.closure ((InternalSylow.S : Set NativeSporadic.M12) ∪
    {burnsideI22P5_M12c_g}) with hD
  have hSC : InternalSylow.S ≤ C := fun s hs => by
    rw [hC, Subgroup.mem_centralizer_singleton_iff]
    have hcen : d 27 ∈ Subgroup.center InternalSylow.S := (mem_center_iff _).2 (Or.inr rfl)
    have := Subgroup.mem_center_iff.1 hcen ⟨s, hs⟩
    exact congrArg Subtype.val this
  have hgC : burnsideI22P5_M12c_g ∈ C := by
    rw [hC, Subgroup.mem_centralizer_singleton_iff]
    exact burnsideI22P5_M12c_g_comm
  have hDC : D ≤ C := (Subgroup.closure_le C).2
    (Set.union_subset (fun s hs => hSC hs) (Set.singleton_subset_iff.2 hgC))
  have hcardC : Nat.card C = 192 :=
    burnsideI22P5_M12c_card_centralizer c0 burnsideI22P5_M12c_d27_order
      burnsideI22P5_M12c_d27_fixed
  have hSD : InternalSylow.S ≤ D := fun s hs => Subgroup.subset_closure (Or.inl hs)
  have hgD : burnsideI22P5_M12c_g ∈ D := Subgroup.subset_closure (Or.inr rfl)
  have h64 : 64 ∣ Nat.card D := by
    have := Subgroup.card_dvd_of_le hSD
    rwa [InternalSylow.card_S] at this
  have h3 : 3 ∣ Nat.card D := by
    have := Subgroup.orderOf_dvd_natCard D hgD
    rwa [burnsideI22P5_M12c_g_order] at this
  have h192 : 192 ∣ Nat.card D :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 64 3) h64 h3
  have hle : Nat.card D ≤ 192 := hcardC ▸ Subgroup.card_le_of_le hDC
  have hge : 192 ≤ Nat.card D := Nat.le_of_dvd Nat.card_pos h192
  exact (Subgroup.eq_of_le_of_card_ge hDC (by omega)).symm

open CFSG.Blueprint CFSG.ComponentClassification.M12Cover
  CFSG.ComponentClassification.M12Cover.InternalSylow CFSG.ComponentClassification.CentralCover in
theorem burnsideI22P5_M12c_Wn :
    ∀ c ∈ Subgroup.centralizer ({((d 27 : InternalSylow.S) : NativeSporadic.M12)} :
        Set NativeSporadic.M12), ∀ w ∈ burnsideI22P5_M12c_W,
      c * w * c⁻¹ ∈ burnsideI22P5_M12c_W := by
  intro c hc w hw
  rw [burnsideI22P5_M12c_C_eq] at hc
  have := Subgroup.mem_normalizer_iff.1 (burnsideI22P5_M12c_closure_le_normalizer hc) w
  exact this.1 hw

open CFSG.Blueprint CFSG.ComponentClassification.M12Cover
  CFSG.ComponentClassification.M12Cover.InternalSylow CFSG.ComponentClassification.CentralCover in
@[expose] def burnsideI22P5_M12c_commPairs : List (ℕ × ℕ) := [(3, 1), (42, 8), (46, 13), (13, 21)]

open CFSG.Blueprint CFSG.ComponentClassification.M12Cover
  CFSG.ComponentClassification.M12Cover.InternalSylow CFSG.ComponentClassification.CentralCover in
theorem burnsideI22P5_M12c_commPairs_check :
    ∀ pr ∈ burnsideI22P5_M12c_commPairs, pr.1 < 64 ∧ pr.1 ∈ burnsideI22P5_M12c_Widx ∧
      invIdx pr.1 ∈ burnsideI22P5_M12c_Widx ∧
      mIdx pr.1 (burnsideI22P5_M12c_gconj (invIdx pr.1)) = pr.2 ∧ pr.2 < 64 := by
  decide +kernel

open CFSG.Blueprint CFSG.ComponentClassification.M12Cover
  CFSG.ComponentClassification.M12Cover.InternalSylow CFSG.ComponentClassification.CentralCover in
@[expose] def burnsideI22P5_M12c_genF : Fin 4 → Fin 64 := ![1, 8, 13, 21]

open CFSG.Blueprint CFSG.ComponentClassification.M12Cover
  CFSG.ComponentClassification.M12Cover.InternalSylow CFSG.ComponentClassification.CentralCover in
@[expose] def burnsideI22P5_M12c_evalG (w : List (Fin 4)) : Fin 64 :=
  w.foldr (fun i acc => mTab (burnsideI22P5_M12c_genF i) acc) 0

open CFSG.Blueprint CFSG.ComponentClassification.M12Cover
  CFSG.ComponentClassification.M12Cover.InternalSylow CFSG.ComponentClassification.CentralCover in
theorem burnsideI22P5_M12c_d_evalG (w : List (Fin 4)) :
    d (burnsideI22P5_M12c_evalG w) =
      (w.map fun i => d (burnsideI22P5_M12c_genF i)).prod := by
  induction w with
  | nil => exact d_zero
  | cons i w ih =>
    simp only [burnsideI22P5_M12c_evalG, List.foldr_cons, List.map_cons, List.prod_cons] at ih ⊢
    rw [d_mul, ih]

open CFSG.Blueprint CFSG.ComponentClassification.M12Cover
  CFSG.ComponentClassification.M12Cover.InternalSylow CFSG.ComponentClassification.CentralCover in
@[expose] def burnsideI22P5_M12c_wordTable : List (List (Fin 4)) :=
  [[],
    [0],
    [1, 2, 0],
    [1, 2],
    [],
    [],
    [],
    [],
    [1],
    [1, 0],
    [],
    [],
    [2, 0],
    [2],
    [],
    [],
    [],
    [],
    [],
    [],
    [3, 0],
    [3],
    [2, 3, 1],
    [2, 3, 1, 0],
    [2, 1],
    [2, 1, 0],
    [2, 2, 0],
    [2, 2],
    [],
    [],
    [],
    [],
    [1, 2, 1],
    [1, 2, 1, 0],
    [],
    [],
    [2, 2, 1, 0],
    [2, 2, 1],
    [],
    [],
    [],
    [],
    [3, 1, 0],
    [3, 1],
    [],
    [],
    [3, 2],
    [3, 2, 0],
    [],
    [],
    [2, 3, 0],
    [2, 3],
    [],
    [],
    [0, 3, 1, 0],
    [0, 3, 1],
    [],
    [],
    [],
    [],
    [3, 2, 1, 0],
    [3, 2, 1],
    [0, 3, 0],
    [0, 3]]

open CFSG.Blueprint CFSG.ComponentClassification.M12Cover
  CFSG.ComponentClassification.M12Cover.InternalSylow CFSG.ComponentClassification.CentralCover in
theorem burnsideI22P5_M12c_wordTable_check :
    ∀ j : Fin 64, (j : ℕ) ∈ burnsideI22P5_M12c_Widx →
      burnsideI22P5_M12c_evalG (burnsideI22P5_M12c_wordTable.getD j []) = j := by
  decide +kernel

open CFSG.Blueprint CFSG.ComponentClassification.M12Cover
  CFSG.ComponentClassification.M12Cover.InternalSylow CFSG.ComponentClassification.CentralCover in
theorem burnsideI22P5_M12c_g_conj_eq (k : Fin 64) (hk : (k : ℕ) ∈ burnsideI22P5_M12c_Widx) :
    burnsideI22P5_M12c_g * ((d k : InternalSylow.S) : NativeSporadic.M12) *
        burnsideI22P5_M12c_g⁻¹ =
      ((d ⟨burnsideI22P5_M12c_gconj k, (burnsideI22P5_M12c_gconj_check k hk).2.1⟩ :
        InternalSylow.S) : NativeSporadic.M12) := by
  obtain ⟨hm, hlt, hc⟩ := burnsideI22P5_M12c_gconj_check k hk
  apply Subtype.ext
  have h := (burnsideI22P5_M12c_isFCode_g.mul (isFCode_d k)).mul burnsideI22P5_M12c_isFCode_gi
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
  exact ((isFCode_d _).perm_eq (h.congr fun p hp => hc p hp)).symm

open CFSG.Blueprint CFSG.ComponentClassification.M12Cover
  CFSG.ComponentClassification.M12Cover.InternalSylow CFSG.ComponentClassification.CentralCover in
theorem burnsideI22P5_M12c_comm_eq {k κ : ℕ} (h : (k, κ) ∈ burnsideI22P5_M12c_commPairs) :
    ∃ (hk : k < 64) (hκ : κ < 64),
      ((d ⟨κ, hκ⟩ : InternalSylow.S) : NativeSporadic.M12) =
        ((d ⟨k, hk⟩ : InternalSylow.S) : NativeSporadic.M12) * burnsideI22P5_M12c_g *
          ((d ⟨k, hk⟩ : InternalSylow.S) : NativeSporadic.M12)⁻¹ * burnsideI22P5_M12c_g⁻¹ := by
  obtain ⟨hk, hkW, hiW, hm, hκ⟩ := burnsideI22P5_M12c_commPairs_check (k, κ) h
  refine ⟨hk, hκ, ?_⟩
  have hg := burnsideI22P5_M12c_g_conj_eq ⟨invIdx k, packEntry_lt _ 6 _⟩ hiW
  have hinv : ((d ⟨invIdx k, packEntry_lt _ 6 _⟩ : InternalSylow.S) : NativeSporadic.M12) =
      ((d ⟨k, hk⟩ : InternalSylow.S) : NativeSporadic.M12)⁻¹ := by
    have := congrArg (fun x : InternalSylow.S => (x : NativeSporadic.M12)) (d_inv ⟨k, hk⟩)
    exact this.symm
  rw [hinv] at hg
  have h2 : ((d ⟨κ, hκ⟩ : InternalSylow.S) : NativeSporadic.M12) =
      ((d (mTab ⟨k, hk⟩ ⟨burnsideI22P5_M12c_gconj (invIdx k),
        (burnsideI22P5_M12c_gconj_check ⟨invIdx k, packEntry_lt _ 6 _⟩ hiW).2.1⟩) :
        InternalSylow.S) : NativeSporadic.M12) := by
    congr 2
    exact Fin.ext hm.symm
  rw [h2, d_mul, Subgroup.coe_mul, ← hg]
  group

open CFSG.Blueprint CFSG.ComponentClassification.M12Cover
  CFSG.ComponentClassification.M12Cover.InternalSylow CFSG.ComponentClassification.CentralCover in
theorem burnsideI22P5_M12c_S_le_C :
    InternalSylow.S ≤ Subgroup.centralizer ({((d 27 : InternalSylow.S) : NativeSporadic.M12)} :
      Set NativeSporadic.M12) := fun s hs => by
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hcen : d 27 ∈ Subgroup.center InternalSylow.S := (mem_center_iff _).2 (Or.inr rfl)
  have := Subgroup.mem_center_iff.1 hcen ⟨s, hs⟩
  exact congrArg Subtype.val this

open CFSG.Blueprint CFSG.ComponentClassification.M12Cover
  CFSG.ComponentClassification.M12Cover.InternalSylow CFSG.ComponentClassification.CentralCover in
theorem burnsideI22P5_M12c_g_mem_C :
    burnsideI22P5_M12c_g ∈ Subgroup.centralizer
      ({((d 27 : InternalSylow.S) : NativeSporadic.M12)} : Set NativeSporadic.M12) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact burnsideI22P5_M12c_g_comm

open CFSG.Blueprint CFSG.ComponentClassification.M12Cover
  CFSG.ComponentClassification.M12Cover.InternalSylow CFSG.ComponentClassification.CentralCover in
theorem burnsideI22P5_M12c_Wodd :
    burnsideI22P5_M12c_W ≤ Subgroup.closure
      {a : NativeSporadic.M12 | a ∈ Subgroup.centralizer
        ({((d 27 : InternalSylow.S) : NativeSporadic.M12)} : Set NativeSporadic.M12) ∧
        Odd (orderOf a)} := by
  set C := Subgroup.centralizer
    ({((d 27 : InternalSylow.S) : NativeSporadic.M12)} : Set NativeSporadic.M12) with hC
  set A : Set NativeSporadic.M12 := {a | a ∈ C ∧ Odd (orderOf a)} with hA
  have hgodd : Odd (orderOf burnsideI22P5_M12c_g) := by
    rw [burnsideI22P5_M12c_g_order]; exact ⟨1, rfl⟩
  have hcomm : ∀ x : NativeSporadic.M12, x ∈ InternalSylow.S →
      x * burnsideI22P5_M12c_g * x⁻¹ * burnsideI22P5_M12c_g⁻¹ ∈ Subgroup.closure A := by
    intro x hx
    have hxC : x ∈ C := burnsideI22P5_M12c_S_le_C hx
    refine Subgroup.mul_mem _ (Subgroup.subset_closure ⟨C.mul_mem (C.mul_mem hxC
      burnsideI22P5_M12c_g_mem_C) (C.inv_mem hxC), ?_⟩)
      (Subgroup.subset_closure ⟨C.inv_mem burnsideI22P5_M12c_g_mem_C, ?_⟩)
    · have := MulEquiv.orderOf_eq (MulAut.conj x) burnsideI22P5_M12c_g
      rw [MulAut.conj_apply] at this
      rw [this]; exact hgodd
    · rw [orderOf_inv]; exact hgodd
  have hgen : ∀ i : Fin 4, ((d (burnsideI22P5_M12c_genF i) : InternalSylow.S) :
      NativeSporadic.M12) ∈ Subgroup.closure A := by
    intro i
    have hex : ∃ pr ∈ burnsideI22P5_M12c_commPairs, pr.2 = (burnsideI22P5_M12c_genF i : ℕ) := by
      revert i; decide
    obtain ⟨⟨k, κ⟩, hpr, hκ⟩ := hex
    obtain ⟨hk, hκ', heq⟩ := burnsideI22P5_M12c_comm_eq hpr
    have : burnsideI22P5_M12c_genF i = ⟨κ, hκ'⟩ := Fin.ext hκ.symm
    rw [this, heq]
    exact hcomm _ (d ⟨k, hk⟩).2
  have hmem : ∀ w : List (Fin 4),
      (((w.map fun i => d (burnsideI22P5_M12c_genF i)).prod : InternalSylow.S) :
        NativeSporadic.M12) ∈ Subgroup.closure A := by
    intro w
    induction w with
    | nil => exact Subgroup.one_mem _
    | cons i w ih =>
      rw [List.map_cons, List.prod_cons, Subgroup.coe_mul]
      exact Subgroup.mul_mem _ (hgen i) ih
  rintro _ ⟨j, hj, rfl⟩
  have hw := burnsideI22P5_M12c_wordTable_check j hj
  rw [← hw, burnsideI22P5_M12c_d_evalG]
  exact hmem _

open CFSG.Blueprint CFSG.ComponentClassification.M12Cover
  CFSG.ComponentClassification.M12Cover.InternalSylow CFSG.ComponentClassification.CentralCover in
theorem burnsideI22P5_M12c_f_diag : ∀ i : Fin 64, mIdx i i = 27 → fIdx i i = 1 := by
  decide +kernel

open CFSG.Blueprint CFSG.ComponentClassification.M12Cover
  CFSG.ComponentClassification.M12Cover.InternalSylow CFSG.ComponentClassification.CentralCover in
theorem burnsideI22P5_M12c_T_level
    {K : Type} [Group K] [Group.IsPerfect K]
    (π : K →* NativeSporadic.M12) {t : K}
    (hext : CFSG.ComponentClassification.CentralCover.IsCentralDoubleExt π t)
    (h4 : ∀ v : K, orderOf (π v) = 2 → fixedCount (π v) = 4 → orderOf v = 2)
    (h0 : ∀ v : K, orderOf (π v) = 2 → fixedCount (π v) = 0 → v ^ 2 = t)
    (u : K) (hπu : π u = ((d 27 : InternalSylow.S) : NativeSporadic.M12)) :
    (∀ y : K, π y ∈ InternalSylow.S → y * u = u * y) ∧
      ∀ x y : K, π x ∈ InternalSylow.S → π y ∈ InternalSylow.S → x ^ 2 = u → y ^ 2 = u * t →
        False := by
  obtain ⟨ι, hιsnd, hιt, -⟩ := exists_local_coordinates hext h4 h0
  have hu' : π u ∈ InternalSylow.S := hπu ▸ (d 27).2
  have ht' : π t ∈ InternalSylow.S := by
    have : π t = 1 := by
      have : t ∈ π.ker := by rw [hext.ker_eq]; exact Subgroup.mem_zpowers t
      exact this
    rw [this]; exact InternalSylow.S.one_mem
  have huR : (ι ⟨u, hu'⟩).snd = d 27 := Subtype.ext ((hιsnd _).trans hπu)
  constructor
  · intro y hy
    have hc := mem_center_R_of_snd huR
    have h1 := Subgroup.mem_center_iff.1 hc (ι ⟨y, hy⟩)
    have h2 : (⟨y, hy⟩ * ⟨u, hu'⟩ : InternalSylow.S.comap π) = ⟨u, hu'⟩ * ⟨y, hy⟩ :=
      ι.injective (by rw [map_mul, map_mul]; exact h1)
    exact congrArg Subtype.val h2
  · intro x y hx hy hx2 hy2
    have htT : ι ⟨t, ht'⟩ = ⟨1, 1⟩ := by
      have : (⟨t, ht'⟩ : InternalSylow.S.comap π) = ι.symm ⟨1, 1⟩ := Subtype.ext hιt.symm
      rw [this, MulEquiv.apply_symm_apply]
    have hsq : ∀ z : InternalSylow.S.comap π, (ι z * ι z).fst = fN (ι z).snd (ι z).snd := by
      intro z
      rw [CocycleExtension.mul_fst, zmod2_add_self, zero_add]
    have hx2' : (⟨x, hx⟩ * ⟨x, hx⟩ : InternalSylow.S.comap π) = ⟨u, hu'⟩ := Subtype.ext (by
      show x * x = u
      rw [← sq]; exact hx2)
    have hy2' : (⟨y, hy⟩ * ⟨y, hy⟩ : InternalSylow.S.comap π) = ⟨u, hu'⟩ * ⟨t, ht'⟩ :=
      Subtype.ext (by
        show y * y = u * t
        rw [← sq]; exact hy2)
    have e1 := congrArg ι hx2'
    rw [map_mul] at e1
    have e2 := congrArg ι hy2'
    rw [map_mul, map_mul, htT] at e2
    have hfx := hsq ⟨x, hx⟩
    rw [e1] at hfx
    have hfy := hsq ⟨y, hy⟩
    rw [e2, CocycleExtension.mul_fst] at hfy
    obtain ⟨i, hi⟩ := d_surjective (ι ⟨x, hx⟩).snd
    obtain ⟨j, hj⟩ := d_surjective (ι ⟨y, hy⟩).snd
    have hxs : (ι ⟨x, hx⟩).snd * (ι ⟨x, hx⟩).snd = d 27 := by
      have := congrArg CocycleExtension.snd e1
      rw [CocycleExtension.mul_snd] at this
      exact this.trans huR
    have hys : (ι ⟨y, hy⟩).snd * (ι ⟨y, hy⟩).snd = d 27 := by
      have := congrArg CocycleExtension.snd e2
      rw [CocycleExtension.mul_snd, CocycleExtension.mul_snd] at this
      exact this.trans (by show (ι ⟨u, hu'⟩).snd * 1 = d 27; rw [mul_one]; exact huR)
    rw [← hi, ← d_mul] at hxs
    rw [← hj, ← d_mul] at hys
    have hxi : mIdx i i = 27 := congrArg Fin.val (d_injective hxs)
    have hyj : mIdx j j = 27 := congrArg Fin.val (d_injective hys)
    rw [← hi, fN_apply, f_d, burnsideI22P5_M12c_f_diag i hxi] at hfx
    rw [← hj] at hfy
    have hf1 : f (ι ⟨u, hu'⟩).snd 1 = 0 := f_one_right _
    have hfy' : (ι ⟨u, hu'⟩).fst + 1 + f (ι ⟨u, hu'⟩).snd 1 = f (d j) (d j) := hfy
    rw [f_d, burnsideI22P5_M12c_f_diag j hyj, hf1, hfx] at hfy'
    revert hfy'
    decide

open CFSG.Blueprint CFSG.ComponentClassification.M12Cover
  CFSG.ComponentClassification.M12Cover.InternalSylow CFSG.ComponentClassification.CentralCover in
theorem burnsideI22P5_M12c_S_pGroup : IsPGroup 2 InternalSylow.S :=
  IsPGroup.of_card (n := 6) (by rw [InternalSylow.card_S]; norm_num)

open CFSG.Blueprint CFSG.ComponentClassification.M12Cover
  CFSG.ComponentClassification.M12Cover.InternalSylow CFSG.ComponentClassification.CentralCover in
theorem burnsideI22P5_M12c_S_odd : ¬ 2 ∣ InternalSylow.S.index := by
  intro hd
  have h := InternalSylow.S.card_mul_index
  rw [InternalSylow.card_S, CFSG.Sporadic.Mathieu.card_M12] at h
  have : InternalSylow.S.index = 1485 := by omega
  rw [this] at hd
  exact absurd hd (by norm_num)

open CFSG.Blueprint CFSG.ComponentClassification.M12Cover
  CFSG.ComponentClassification.M12Cover.InternalSylow CFSG.ComponentClassification.CentralCover in
theorem burnsideI22P5_M12c_d12_mem : ((d 12 : InternalSylow.S) : NativeSporadic.M12) ∈
    burnsideI22P5_M12c_W := burnsideI22P5_M12c_mem_W (by decide)

open CFSG.Blueprint CFSG.ComponentClassification.M12Cover
  CFSG.ComponentClassification.M12Cover.InternalSylow CFSG.ComponentClassification.CentralCover in
theorem burnsideI22P5_M12c_d12_sq :
    ((d 12 : InternalSylow.S) : NativeSporadic.M12) ^ 2 =
      ((d 27 : InternalSylow.S) : NativeSporadic.M12) := by
  rw [sq, ← Subgroup.coe_mul, ← d_mul]
  have : mTab 12 12 = 27 := by decide +kernel
  rw [this]

open CFSG.Blueprint CFSG.ComponentClassification.M12Cover
  CFSG.ComponentClassification.M12Cover.InternalSylow CFSG.ComponentClassification.CentralCover
  CFSG.ASVolI.ChIJK in
theorem burnsideI22P5_M12_c
    {K : Type} [Group K] [Finite K] (hK : CFSG.IsQuasisimple K)
    (hZ : Subgroup.center K ≠ ⊥)
    (h : CFSG.Blueprint.NativeSporadic.IsSporadic (K ⧸ Subgroup.center K) .M12)
    (u : K) (hu : u ∉ Subgroup.center K) (hu2 : u ^ 2 = 1) : UniqueSquareInCoset K u := by
  classical
  obtain ⟨hZ2, ⟨e⟩⟩ := burnsideI22P5_M12_setup hK hZ h
  obtain ⟨t, ht, hZt, h4, h0⟩ := burnsideI22P5_M12_lift hK hZ2 e
  haveI : Group.IsPerfect K := hK.1
  let π : K →* NativeSporadic.M12 := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K))
  have hπ : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : π.ker = Subgroup.zpowers t := by
    rw [← hZt]
    ext l
    simp only [π, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hext : IsCentralDoubleExt π t := ⟨hπ, hZt ▸ Subgroup.mem_zpowers t, ht, hker⟩
  have h4' : ∀ v : K, orderOf (π v) = 2 → fixedCount (π v) = 4 → orderOf v = 2 := h4
  have h0' : ∀ v : K, orderOf (π v) = 2 → fixedCount (π v) = 0 → v ^ 2 = t :=
    fun v hv hf => (h0 v hv hf).1
  have ht1 : t ≠ 1 := by
    intro h1; rw [h1, orderOf_one] at ht; exact absurd ht (by norm_num)
  have hπu1 : π u ≠ 1 := fun h1 => hu (by
    rw [hZt, ← hker]; exact h1)
  have hπu2 : (π u) ^ 2 = 1 := by rw [← map_pow, hu2, map_one]
  have hord : orderOf (π u) = 2 := orderOf_eq_prime hπu2 hπu1
  have hfix : fixedCount (π u) = 4 := by
    rcases fixedCount_of_orderOf_eq_two (π u) hord with h' | h'
    · exact h'
    · exfalso
      have := h0' u hord h'
      rw [hu2] at this
      exact ht1 this.symm
  obtain ⟨g₁, hg₁⟩ := conj_elemR_of_fixedCount_four (π u) hord hfix
  obtain ⟨g₂, hg₂⟩ := conj_elemR_of_fixedCount_four ((d 27 : InternalSylow.S) : NativeSporadic.M12)
    burnsideI22P5_M12c_d27_order burnsideI22P5_M12c_d27_fixed
  obtain ⟨a, ha⟩ := hπ (g₂ * g₁⁻¹)
  have hπu' : π (a * u * a⁻¹) = ((d 27 : InternalSylow.S) : NativeSporadic.M12) := by
    rw [map_mul, map_mul, map_inv, ha, ← hg₁, ← hg₂]
    group
  suffices H : UniqueSquareInCoset K (a * u * a⁻¹) by
    have := burnsideI22P5_unique_square_conj a⁻¹ (a * u * a⁻¹) H
    simpa [mul_assoc] using this
  obtain ⟨hTu, hU⟩ := burnsideI22P5_M12c_T_level π hext h4' h0' (a * u * a⁻¹) hπu'
  refine burnsideI22P5_unique_square_of_data π hπ ht hZt hker (a * u * a⁻¹) InternalSylow.S
    burnsideI22P5_M12c_S_pGroup burnsideI22P5_M12c_S_odd hTu burnsideI22P5_M12c_W
    (burnsideI22P5_M12c_W_le_S |> fun hle => burnsideI22P5_M12c_S_pGroup.to_le hle)
    ?_ ?_ ((d 12 : InternalSylow.S) : NativeSporadic.M12) burnsideI22P5_M12c_d12_mem ?_ ∅
    (fun g hg => absurd hg (Set.notMem_empty g)) ?_
  · rw [hπu']; exact burnsideI22P5_M12c_Wn
  · rw [hπu']; exact burnsideI22P5_M12c_Wodd
  · rw [hπu']; exact burnsideI22P5_M12c_d12_sq
  · intro x y hx hy _ _ hx2 hy2
    exact hU x y hx hy hx2 hy2

open CFSG.ComponentClassification.J2Cover.Models CFSG.ComponentClassification.J2Cover
  CFSG.ComponentClassification.CentralCover in
theorem burnsideI22P5_J2c_Widx_mul :
    ∀ i ∈ oddWidx, ∀ j ∈ oddWidx, mulIdx i j ∈ oddWidx := by
  decide +kernel

open CFSG.ComponentClassification.J2Cover.Models CFSG.ComponentClassification.J2Cover
  CFSG.ComponentClassification.CentralCover in
theorem burnsideI22P5_J2c_Widx_inv : ∀ i ∈ oddWidx, invIdx i ∈ oddWidx := by
  decide +kernel

open CFSG.ComponentClassification.J2Cover.Models CFSG.ComponentClassification.J2Cover
  CFSG.ComponentClassification.CentralCover in
theorem burnsideI22P5_J2c_Widx_lt : ∀ i ∈ oddWidx, i < 128 := by
  decide +kernel

open CFSG.ComponentClassification.J2Cover.Models CFSG.ComponentClassification.J2Cover
  CFSG.ComponentClassification.CentralCover in
@[expose] noncomputable def burnsideI22P5_J2c_W :
    Subgroup Models.P where
  carrier := {x | ∃ k : ℕ, k ∈ oddWidx ∧ incl (elt k) = x}
  mul_mem' := by
    rintro _ _ ⟨i, hi, rfl⟩ ⟨j, hj, rfl⟩
    refine ⟨mulIdx i j, burnsideI22P5_J2c_Widx_mul i hi j hj, ?_⟩
    rw [(mulIdx_spec (burnsideI22P5_J2c_Widx_lt j hj)).2, map_mul]
  one_mem' := ⟨0, by decide, by rw [elt_zero, map_one]⟩
  inv_mem' := by
    rintro _ ⟨i, hi, rfl⟩
    refine ⟨invIdx i, burnsideI22P5_J2c_Widx_inv i hi, ?_⟩
    rw [← (elt_inv (burnsideI22P5_J2c_Widx_lt i hi)).2, map_inv]

open CFSG.ComponentClassification.J2Cover.Models CFSG.ComponentClassification.J2Cover
  CFSG.ComponentClassification.CentralCover in
theorem burnsideI22P5_J2c_mem_W
    {k : ℕ} (hk : k ∈ oddWidx) :
    incl (elt k) ∈ burnsideI22P5_J2c_W := ⟨k, hk, rfl⟩

open CFSG.ComponentClassification.J2Cover.Models CFSG.ComponentClassification.J2Cover
  CFSG.ComponentClassification.CentralCover CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native in
theorem burnsideI22P5_J2c_check_parts :
    wordPerm oddW3 * (wordPerm oddW3 * wordPerm oddW3) = 1 ∧ wordPerm oddW3 ≠ 1 ∧
    wordPerm oddW5 * ((wordPerm oddW5 * wordPerm oddW5) * (wordPerm oddW5 * wordPerm oddW5)) = 1 ∧
    wordPerm oddW5 ≠ 1 ∧
    wordPerm oddW3 * (elt 4 : Perm315) = (elt 4 : Perm315) * wordPerm oddW3 ∧
    wordPerm oddW5 * (elt 4 : Perm315) = (elt 4 : Perm315) * wordPerm oddW5 ∧
    (∀ k, k < 128 → k ∈ oddWidx →
      (nth 0 oddC3 k < 128 ∧ nth 0 oddC3 k ∈ oddWidx ∧
        wordPerm oddW3 * (elt k : Perm315) * (wordPerm oddW3 * wordPerm oddW3) =
          (elt (nth 0 oddC3 k) : Perm315)) ∧
      (nth 0 oddC3i k < 128 ∧ nth 0 oddC3i k ∈ oddWidx ∧
        (wordPerm oddW3 * wordPerm oddW3) * (elt k : Perm315) * wordPerm oddW3 =
          (elt (nth 0 oddC3i k) : Perm315)) ∧
      (nth 0 oddC5 k < 128 ∧ nth 0 oddC5 k ∈ oddWidx ∧
        wordPerm oddW5 * (elt k : Perm315) *
          ((wordPerm oddW5 * wordPerm oddW5) * (wordPerm oddW5 * wordPerm oddW5)) =
          (elt (nth 0 oddC5 k) : Perm315)) ∧
      (nth 0 oddC5i k < 128 ∧ nth 0 oddC5i k ∈ oddWidx ∧
        ((wordPerm oddW5 * wordPerm oddW5) * (wordPerm oddW5 * wordPerm oddW5)) *
          (elt k : Perm315) * wordPerm oddW5 = (elt (nth 0 oddC5i k) : Perm315))) ∧
    (∀ i, i < 128 → mulIdx i i = 4 → bitAt fRows i i = true) := by
  have h := Certificates.certificate7290
  simp only [oddCheck, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, allLt_iff] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  have rg3 : Rep 315 (wordArr oddW3) (wordPerm oddW3) := rep_wordArr oddW3
  have rg5 : Rep 315 (wordArr oddW5) (wordPerm oddW5) := rep_wordArr oddW5
  have rid : Rep 315 (idA 315) 1 := rep_idA
  have rg3s := rep_compA rg3 rg3
  have rg5s := rep_compA rg5 rg5
  have rg5i := rep_compA rg5s rg5s
  have re : ∀ {k : ℕ}, k < 128 → Rep 315 eltArrs[k]! (elt k : Perm315) := fun hk => rep_eltArrs hk
  refine ⟨(eqA_iff (rep_compA rg3 rg3s) rid).1 h1, ?_, (eqA_iff (rep_compA rg5 rg5i) rid).1 h3, ?_,
    (eqA_iff (rep_compA rg3 (re (by norm_num))) (rep_compA (re (by norm_num)) rg3)).1 h5,
    (eqA_iff (rep_compA rg5 (re (by norm_num))) (rep_compA (re (by norm_num)) rg5)).1 h6, ?_, ?_⟩
  · intro h
    rw [(eqA_iff rg3 rid).2 h] at h2
    exact absurd h2 (by simp)
  · intro h
    rw [(eqA_iff rg5 rid).2 h] at h4
    exact absurd h4 (by simp)
  · intro k hk hkW
    have hk' := h7 k hk
    have hkB : oddWidxB k = true := by simp [oddWidxB, hkW]
    simp only [hkB, Bool.not_true, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq] at hk'
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩, a7⟩, a8⟩, a9⟩, a10⟩, a11⟩, a12⟩ := hk'
    have hw : ∀ j, oddWidxB j = true → j ∈ oddWidx := fun j hj => by simpa [oddWidxB] using hj
    have hl : ∀ j, oddWidxB j = true → j < 128 := fun j hj =>
      burnsideI22P5_J2c_Widx_lt j (hw j hj)
    refine ⟨⟨a1, hw _ a2, ?_⟩, ⟨a4, hw _ a5, ?_⟩, ⟨a7, hw _ a8, ?_⟩, ⟨a10, hw _ a11, ?_⟩⟩
    · exact (eqA_iff (rep_compA (rep_compA rg3 (re hk)) rg3s) (re a1)).1 a3
    · exact (eqA_iff (rep_compA (rep_compA rg3s (re hk)) rg3) (re a4)).1 a6
    · exact (eqA_iff (rep_compA (rep_compA rg5 (re hk)) rg5i) (re a7)).1 a9
    · exact (eqA_iff (rep_compA (rep_compA rg5i (re hk)) rg5) (re a10)).1 a12
  · intro i hi hmi
    have := h8 i hi
    simpa [hmi] using this

open CFSG.ComponentClassification.J2Cover.Models CFSG.ComponentClassification.J2Cover
  CFSG.ComponentClassification.CentralCover in
theorem burnsideI22P5_J2c_card_C :
    Nat.card (Subgroup.centralizer ({incl (elt 4)} : Set Models.P)) = 1920 := by
  have h1 := CFSG.ComponentClassification.M12Cover.card_centralizer_eq_centralizerIn Models.P
    (incl (elt 4))
  rw [h1, incl_coe, Models.P_eq_autP]
  have hy2 : orderOf ((elt 4 : S) : Perm315) = 2 := by
    rw [Subgroup.orderOf_coe]; exact orderOf_elt_four
  have hyP : ((elt 4 : S) : Perm315) ∈ CFSG.ComponentClassification.J2Cover.P := by
    rw [← Models.P_eq_autP]; exact S_le_P (elt 4).2
  obtain ⟨r, hr, c, hc, hrc⟩ := inner_classes.1 _ hyP hy2
  have hcard := Nat.card_congr (CFSG.ComponentClassification.M12Cover.centralizerInConjEquiv
    CFSG.ComponentClassification.J2Cover.P hc r).toEquiv
  rw [← hrc] at hcard
  have h128 : 128 ∣ Nat.card (CFSG.Sporadic.Schreier.centralizerIn CFSG.ComponentClassification.J2Cover.P ((elt 4 : S) : Perm315)) := by
    have hle : S ≤ CFSG.Sporadic.Schreier.centralizerIn CFSG.ComponentClassification.J2Cover.P ((elt 4 : S) : Perm315) := fun s hs => by
      refine ⟨by rw [← Models.P_eq_autP]; exact S_le_P hs, ?_⟩
      exact Subgroup.mem_centralizer_singleton_iff.2 (burnsideI22P5_J2_elt4_central hs)
    have := Subgroup.card_dvd_of_le hle
    rwa [card_S] at this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exfalso
    rw [← hcard, inner_classes.2.2.1, (cent2B_facts).2.1] at h128
    exact absurd h128 (by norm_num)
  · rw [← hcard, inner_classes.2.2.2.2, (cent2A_facts).2.1]

open CFSG.ComponentClassification.J2Cover.Models CFSG.ComponentClassification.J2Cover
  CFSG.ComponentClassification.CentralCover in
@[expose] noncomputable def burnsideI22P5_J2c_g3 :
    Models.P := ⟨wordPerm oddW3, wordPerm_mem _⟩

open CFSG.ComponentClassification.J2Cover.Models CFSG.ComponentClassification.J2Cover
  CFSG.ComponentClassification.CentralCover in
@[expose] noncomputable def burnsideI22P5_J2c_g5 :
    Models.P := ⟨wordPerm oddW5, wordPerm_mem _⟩

open CFSG.ComponentClassification.J2Cover.Models CFSG.ComponentClassification.J2Cover
  CFSG.ComponentClassification.CentralCover in
theorem burnsideI22P5_J2c_g3_order :
    orderOf burnsideI22P5_J2c_g3 = 3 := by
  obtain ⟨h1, h2, -⟩ := burnsideI22P5_J2c_check_parts
  refine orderOf_eq_prime ?_ ?_
  · apply Subtype.ext
    show (wordPerm oddW3) ^ 3 = 1
    calc (wordPerm oddW3) ^ 3 = wordPerm oddW3 * (wordPerm oddW3 * wordPerm oddW3) := by
          rw [pow_succ, pow_two, mul_assoc]
      _ = 1 := h1
  · intro h; exact h2 (congrArg Subtype.val h)

open CFSG.ComponentClassification.J2Cover.Models CFSG.ComponentClassification.J2Cover
  CFSG.ComponentClassification.CentralCover in
theorem burnsideI22P5_J2c_g5_order :
    orderOf burnsideI22P5_J2c_g5 = 5 := by
  obtain ⟨-, -, h3, h4, -⟩ := burnsideI22P5_J2c_check_parts
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  refine orderOf_eq_prime ?_ ?_
  · apply Subtype.ext
    show (wordPerm oddW5) ^ 5 = 1
    calc (wordPerm oddW5) ^ 5 = wordPerm oddW5 *
        ((wordPerm oddW5 * wordPerm oddW5) * (wordPerm oddW5 * wordPerm oddW5)) := by
          simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      _ = 1 := h3
  · intro h; exact h4 (congrArg Subtype.val h)

open CFSG.ComponentClassification.J2Cover.Models CFSG.ComponentClassification.J2Cover
  CFSG.ComponentClassification.CentralCover in
theorem burnsideI22P5_J2c_g3_mem_C :
    burnsideI22P5_J2c_g3 ∈ Subgroup.centralizer ({incl (elt 4)} : Set Models.P) := by
  obtain ⟨-, -, -, -, h5, -⟩ := burnsideI22P5_J2c_check_parts
  rw [Subgroup.mem_centralizer_singleton_iff]
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, incl_coe]
  exact h5

open CFSG.ComponentClassification.J2Cover.Models CFSG.ComponentClassification.J2Cover
  CFSG.ComponentClassification.CentralCover in
theorem burnsideI22P5_J2c_g5_mem_C :
    burnsideI22P5_J2c_g5 ∈ Subgroup.centralizer ({incl (elt 4)} : Set Models.P) := by
  obtain ⟨-, -, -, -, -, h6, -⟩ := burnsideI22P5_J2c_check_parts
  rw [Subgroup.mem_centralizer_singleton_iff]
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, incl_coe]
  exact h6

open CFSG.ComponentClassification.J2Cover.Models CFSG.ComponentClassification.J2Cover
  CFSG.ComponentClassification.CentralCover in
theorem burnsideI22P5_J2c_S_conj_idx :
    ∀ i < 128, ∀ k ∈ oddWidx, mulIdx (mulIdx i k) (invIdx i) ∈ oddWidx := by
  decide +kernel

open CFSG.ComponentClassification.J2Cover.Models CFSG.ComponentClassification.J2Cover
  CFSG.ComponentClassification.CentralCover in
theorem burnsideI22P5_J2c_S_conj
    {s w : Models.P} (hs : s ∈ Sp) (hw : w ∈ burnsideI22P5_J2c_W) :
    s * w * s⁻¹ ∈ burnsideI22P5_J2c_W := by
  obtain ⟨i, hi, hsi⟩ := exists_elt (σ := (s : Perm315)) hs
  obtain ⟨k, hk, rfl⟩ := hw
  have hs' : s = incl (elt i) := Subtype.ext (by rw [incl_coe, hsi])
  have hk128 := burnsideI22P5_J2c_Widx_lt k hk
  have hinv := elt_inv hi
  have hm1 := mulIdx_spec (a := i) hk128
  have hm2 := mulIdx_spec (a := mulIdx i k) hinv.1
  refine ⟨mulIdx (mulIdx i k) (invIdx i), burnsideI22P5_J2c_S_conj_idx i hi k hk, ?_⟩
  rw [hs', hm2.2, hm1.2, ← hinv.2]
  simp only [map_mul, map_inv]

open CFSG.ComponentClassification.J2Cover.Models CFSG.ComponentClassification.J2Cover
  CFSG.ComponentClassification.CentralCover in
theorem burnsideI22P5_J2c_g3_inv_coe :
    ((burnsideI22P5_J2c_g3⁻¹ : Models.P) : Perm315) = wordPerm oddW3 * wordPerm oddW3 := by
  obtain ⟨h1, -⟩ := burnsideI22P5_J2c_check_parts
  rw [Subgroup.coe_inv]
  exact inv_eq_of_mul_eq_one_right h1

open CFSG.ComponentClassification.J2Cover.Models CFSG.ComponentClassification.J2Cover
  CFSG.ComponentClassification.CentralCover in
theorem burnsideI22P5_J2c_g5_inv_coe :
    ((burnsideI22P5_J2c_g5⁻¹ : Models.P) : Perm315) =
      (wordPerm oddW5 * wordPerm oddW5) * (wordPerm oddW5 * wordPerm oddW5) := by
  obtain ⟨-, -, h3, -⟩ := burnsideI22P5_J2c_check_parts
  rw [Subgroup.coe_inv]
  exact inv_eq_of_mul_eq_one_right h3

open CFSG.ComponentClassification.J2Cover.Models CFSG.ComponentClassification.J2Cover
  CFSG.ComponentClassification.CentralCover in
theorem burnsideI22P5_J2c_g3_conj
    {w : Models.P} (hw : w ∈ burnsideI22P5_J2c_W) :
    burnsideI22P5_J2c_g3 * w * burnsideI22P5_J2c_g3⁻¹ ∈ burnsideI22P5_J2c_W := by
  obtain ⟨k, hk, rfl⟩ := hw
  obtain ⟨-, -, -, -, -, -, hall, -⟩ := burnsideI22P5_J2c_check_parts
  obtain ⟨⟨ha1, ha2, ha3⟩, -⟩ := hall k (burnsideI22P5_J2c_Widx_lt k hk) hk
  refine ⟨nth 0 oddC3 k, ha2, ?_⟩
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, incl_coe, burnsideI22P5_J2c_g3_inv_coe, incl_coe]
  exact ha3.symm

open CFSG.ComponentClassification.J2Cover.Models CFSG.ComponentClassification.J2Cover
  CFSG.ComponentClassification.CentralCover in
theorem burnsideI22P5_J2c_g3i_conj
    {w : Models.P} (hw : w ∈ burnsideI22P5_J2c_W) :
    burnsideI22P5_J2c_g3⁻¹ * w * burnsideI22P5_J2c_g3⁻¹⁻¹ ∈ burnsideI22P5_J2c_W := by
  obtain ⟨k, hk, rfl⟩ := hw
  obtain ⟨-, -, -, -, -, -, hall, -⟩ := burnsideI22P5_J2c_check_parts
  obtain ⟨-, ⟨ha1, ha2, ha3⟩, -⟩ := hall k (burnsideI22P5_J2c_Widx_lt k hk) hk
  refine ⟨nth 0 oddC3i k, ha2, ?_⟩
  apply Subtype.ext
  rw [inv_inv, Subgroup.coe_mul, Subgroup.coe_mul, incl_coe, burnsideI22P5_J2c_g3_inv_coe,
    incl_coe]
  exact ha3.symm

open CFSG.ComponentClassification.J2Cover.Models CFSG.ComponentClassification.J2Cover
  CFSG.ComponentClassification.CentralCover in
theorem burnsideI22P5_J2c_g5_conj
    {w : Models.P} (hw : w ∈ burnsideI22P5_J2c_W) :
    burnsideI22P5_J2c_g5 * w * burnsideI22P5_J2c_g5⁻¹ ∈ burnsideI22P5_J2c_W := by
  obtain ⟨k, hk, rfl⟩ := hw
  obtain ⟨-, -, -, -, -, -, hall, -⟩ := burnsideI22P5_J2c_check_parts
  obtain ⟨-, -, ⟨ha1, ha2, ha3⟩, -⟩ := hall k (burnsideI22P5_J2c_Widx_lt k hk) hk
  refine ⟨nth 0 oddC5 k, ha2, ?_⟩
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, incl_coe, burnsideI22P5_J2c_g5_inv_coe, incl_coe]
  exact ha3.symm

open CFSG.ComponentClassification.J2Cover.Models CFSG.ComponentClassification.J2Cover
  CFSG.ComponentClassification.CentralCover in
theorem burnsideI22P5_J2c_g5i_conj
    {w : Models.P} (hw : w ∈ burnsideI22P5_J2c_W) :
    burnsideI22P5_J2c_g5⁻¹ * w * burnsideI22P5_J2c_g5⁻¹⁻¹ ∈ burnsideI22P5_J2c_W := by
  obtain ⟨k, hk, rfl⟩ := hw
  obtain ⟨-, -, -, -, -, -, hall, -⟩ := burnsideI22P5_J2c_check_parts
  obtain ⟨-, -, -, ⟨ha1, ha2, ha3⟩⟩ := hall k (burnsideI22P5_J2c_Widx_lt k hk) hk
  refine ⟨nth 0 oddC5i k, ha2, ?_⟩
  apply Subtype.ext
  rw [inv_inv, Subgroup.coe_mul, Subgroup.coe_mul, incl_coe, burnsideI22P5_J2c_g5_inv_coe,
    incl_coe]
  exact ha3.symm

open CFSG.ComponentClassification.J2Cover.Models CFSG.ComponentClassification.J2Cover
  CFSG.ComponentClassification.CentralCover in
theorem burnsideI22P5_J2c_closure_le_normalizer :
    Subgroup.closure ((Sp : Set Models.P) ∪ {burnsideI22P5_J2c_g3, burnsideI22P5_J2c_g5}) ≤
      Subgroup.normalizer (burnsideI22P5_J2c_W : Set Models.P) := by
  rw [Subgroup.closure_le]
  rintro x (hx | hx)
  · rw [SetLike.mem_coe, Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh; exact burnsideI22P5_J2c_S_conj hx hh
    · intro hh
      have := burnsideI22P5_J2c_S_conj (Sp.inv_mem hx) hh
      simpa [mul_assoc] using this
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · rw [SetLike.mem_coe, Subgroup.mem_normalizer_iff]
      intro h
      constructor
      · intro hh; exact burnsideI22P5_J2c_g3_conj hh
      · intro hh
        have := burnsideI22P5_J2c_g3i_conj hh
        simpa [mul_assoc] using this
    · rw [SetLike.mem_coe, Subgroup.mem_normalizer_iff]
      intro h
      constructor
      · intro hh; exact burnsideI22P5_J2c_g5_conj hh
      · intro hh
        have := burnsideI22P5_J2c_g5i_conj hh
        simpa [mul_assoc] using this

open CFSG.ComponentClassification.J2Cover.Models CFSG.ComponentClassification.J2Cover
  CFSG.ComponentClassification.CentralCover in
theorem burnsideI22P5_J2c_card_Sp :
    Nat.card Sp = 128 := by
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe S_le_P).toEquiv, card_S]

open CFSG.ComponentClassification.J2Cover.Models CFSG.ComponentClassification.J2Cover
  CFSG.ComponentClassification.CentralCover in
theorem burnsideI22P5_J2c_Sp_le_C :
    Sp ≤ Subgroup.centralizer ({incl (elt 4)} : Set Models.P) := fun s hs => by
  rw [Subgroup.mem_centralizer_singleton_iff]
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, incl_coe]
  exact burnsideI22P5_J2_elt4_central hs

open CFSG.ComponentClassification.J2Cover.Models CFSG.ComponentClassification.J2Cover
  CFSG.ComponentClassification.CentralCover in
theorem burnsideI22P5_J2c_C_eq :
    Subgroup.centralizer ({incl (elt 4)} : Set Models.P) =
      Subgroup.closure ((Sp : Set Models.P) ∪ {burnsideI22P5_J2c_g3, burnsideI22P5_J2c_g5}) := by
  set C := Subgroup.centralizer ({incl (elt 4)} : Set Models.P) with hC
  set D := Subgroup.closure ((Sp : Set Models.P) ∪
    {burnsideI22P5_J2c_g3, burnsideI22P5_J2c_g5}) with hD
  have hDC : D ≤ C := (Subgroup.closure_le C).2 (Set.union_subset
    (fun s hs => burnsideI22P5_J2c_Sp_le_C hs) (by
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact burnsideI22P5_J2c_g3_mem_C
      · exact burnsideI22P5_J2c_g5_mem_C))
  have hSD : Sp ≤ D := fun s hs => Subgroup.subset_closure (Or.inl hs)
  have hg3D : burnsideI22P5_J2c_g3 ∈ D := Subgroup.subset_closure (Or.inr (Or.inl rfl))
  have hg5D : burnsideI22P5_J2c_g5 ∈ D := Subgroup.subset_closure (Or.inr (Or.inr rfl))
  have h128 : 128 ∣ Nat.card D := by
    have := Subgroup.card_dvd_of_le hSD
    rwa [burnsideI22P5_J2c_card_Sp] at this
  have h3 : 3 ∣ Nat.card D := by
    have := Subgroup.orderOf_dvd_natCard D hg3D
    rwa [burnsideI22P5_J2c_g3_order] at this
  have h5 : 5 ∣ Nat.card D := by
    have := Subgroup.orderOf_dvd_natCard D hg5D
    rwa [burnsideI22P5_J2c_g5_order] at this
  have h1920 : 1920 ∣ Nat.card D := by
    have h384 : 384 ∣ Nat.card D :=
      Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 128 3) h128 h3
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 384 5) h384 h5
  have hcardC : Nat.card C = 1920 := burnsideI22P5_J2c_card_C
  have hge : 1920 ≤ Nat.card D := Nat.le_of_dvd Nat.card_pos h1920
  exact (Subgroup.eq_of_le_of_card_ge hDC (by omega)).symm

open CFSG.ComponentClassification.J2Cover.Models CFSG.ComponentClassification.J2Cover
  CFSG.ComponentClassification.CentralCover in
theorem burnsideI22P5_J2c_Wn :
    ∀ c ∈ Subgroup.centralizer ({incl (elt 4)} : Set Models.P), ∀ w ∈ burnsideI22P5_J2c_W,
      c * w * c⁻¹ ∈ burnsideI22P5_J2c_W := by
  intro c hc w hw
  rw [burnsideI22P5_J2c_C_eq] at hc
  have := Subgroup.mem_normalizer_iff.1 (burnsideI22P5_J2c_closure_le_normalizer hc) w
  exact this.1 hw

open CFSG.ComponentClassification.J2Cover.Models CFSG.ComponentClassification.J2Cover
  CFSG.ComponentClassification.CentralCover in
theorem burnsideI22P5_J2c_g5_conj_eq
    {k : ℕ} (hk : k ∈ oddWidx) :
    burnsideI22P5_J2c_g5 * incl (elt k) * burnsideI22P5_J2c_g5⁻¹ =
      incl (elt (nth 0 oddC5 k)) := by
  obtain ⟨-, -, -, -, -, -, hall, -⟩ := burnsideI22P5_J2c_check_parts
  obtain ⟨-, -, ⟨ha1, ha2, ha3⟩, -⟩ := hall k (burnsideI22P5_J2c_Widx_lt k hk) hk
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, incl_coe, burnsideI22P5_J2c_g5_inv_coe, incl_coe]
  exact ha3

open CFSG.ComponentClassification.J2Cover.Models CFSG.ComponentClassification.J2Cover
  CFSG.ComponentClassification.CentralCover in
@[expose] def burnsideI22P5_J2c_commPairs : List (ℕ × ℕ) :=
  [(70, 11), (116, 32), (85, 37), (18, 86)]

open CFSG.ComponentClassification.J2Cover.Models CFSG.ComponentClassification.J2Cover
  CFSG.ComponentClassification.CentralCover in
theorem burnsideI22P5_J2c_commPairs_check :
    ∀ pr ∈ burnsideI22P5_J2c_commPairs, pr.1 ∈ oddWidx ∧ invIdx pr.1 ∈ oddWidx ∧
      mulIdx pr.1 (nth 0 oddC5 (invIdx pr.1)) = pr.2 ∧ pr.2 < 128 := by
  decide +kernel

open CFSG.ComponentClassification.J2Cover.Models CFSG.ComponentClassification.J2Cover
  CFSG.ComponentClassification.CentralCover in
theorem burnsideI22P5_J2c_comm_eq
    {k κ : ℕ} (h : (k, κ) ∈ burnsideI22P5_J2c_commPairs) :
    incl (elt κ) = incl (elt k) * burnsideI22P5_J2c_g5 * (incl (elt k))⁻¹ *
      burnsideI22P5_J2c_g5⁻¹ := by
  obtain ⟨hkW, hiW, hm, hκ⟩ := burnsideI22P5_J2c_commPairs_check (k, κ) h
  have hk128 := burnsideI22P5_J2c_Widx_lt k hkW
  have hinv := elt_inv hk128
  have hg := burnsideI22P5_J2c_g5_conj_eq hiW
  have hnc : nth 0 oddC5 (invIdx k) < 128 := by
    obtain ⟨-, -, ⟨-, ha2, -⟩, -⟩ := (burnsideI22P5_J2c_check_parts.2.2.2.2.2.2.1 (invIdx k)
      (burnsideI22P5_J2c_Widx_lt _ hiW) hiW)
    exact burnsideI22P5_J2c_Widx_lt _ ha2
  have hm' := mulIdx_spec (a := k) hnc
  have hmm : mulIdx k (nth 0 oddC5 (invIdx k)) = κ := hm
  rw [← hmm, hm'.2, map_mul, ← hg, ← hinv.2, map_inv]
  group

open CFSG.ComponentClassification.J2Cover.Models CFSG.ComponentClassification.J2Cover
  CFSG.ComponentClassification.CentralCover in
@[expose] def burnsideI22P5_J2c_genN : Fin 4 → ℕ := ![11, 32, 37, 86]

open CFSG.ComponentClassification.J2Cover.Models CFSG.ComponentClassification.J2Cover
  CFSG.ComponentClassification.CentralCover in
@[expose] def burnsideI22P5_J2c_evalG (w : List (Fin 4)) : ℕ :=
  w.foldr (fun i acc => mulIdx (burnsideI22P5_J2c_genN i) acc) 0

open CFSG.ComponentClassification.J2Cover.Models CFSG.ComponentClassification.J2Cover
  CFSG.ComponentClassification.CentralCover in

open CFSG.ComponentClassification.J2Cover.Models CFSG.ComponentClassification.J2Cover
  CFSG.ComponentClassification.CentralCover in
theorem burnsideI22P5_J2c_evalG_spec
    (w : List (Fin 4)) :
    burnsideI22P5_J2c_evalG w < 128 ∧
      incl (elt (burnsideI22P5_J2c_evalG w)) =
        (w.map fun i => incl (elt (burnsideI22P5_J2c_genN i))).prod := by
  induction w with
  | nil => exact ⟨by decide, by simp [burnsideI22P5_J2c_evalG, elt_zero]⟩
  | cons i w ih =>
    obtain ⟨ih1, ih2⟩ := ih
    have hm := mulIdx_spec (a := burnsideI22P5_J2c_genN i) ih1
    have hev : burnsideI22P5_J2c_evalG (i :: w) =
        mulIdx (burnsideI22P5_J2c_genN i) (burnsideI22P5_J2c_evalG w) := rfl
    rw [hev, List.map_cons, List.prod_cons]
    refine ⟨hm.1, ?_⟩
    rw [hm.2, map_mul, ih2]

open CFSG.ComponentClassification.J2Cover.Models CFSG.ComponentClassification.J2Cover
  CFSG.ComponentClassification.CentralCover in
@[expose] def burnsideI22P5_J2c_wordTable : List (List (Fin 4)) :=
  [[], [0, 0, 0], [], [], [0, 0], [], [], [], [], [], [], [0], [], [], [], [], [], [], [1, 0], [], [], [], [], [2, 0], [], [], [], [], [], [], [], [], [1], [], [], [], [], [2], [], [], [1, 0, 0], [], [], [], [], [], [0, 3], [], [2, 0, 0], [], [], [], [], [], [], [], [], [0, 1], [], [], [], [], [0, 2], [], [], [], [], [], [], [], [3, 0, 0], [], [], [], [], [], [], [], [], [], [1, 3], [1, 2, 0], [], [2, 3, 1], [], [3, 2], [3], [], [2, 3], [], [], [], [], [3, 2, 1], [2, 1, 0], [3, 1], [], [], [], [], [], [], [], [], [], [], [], [], [3, 0], [], [], [], [], [], [], [3, 1, 0], [1, 2], [3, 2, 1, 0], [], [2, 3, 0], [3, 2, 0], [], [2, 3, 1, 0], [2, 1], [1, 3, 0], [], [], []]

open CFSG.ComponentClassification.J2Cover.Models CFSG.ComponentClassification.J2Cover
  CFSG.ComponentClassification.CentralCover in
theorem burnsideI22P5_J2c_wordTable_check :
    ∀ j ∈ oddWidx, burnsideI22P5_J2c_evalG (burnsideI22P5_J2c_wordTable.getD j []) = j := by
  decide +kernel

open CFSG.ComponentClassification.J2Cover.Models CFSG.ComponentClassification.J2Cover
  CFSG.ComponentClassification.CentralCover in
theorem burnsideI22P5_J2c_Wodd :
    burnsideI22P5_J2c_W ≤ Subgroup.closure
      {a : Models.P | a ∈ Subgroup.centralizer ({incl (elt 4)} : Set Models.P) ∧
        Odd (orderOf a)} := by
  set C := Subgroup.centralizer ({incl (elt 4)} : Set Models.P) with hC
  set A : Set Models.P := {a | a ∈ C ∧ Odd (orderOf a)} with hA
  have hg5odd : Odd (orderOf burnsideI22P5_J2c_g5) := by
    rw [burnsideI22P5_J2c_g5_order]; exact ⟨2, rfl⟩
  have hcomm : ∀ x : Models.P, x ∈ Sp →
      x * burnsideI22P5_J2c_g5 * x⁻¹ * burnsideI22P5_J2c_g5⁻¹ ∈ Subgroup.closure A := by
    intro x hx
    have hxC : x ∈ C := burnsideI22P5_J2c_Sp_le_C hx
    refine Subgroup.mul_mem _ (Subgroup.subset_closure ⟨C.mul_mem (C.mul_mem hxC
      burnsideI22P5_J2c_g5_mem_C) (C.inv_mem hxC), ?_⟩)
      (Subgroup.subset_closure ⟨C.inv_mem burnsideI22P5_J2c_g5_mem_C, ?_⟩)
    · have := MulEquiv.orderOf_eq (MulAut.conj x) burnsideI22P5_J2c_g5
      rw [MulAut.conj_apply] at this
      rw [this]; exact hg5odd
    · rw [orderOf_inv]; exact hg5odd
  have hgen : ∀ i : Fin 4, incl (elt (burnsideI22P5_J2c_genN i)) ∈ Subgroup.closure A := by
    intro i
    have hex : ∃ pr ∈ burnsideI22P5_J2c_commPairs, pr.2 = burnsideI22P5_J2c_genN i := by
      revert i; decide
    obtain ⟨⟨k, κ⟩, hpr, hκ⟩ := hex
    have hκ' : burnsideI22P5_J2c_genN i = κ := hκ.symm
    rw [hκ', burnsideI22P5_J2c_comm_eq hpr]
    exact hcomm _ (incl_mem_Sp (elt k))
  have hmem : ∀ w : List (Fin 4),
      (w.map fun i => incl (elt (burnsideI22P5_J2c_genN i))).prod ∈ Subgroup.closure A := by
    intro w
    induction w with
    | nil => exact Subgroup.one_mem _
    | cons i w ih =>
      rw [List.map_cons, List.prod_cons]
      exact Subgroup.mul_mem _ (hgen i) ih
  rintro _ ⟨j, hj, rfl⟩
  have hw := burnsideI22P5_J2c_wordTable_check j hj
  have := (burnsideI22P5_J2c_evalG_spec (burnsideI22P5_J2c_wordTable.getD j [])).2
  rw [hw] at this
  rw [this]
  exact hmem _

open CFSG.ComponentClassification.J2Cover.Models CFSG.ComponentClassification.J2Cover
  CFSG.ComponentClassification.CentralCover in
theorem burnsideI22P5_J2c_one_mem : (1 : ℕ) ∈ oddWidx := by decide

open CFSG.ComponentClassification.J2Cover.Models CFSG.ComponentClassification.J2Cover
  CFSG.ComponentClassification.CentralCover in
theorem burnsideI22P5_J2c_one_sq : mulIdx 1 1 = 4 := by decide +kernel

open CFSG.ComponentClassification.J2Cover.Models CFSG.ComponentClassification.J2Cover
  CFSG.ComponentClassification.CentralCover in
theorem burnsideI22P5_J2c_w0_sq :
    (incl (elt 1)) ^ 2 = incl (elt 4) := by
  rw [sq, ← map_mul, ← (mulIdx_spec (a := 1) (by norm_num : 1 < 128)).2, burnsideI22P5_J2c_one_sq]

open CFSG.ComponentClassification.J2Cover.Models CFSG.ComponentClassification.J2Cover
  CFSG.ComponentClassification.CentralCover in
theorem burnsideI22P5_J2c_f_diag :
    ∀ i < 128, mulIdx i i = 4 → bitAt fRows i i = true :=
  burnsideI22P5_J2c_check_parts.2.2.2.2.2.2.2

open CFSG.ComponentClassification.J2Cover.Models CFSG.ComponentClassification.J2Cover
  CFSG.ComponentClassification.CentralCover in
theorem burnsideI22P5_J2c_fCoc_root
    {s : S} (hs : s * s = elt 4) : fCoc s s = 1 := by
  obtain ⟨i, hi, rfl⟩ := elt_surjective s
  have h1 := (mulIdx_spec (a := i) hi).2
  have h2 : mulIdx i i = 4 := by
    refine elt_injective (mulIdx_spec (a := i) hi).1 (by norm_num) ?_
    rw [h1, hs]
  have h3 := burnsideI22P5_J2c_f_diag i hi h2
  rw [fCoc, tbl_elt fRows hi hi, if_pos h3]

open CFSG.ComponentClassification.J2Cover.Models CFSG.ComponentClassification.J2Cover
  CFSG.ComponentClassification.CentralCover in
theorem burnsideI22P5_J2c_T_level
    {K : Type} [Group K] [Finite K]
    (hK : commutator K = ⊤)
    (π : K →* Models.P) {t : K} (hext : IsCentralDoubleExt π t)
    (u : K) (hπu : π u = incl (elt 4)) :
    (∀ y : K, π y ∈ Sp → y * u = u * y) ∧
      ∀ x y : K, π x ∈ Sp → π y ∈ Sp → x ^ 2 = u → y ^ 2 = u * t → False := by
  obtain ⟨ι, hιsnd, hιt⟩ := Lift.exists_mulEquiv_RfN hK hext
  have hu' : π u ∈ Sp := hπu ▸ incl_mem_Sp (elt 4)
  have ht' : π t ∈ Sp := by
    have : π t = 1 := by
      have : t ∈ π.ker := by rw [hext.ker_eq]; exact Subgroup.mem_zpowers t
      exact this
    rw [this]; exact Sp.one_mem
  have huR : (ι ⟨u, hu'⟩).snd = eS.symm (elt 4) :=
    Subtype.ext ((hιsnd _).trans (hπu.trans (coe_eS_symm _).symm))
  constructor
  · intro y hy
    have hc : ι ⟨u, hu'⟩ ∈ Subgroup.center RfN := by
      rw [mem_center_RfN, mem_center_Rf]
      have hy' : ι ⟨u, hu'⟩ = ⟨(ι ⟨u, hu'⟩).fst, eS.symm (elt 4)⟩ :=
        CocycleExtension.ext rfl huR
      rw [hy', rfEquiv_mk]
      rcases CFSG.ComponentClassification.CentralCover.zmod_two_cases (ι ⟨u, hu'⟩).fst with h | h
      · rw [h]; exact Or.inr (Or.inl rfl)
      · rw [h]; exact Or.inr (Or.inr (Or.inr (by
          rw [zR_mul_central])))
    have h1 := Subgroup.mem_center_iff.1 hc (ι ⟨y, hy⟩)
    have h2 : (⟨y, hy⟩ * ⟨u, hu'⟩ : Sp.comap π) = ⟨u, hu'⟩ * ⟨y, hy⟩ :=
      ι.injective (by rw [map_mul, map_mul]; exact h1)
    exact congrArg Subtype.val h2
  · intro x y hx hy hx2 hy2
    have htT : ι ⟨t, ht'⟩ = ⟨1, 1⟩ := by
      have : (⟨t, ht'⟩ : Sp.comap π) = ι.symm ⟨1, 1⟩ := Subtype.ext hιt.symm
      rw [this, MulEquiv.apply_symm_apply]
    have hsq : ∀ z : Sp.comap π, (ι z * ι z).fst = fN (ι z).snd (ι z).snd := by
      intro z
      rw [CocycleExtension.mul_fst, CFSG.ComponentClassification.CentralCover.zmod_two_add_self, zero_add]
    have hx2' : (⟨x, hx⟩ * ⟨x, hx⟩ : Sp.comap π) = ⟨u, hu'⟩ := Subtype.ext (by
      show x * x = u
      rw [← sq]; exact hx2)
    have hy2' : (⟨y, hy⟩ * ⟨y, hy⟩ : Sp.comap π) = ⟨u, hu'⟩ * ⟨t, ht'⟩ :=
      Subtype.ext (by
        show y * y = u * t
        rw [← sq]; exact hy2)
    have e1 := congrArg ι hx2'
    rw [map_mul] at e1
    have e2 := congrArg ι hy2'
    rw [map_mul, map_mul, htT] at e2
    have hfx := hsq ⟨x, hx⟩
    rw [e1] at hfx
    have hfy := hsq ⟨y, hy⟩
    rw [e2, CocycleExtension.mul_fst] at hfy
    have hxs : (ι ⟨x, hx⟩).snd * (ι ⟨x, hx⟩).snd = eS.symm (elt 4) := by
      have := congrArg CocycleExtension.snd e1
      rw [CocycleExtension.mul_snd] at this
      exact this.trans huR
    have hys : (ι ⟨y, hy⟩).snd * (ι ⟨y, hy⟩).snd = eS.symm (elt 4) := by
      have := congrArg CocycleExtension.snd e2
      rw [CocycleExtension.mul_snd, CocycleExtension.mul_snd] at this
      exact this.trans (by show (ι ⟨u, hu'⟩).snd * 1 = eS.symm (elt 4); rw [mul_one]; exact huR)
    have hxS : eS (ι ⟨x, hx⟩).snd * eS (ι ⟨x, hx⟩).snd = elt 4 := by
      rw [← map_mul, hxs, MulEquiv.apply_symm_apply]
    have hyS : eS (ι ⟨y, hy⟩).snd * eS (ι ⟨y, hy⟩).snd = elt 4 := by
      rw [← map_mul, hys, MulEquiv.apply_symm_apply]
    have hf1 : fN (ι ⟨u, hu'⟩).snd 1 = 0 := fN.map_one_right _
    have hfy' : (ι ⟨u, hu'⟩).fst + 1 + fN (ι ⟨u, hu'⟩).snd 1 =
        fN (ι ⟨y, hy⟩).snd (ι ⟨y, hy⟩).snd := hfy
    rw [hf1, fN_apply (ι ⟨y, hy⟩).snd (ι ⟨y, hy⟩).snd, burnsideI22P5_J2c_fCoc_root hyS] at hfy'
    rw [fN_apply (ι ⟨x, hx⟩).snd (ι ⟨x, hx⟩).snd, burnsideI22P5_J2c_fCoc_root hxS] at hfx
    rw [hfx] at hfy'
    revert hfy'
    decide

open CFSG.ComponentClassification.J2Cover.Models CFSG.ComponentClassification.J2Cover
  CFSG.ComponentClassification.CentralCover in
theorem burnsideI22P5_J2c_Sp_pGroup :
    IsPGroup 2 Sp :=
  IsPGroup.of_card (n := 7) (by rw [burnsideI22P5_J2c_card_Sp]; norm_num)

open CFSG.ComponentClassification.J2Cover.Models CFSG.ComponentClassification.J2Cover
  CFSG.ComponentClassification.CentralCover in
theorem burnsideI22P5_J2c_Sp_odd :
    ¬ 2 ∣ Sp.index := by
  intro hd
  have h := Sp.card_mul_index
  rw [burnsideI22P5_J2c_card_Sp, Models.card_P] at h
  have : Sp.index = 4725 := by omega
  rw [this] at hd
  exact absurd hd (by norm_num)

open CFSG.ComponentClassification.J2Cover.Models CFSG.ComponentClassification.J2Cover
  CFSG.ComponentClassification.CentralCover in
theorem burnsideI22P5_J2c_W_le_Sp :
    burnsideI22P5_J2c_W ≤ Sp := by
  rintro _ ⟨k, -, rfl⟩
  exact incl_mem_Sp (elt k)

open CFSG.ComponentClassification.J2Cover.Models CFSG.ComponentClassification.J2Cover
  CFSG.ComponentClassification.CentralCover CFSG.ASVolI.ChIJK in
theorem burnsideI22P5_J2_c
    {K : Type} [Group K] [Finite K] (hK : CFSG.IsQuasisimple K)
    (hZ : Subgroup.center K ≠ ⊥)
    (h : CFSG.Blueprint.NativeSporadic.IsSporadic (K ⧸ Subgroup.center K) .J2)
    (u : K) (hu : u ∉ Subgroup.center K) (hu2 : u ^ 2 = 1) : UniqueSquareInCoset K u := by
  classical
  obtain ⟨hZ2, ⟨e⟩⟩ := burnsideI22P5_J2_setup hK hZ h
  obtain ⟨t, ht, hZt, h11, h15⟩ := burnsideI22P5_J2_lift hK hZ2 e
  haveI : Group.IsPerfect K := hK.1
  let π : K →* Models.P := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K))
  have hπ : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : π.ker = Subgroup.zpowers t := by
    rw [← hZt]
    ext l
    simp only [π, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hext : IsCentralDoubleExt π t := ⟨hπ, hZt ▸ Subgroup.mem_zpowers t, ht, hker⟩
  have ht1 : t ≠ 1 := by
    intro h1; rw [h1, orderOf_one] at ht; exact absurd ht (by norm_num)
  have hπu1 : π u ≠ 1 := fun h1 => hu (by
    rw [hZt, ← hker]; exact h1)
  have hπu2 : (π u) ^ 2 = 1 := by rw [← map_pow, hu2, map_one]
  have hord : orderOf (π u) = 2 := orderOf_eq_prime hπu2 hπu1
  obtain ⟨hcases, hconj, -⟩ := ctss_j2_involutions
  have hfix : fixCount ((π u : Models.P) : Perm315) = 11 := by
    rcases hcases (π u) hord with h' | h'
    · exact h'
    · exfalso
      have := (h15 u hord h').1
      rw [hu2] at this
      exact ht1 this.symm
  have hord4 : orderOf (incl (elt 4)) = 2 := by
    rw [orderOf_injective incl (fun a b hab => Subtype.ext (by simpa using congrArg Subtype.val hab))
      (elt 4)]
    exact orderOf_elt_four
  obtain ⟨g, hg⟩ := hconj (π u) (incl (elt 4)) hord hord4 (by
    rw [hfix, incl_coe]; exact fixCount_elt_four.symm)
  obtain ⟨a, ha⟩ := hπ g
  have hπu' : π (a * u * a⁻¹) = incl (elt 4) := by
    rw [map_mul, map_mul, map_inv, ha]; exact hg
  suffices H : UniqueSquareInCoset K (a * u * a⁻¹) by
    have := burnsideI22P5_unique_square_conj a⁻¹ (a * u * a⁻¹) H
    simpa [mul_assoc] using this
  obtain ⟨hTu, hU⟩ := burnsideI22P5_J2c_T_level hK.1.commutator_eq_top π hext (a * u * a⁻¹) hπu'
  refine burnsideI22P5_unique_square_of_data π hπ ht hZt hker (a * u * a⁻¹) Sp
    burnsideI22P5_J2c_Sp_pGroup burnsideI22P5_J2c_Sp_odd hTu burnsideI22P5_J2c_W
    (burnsideI22P5_J2c_Sp_pGroup.to_le burnsideI22P5_J2c_W_le_Sp)
    ?_ ?_ (incl (elt 1)) (burnsideI22P5_J2c_mem_W burnsideI22P5_J2c_one_mem) ?_ ∅
    (fun g hg => absurd hg (Set.notMem_empty g)) ?_
  · rw [hπu']; exact burnsideI22P5_J2c_Wn
  · rw [hπu']; exact burnsideI22P5_J2c_Wodd
  · rw [hπu']; exact burnsideI22P5_J2c_w0_sq
  · intro x y hx hy _ _ hx2 hy2
    exact hU x y hx hy hx2 hy2

open CFSG.EvenSporadicStandard.TwoHS CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native in
theorem burnsideI22P5_HSc_letters : (∀ l ∈ harCW3, 1 ≤ l ∧ l ≤ 6) ∧ (∀ l ∈ harCW5, 1 ≤ l ∧ l ≤ 6) ∧
    (∀ l ∈ harCWit, 1 ≤ l ∧ l ≤ 6) ∧
    (∀ p ∈ harCQPairs, ∀ l ∈ p.1, 1 ≤ l ∧ l ≤ 3) ∧ (∀ l ∈ harCRoot, 1 ≤ l ∧ l ≤ 3) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide

open CFSG.EvenSporadicStandard.TwoHS CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native in
theorem burnsideI22P5_HSc_rep_word
    {K : Type} [Group K] (M : CoverMaps K) {w : List ℕ}
    (hw : ∀ l ∈ w, 1 ≤ l ∧ l ≤ 6) :
    Rep 11200 (wordTbl 11200 harYs w) (M.ρ (wordVal M.gE w)) := by
  have hr := rep_wordTbl'' (n := 11200) (by norm_num) harYs_perm w (by
    rw [harYs_length]
    exact hw)
  rw [map_wordVal, M.rho_gE]
  exact hr

open CFSG.EvenSporadicStandard.TwoHS CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native in
theorem burnsideI22P5_HSc_ok1 :
    harCOK1 () = true := by
  have h := Certificates.certificate7291
  simp only [harCOK, Bool.and_eq_true] at h
  exact h.1.1

open CFSG.EvenSporadicStandard.TwoHS CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native in
theorem burnsideI22P5_HSc_ok2 :
    harCOK2 () = true := by
  have h := Certificates.certificate7291
  simp only [harCOK, Bool.and_eq_true] at h
  exact h.1.2

open CFSG.EvenSporadicStandard.TwoHS CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native in
theorem burnsideI22P5_HSc_ok3 :
    harCOK3 () = true := by
  have h := Certificates.certificate7291
  simp only [harCOK, Bool.and_eq_true] at h
  exact h.2

open CFSG.EvenSporadicStandard.TwoHS CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native in
theorem burnsideI22P5_HSc_ok1_parts :
    tblEq 11200 (compT 11200 (compT 11200 (harCG3 ()) (harCG3 ())) (harCG3 ())) (idT 11200) = true ∧
    (!tblEq 11200 (harCG3 ()) (idT 11200)) = true ∧
    tblEq 11200 (compT 11200 (compT 11200 (compT 11200 (compT 11200 (harCG5 ()) (harCG5 ()))
      (harCG5 ())) (harCG5 ())) (harCG5 ())) (idT 11200) = true ∧
    (!tblEq 11200 (harCG5 ()) (idT 11200)) = true ∧
    commTT 11200 (harCG3 ()) harZ1 = true ∧ commTT 11200 (harCG5 ()) harZ1 = true ∧
    commTT 11200 (harCGW ()) harZ1 = true ∧
    ((harCGens ()).all fun g => permOK 11200 g && invOK 11200 g (invT 11200 g)) = true ∧
    permOK 11200 (harCGW ()) = true ∧
    invOK 11200 (harCGW ()) (invT 11200 (harCGW ())) = true := by
  have h := burnsideI22P5_HSc_ok1
  simp only [harCOK1, Bool.and_eq_true, and_assoc] at h
  exact h

open CFSG.EvenSporadicStandard.TwoHS CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native in
theorem burnsideI22P5_HSc_ok2_parts :
    ((harCQ ()).all (permOK 11200)) = true ∧ enumOK 11200 400 128 (harCQ ()) = true ∧
    normOK 11200 400 (harCQ ()) (harCGens ()) = true ∧
    memT 11200 (mulClosureH 11200 (harCQ ()).toArray 400).1 (tU harCRoot) = true ∧
    tblEq 11200 (compT 11200 (tU harCRoot) (tU harCRoot)) harZ1 = true := by
  have h := burnsideI22P5_HSc_ok2
  simp only [harCOK2, Bool.and_eq_true, and_assoc] at h
  exact h

open CFSG.EvenSporadicStandard.TwoHS CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native in
theorem burnsideI22P5_HSc_ok3_parts :
    enumOK 11200 2000 1024 harU = true ∧
    ((mulClosureH 11200 harU.toArray 2000).1.all fun y =>
      !tblEq 11200 (compT 11200 y y) harZ2 ||
        !memT 11200 (mulClosureH 11200 harU.toArray 2000).1
          (conjT 11200 (harCGW ()) (invT 11200 (harCGW ())) y)) = true := by
  have h := burnsideI22P5_HSc_ok3
  simp only [harCOK3, Bool.and_eq_true] at h
  exact h

open CFSG.EvenSporadicStandard.TwoHS CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native in
@[expose] def burnsideI22P5_HSc_g3 {K : Type} [Group K] (M : CoverMaps K) : K := wordVal M.gE harCW3

open CFSG.EvenSporadicStandard.TwoHS CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native in
@[expose] def burnsideI22P5_HSc_g5 {K : Type} [Group K] (M : CoverMaps K) : K := wordVal M.gE harCW5

open CFSG.EvenSporadicStandard.TwoHS CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native in
@[expose] def burnsideI22P5_HSc_c {K : Type} [Group K] (M : CoverMaps K) : K := wordVal M.gE harCWit

open CFSG.EvenSporadicStandard.TwoHS CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native in
@[expose] def burnsideI22P5_HSc_x0 {K : Type} [Group K] (M : CoverMaps K) : K :=
  wordVal M.uE harCRoot

open CFSG.EvenSporadicStandard.TwoHS CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native in
@[expose] def burnsideI22P5_HSc_qgens {K : Type} [Group K] (M : CoverMaps K) : List K :=
  harCQPairs.map fun p =>
    wordVal M.uE p.1 * (if p.2 then burnsideI22P5_HSc_g3 M else burnsideI22P5_HSc_g5 M) *
      (wordVal M.uE p.1)⁻¹ * (if p.2 then burnsideI22P5_HSc_g3 M else burnsideI22P5_HSc_g5 M)⁻¹

open CFSG.EvenSporadicStandard.TwoHS CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native in
@[expose] def burnsideI22P5_HSc_Q {K : Type} [Group K] (M : CoverMaps K) : Subgroup K :=
  Subgroup.closure {x | x ∈ burnsideI22P5_HSc_qgens M}

open CFSG.EvenSporadicStandard.TwoHS CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native in
theorem burnsideI22P5_HSc_rep_g3
    {K : Type} [Group K] (M : CoverMaps K) :
    Rep 11200 (harCG3 ()) (M.ρ (burnsideI22P5_HSc_g3 M)) :=
  burnsideI22P5_HSc_rep_word M burnsideI22P5_HSc_letters.1

open CFSG.EvenSporadicStandard.TwoHS CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native in
theorem burnsideI22P5_HSc_rep_g5
    {K : Type} [Group K] (M : CoverMaps K) :
    Rep 11200 (harCG5 ()) (M.ρ (burnsideI22P5_HSc_g5 M)) :=
  burnsideI22P5_HSc_rep_word M burnsideI22P5_HSc_letters.2.1

open CFSG.EvenSporadicStandard.TwoHS CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native in
theorem burnsideI22P5_HSc_rep_c
    {K : Type} [Group K] (M : CoverMaps K) :
    Rep 11200 (harCGW ()) (M.ρ (burnsideI22P5_HSc_c M)) :=
  burnsideI22P5_HSc_rep_word M burnsideI22P5_HSc_letters.2.2.1

open CFSG.EvenSporadicStandard.TwoHS CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native in
theorem burnsideI22P5_HSc_rep_x0
    {K : Type} [Group K] (M : CoverMaps K) :
    Rep 11200 (tU harCRoot) (M.ρ (burnsideI22P5_HSc_x0 M)) :=
  M.rep_tU harCRoot burnsideI22P5_HSc_letters.2.2.2.2

open CFSG.EvenSporadicStandard.TwoHS CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native in
theorem burnsideI22P5_HSc_rep_qgen
    {K : Type} [Group K] (M : CoverMaps K) {p : List ℕ × Bool}
    (hp : p ∈ harCQPairs) :
    Rep 11200 (tComm 11200 (tU p.1) (if p.2 then harCG3 () else harCG5 ()))
      (M.ρ (wordVal M.uE p.1 * (if p.2 then burnsideI22P5_HSc_g3 M else burnsideI22P5_HSc_g5 M) *
        (wordVal M.uE p.1)⁻¹ *
          (if p.2 then burnsideI22P5_HSc_g3 M else burnsideI22P5_HSc_g5 M)⁻¹)) := by
  have h1 := M.rep_tU p.1 (burnsideI22P5_HSc_letters.2.2.2.1 p hp)
  have h2 : Rep 11200 (if p.2 then harCG3 () else harCG5 ())
      (M.ρ (if p.2 then burnsideI22P5_HSc_g3 M else burnsideI22P5_HSc_g5 M)) := by
    cases p.2
    · exact burnsideI22P5_HSc_rep_g5 M
    · exact burnsideI22P5_HSc_rep_g3 M
  have h := rep_tComm hn11200 h1 h2
  rw [commutatorElement_def] at h
  simpa only [map_mul, map_inv] using h

open CFSG.EvenSporadicStandard.TwoHS CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native in
theorem burnsideI22P5_HSc_map_Q
    {K : Type} [Group K] (M : CoverMaps K)
    (hperm : ∀ T ∈ harCQ (), permOK 11200 T = true) :
    (burnsideI22P5_HSc_Q M).map M.ρ = genOf 11200 (harCQ ()) := by
  unfold burnsideI22P5_HSc_Q genOf
  rw [MonoidHom.map_closure]
  congr 1
  ext z
  simp only [Set.mem_image, Set.mem_setOf_eq, List.mem_toArray]
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
    have hT : tComm 11200 (tU p.1) (if p.2 then harCG3 () else harCG5 ()) ∈ harCQ () :=
      List.mem_map.2 ⟨p, hp, rfl⟩
    exact ⟨_, hT, rep_unique (rep_tp (hperm _ hT)) (burnsideI22P5_HSc_rep_qgen M hp)⟩
  · rintro ⟨T, hT, rfl⟩
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hT
    exact ⟨_, List.mem_map.2 ⟨p, hp, rfl⟩,
      (rep_unique (rep_tp (hperm _ hT)) (burnsideI22P5_HSc_rep_qgen M hp)).symm⟩

open CFSG.EvenSporadicStandard.TwoHS CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native in
theorem burnsideI22P5_HSc_commute {K : Type} [Group K] (M : CoverModel K) {a b : K} {A B : Table}
    (ha : Rep 11200 A (M.ρ a)) (hb : Rep 11200 B (M.ρ b)) (h : commTT 11200 A B = true) :
    a * b = b * a :=
  M.ρ_inj (by rw [map_mul, map_mul]; exact (commTT_iff ha hb).1 h)

open CFSG.EvenSporadicStandard.TwoHS CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native in
theorem burnsideI22P5_HSc_pow3 {K : Type} [Group K] (M : CoverModel K) {a : K} {A : Table}
    (hA : Rep 11200 A (M.ρ a))
    (h : tblEq 11200 (compT 11200 (compT 11200 A A) A) (idT 11200) = true) : a ^ 3 = 1 := by
  apply M.ρ_inj
  have h1 := (tblEq_idT_iff hn11200 (Rep.compT (Rep.compT hA hA) hA)).1 h
  rw [map_pow, map_one, pow_succ, pow_two]
  exact h1

open CFSG.EvenSporadicStandard.TwoHS CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native in
theorem burnsideI22P5_HSc_pow5 {K : Type} [Group K] (M : CoverModel K) {a : K} {A : Table}
    (hA : Rep 11200 A (M.ρ a))
    (h : tblEq 11200 (compT 11200 (compT 11200 (compT 11200 (compT 11200 A A) A) A) A)
      (idT 11200) = true) : a ^ 5 = 1 := by
  apply M.ρ_inj
  have h1 := (tblEq_idT_iff hn11200
    (Rep.compT (Rep.compT (Rep.compT (Rep.compT hA hA) hA) hA) hA)).1 h
  rw [map_pow, map_one, pow_succ, pow_succ, pow_succ, pow_two]
  exact h1

open CFSG.EvenSporadicStandard.TwoHS CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native in
theorem burnsideI22P5_HSc_ne_one {K : Type} [Group K] (M : CoverModel K) {a : K} {A : Table}
    (hA : Rep 11200 A (M.ρ a)) (h : (!tblEq 11200 A (idT 11200)) = true) : a ≠ 1 := by
  intro ha
  have : tblEq 11200 A (idT 11200) = true := (tblEq_idT_iff hn11200 hA).2 (by rw [ha, map_one])
  rw [this] at h
  exact Bool.false_ne_true h

open CFSG.EvenSporadicStandard.TwoHS CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native in
theorem burnsideI22P5_HSc_memT_of_rep {L : Array Table} {x : Table} {g : Equiv.Perm (Fin 11200)}
    (hx : Rep 11200 x g) {k : ℕ} (hk : k < L.size) (hL : Rep 11200 L[k]! g) :
    memT 11200 L x = true := by
  rw [memT, Array.any_eq_true]
  refine ⟨k, hk, ?_⟩
  rw [getElem!_pos L k hk] at hL
  exact (tblEq_iff_eq hx hL).2 rfl

open CFSG.EvenSporadicStandard.TwoHS CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native in
theorem burnsideI22P5_HSc_g3_facts
    {K : Type} [Group K] (M : CoverModel K) :
    orderOf (burnsideI22P5_HSc_g3 M.toCoverMaps) = 3 ∧
      burnsideI22P5_HSc_g3 M.toCoverMaps * M.z1E = M.z1E * burnsideI22P5_HSc_g3 M.toCoverMaps := by
  obtain ⟨h1, h2, -, -, h5, -⟩ := burnsideI22P5_HSc_ok1_parts
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  exact ⟨orderOf_eq_prime (burnsideI22P5_HSc_pow3 M (burnsideI22P5_HSc_rep_g3 M.toCoverMaps) h1)
    (burnsideI22P5_HSc_ne_one M (burnsideI22P5_HSc_rep_g3 M.toCoverMaps) h2),
    burnsideI22P5_HSc_commute M (burnsideI22P5_HSc_rep_g3 M.toCoverMaps) M.rep_z1E h5⟩

open CFSG.EvenSporadicStandard.TwoHS CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native in
theorem burnsideI22P5_HSc_g5_facts
    {K : Type} [Group K] (M : CoverModel K) :
    orderOf (burnsideI22P5_HSc_g5 M.toCoverMaps) = 5 ∧
      burnsideI22P5_HSc_g5 M.toCoverMaps * M.z1E = M.z1E * burnsideI22P5_HSc_g5 M.toCoverMaps := by
  obtain ⟨-, -, h3, h4, -, h6, -⟩ := burnsideI22P5_HSc_ok1_parts
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  exact ⟨orderOf_eq_prime (burnsideI22P5_HSc_pow5 M (burnsideI22P5_HSc_rep_g5 M.toCoverMaps) h3)
    (burnsideI22P5_HSc_ne_one M (burnsideI22P5_HSc_rep_g5 M.toCoverMaps) h4),
    burnsideI22P5_HSc_commute M (burnsideI22P5_HSc_rep_g5 M.toCoverMaps) M.rep_z1E h6⟩

open CFSG.EvenSporadicStandard.TwoHS CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native in
theorem burnsideI22P5_HSc_c_comm
    {K : Type} [Group K] (M : CoverModel K) :
    burnsideI22P5_HSc_c M.toCoverMaps * M.z1E = M.z1E * burnsideI22P5_HSc_c M.toCoverMaps := by
  obtain ⟨-, -, -, -, -, -, h7, -⟩ := burnsideI22P5_HSc_ok1_parts
  exact burnsideI22P5_HSc_commute M (burnsideI22P5_HSc_rep_c M.toCoverMaps) M.rep_z1E h7

open CFSG.EvenSporadicStandard.TwoHS CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native in
theorem burnsideI22P5_HSc_perm_Q :
    ∀ T ∈ harCQ (), permOK 11200 T = true :=
  List.all_eq_true.1 burnsideI22P5_HSc_ok2_parts.1

open CFSG.EvenSporadicStandard.TwoHS CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native in
theorem burnsideI22P5_HSc_card_Q
    {K : Type} [Group K] (M : CoverModel K) :
    Nat.card (burnsideI22P5_HSc_Q M.toCoverMaps) = 128 := by
  obtain ⟨-, he, -⟩ := burnsideI22P5_HSc_ok2_parts
  rw [← Subgroup.card_map_of_injective M.ρ_inj,
    burnsideI22P5_HSc_map_Q M.toCoverMaps burnsideI22P5_HSc_perm_Q]
  exact (enumOK_spec hn11200 burnsideI22P5_HSc_perm_Q he).1

open CFSG.EvenSporadicStandard.TwoHS CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native in
theorem burnsideI22P5_HSc_Q_isPGroup
    {K : Type} [Group K] (M : CoverModel K) :
    IsPGroup 2 (burnsideI22P5_HSc_Q M.toCoverMaps) :=
  IsPGroup.of_card (n := 7) (by rw [burnsideI22P5_HSc_card_Q M]; norm_num)

open CFSG.EvenSporadicStandard.TwoHS CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native in
theorem burnsideI22P5_HSc_normalizes
    {K : Type} [Group K] (M : CoverModel K) {k : K}
    (hk : M.ρ k ∈ genOf 11200 (harCGens ())) :
    k ∈ Subgroup.normalizer ((burnsideI22P5_HSc_Q M.toCoverMaps : Subgroup K) : Set K) := by
  obtain ⟨-, he, hn, -⟩ := burnsideI22P5_HSc_ok2_parts
  obtain ⟨-, -, -, -, -, -, -, hc, -⟩ := burnsideI22P5_HSc_ok1_parts
  have hcs : ∀ c ∈ harCGens (), permOK 11200 c = true ∧ invOK 11200 c (invT 11200 c) = true := by
    intro c hc'
    have := List.all_eq_true.1 hc c hc'
    simpa only [Bool.and_eq_true] using this
  have hmem := normOK_spec hn11200 burnsideI22P5_HSc_perm_Q he hcs hn hk
  rw [Subgroup.mem_normalizer_iff] at hmem ⊢
  intro h
  have h1 := hmem (M.ρ h)
  have e : ∀ x : K, x ∈ burnsideI22P5_HSc_Q M.toCoverMaps ↔
      M.ρ x ∈ genOf 11200 (harCQ ()) := by
    intro x
    rw [← burnsideI22P5_HSc_map_Q M.toCoverMaps burnsideI22P5_HSc_perm_Q]
    exact (Subgroup.mem_map_iff_mem M.ρ_inj).symm
  rw [e h, e (k * h * k⁻¹), map_mul, map_mul, map_inv]
  exact h1

open CFSG.EvenSporadicStandard.TwoHS CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native in
theorem burnsideI22P5_HSc_x0_mem
    {K : Type} [Group K] (M : CoverModel K) :
    burnsideI22P5_HSc_x0 M.toCoverMaps ∈ burnsideI22P5_HSc_Q M.toCoverMaps := by
  obtain ⟨-, he, -, hm, -⟩ := burnsideI22P5_HSc_ok2_parts
  rw [← Subgroup.mem_map_iff_mem M.ρ_inj,
    burnsideI22P5_HSc_map_Q M.toCoverMaps burnsideI22P5_HSc_perm_Q]
  exact mem_genOf_of_memT hn11200 burnsideI22P5_HSc_perm_Q he
    (burnsideI22P5_HSc_rep_x0 M.toCoverMaps) hm

open CFSG.EvenSporadicStandard.TwoHS CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native in
theorem burnsideI22P5_HSc_x0_sq
    {K : Type} [Group K] (M : CoverModel K) :
    burnsideI22P5_HSc_x0 M.toCoverMaps ^ 2 = M.z1E := by
  obtain ⟨-, -, -, -, hs⟩ := burnsideI22P5_HSc_ok2_parts
  apply M.ρ_inj
  have h1 := Rep.compT (burnsideI22P5_HSc_rep_x0 M.toCoverMaps)
    (burnsideI22P5_HSc_rep_x0 M.toCoverMaps)
  rw [map_pow, pow_two]
  exact (tblEq_iff_eq h1 M.rep_z1E).1 hs

open CFSG.EvenSporadicStandard.TwoHS CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native in
theorem burnsideI22P5_HSc_L
    {K : Type} [Group K] (M : CoverModel K) {y : K} (hy : y ∈ M.T0)
    (hy2 : y ^ 2 = M.tE * M.z1E)
    (hcy : burnsideI22P5_HSc_c M.toCoverMaps * y * (burnsideI22P5_HSc_c M.toCoverMaps)⁻¹ ∈ M.T0) :
    False := by
  obtain ⟨henum, hall⟩ := burnsideI22P5_HSc_ok3_parts
  obtain ⟨-, -, -, -, -, -, -, -, -, hcinv⟩ := burnsideI22P5_HSc_ok1_parts
  obtain ⟨-, -, hcov, -⟩ := enumOK_spec hn11200 harU_perm henum
  have hT0 : ∀ x ∈ M.T0, ∃ k < (mulClosureH 11200 harU.toArray 2000).1.size,
      Rep 11200 (mulClosureH 11200 harU.toArray 2000).1[k]! (M.ρ x) := by
    intro x hx
    have h1 := Subgroup.mem_map_of_mem M.ρ hx
    rw [M.map_T0] at h1
    exact hcov _ h1
  obtain ⟨k, hk, hkrep⟩ := hT0 y hy
  have hc := burnsideI22P5_HSc_rep_c M.toCoverMaps
  have hconj := rep_conjT hc (rep_invT hc hcinv) hkrep
  obtain ⟨k', hk', hk'rep⟩ := hT0 _ hcy
  have hmem : memT 11200 (mulClosureH 11200 harU.toArray 2000).1
      (conjT 11200 (harCGW ()) (invT 11200 (harCGW ())) (mulClosureH 11200 harU.toArray 2000).1[k]!)
        = true := by
    refine burnsideI22P5_HSc_memT_of_rep (g := M.ρ (burnsideI22P5_HSc_c M.toCoverMaps * y *
      (burnsideI22P5_HSc_c M.toCoverMaps)⁻¹)) ?_ hk' hk'rep
    rw [map_mul, map_mul, map_inv]
    exact hconj
  have hz2 : Rep 11200 harZ2 (M.ρ (M.tE * M.z1E)) := by
    rw [map_mul]
    exact Rep.compT M.rep_tE M.rep_z1E
  have hsq : tblEq 11200 (compT 11200 (mulClosureH 11200 harU.toArray 2000).1[k]!
      (mulClosureH 11200 harU.toArray 2000).1[k]!) harZ2 = true := by
    refine (tblEq_iff_eq (Rep.compT hkrep hkrep) hz2).2 ?_
    rw [← map_mul, ← pow_two, hy2]
  have h := Array.all_eq_true.1 hall k hk
  rw [← getElem!_pos (mulClosureH 11200 harU.toArray 2000).1 k hk] at h
  rw [hsq, hmem] at h
  exact absurd h (by decide)

open CFSG.EvenSporadicStandard.TwoHS CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native in
theorem burnsideI22P5_closure_eq_of_card {X : Type} [Group X] [Finite X] (C S : Subgroup X)
    (a b : X) (hC : Nat.card C = 7680) (hS : Nat.card S = 512) (hSC : S ≤ C) (haC : a ∈ C)
    (hbC : b ∈ C) (ha : orderOf a = 3) (hb : orderOf b = 5) :
    Subgroup.closure ((S : Set X) ∪ {a, b}) = C := by
  set D := Subgroup.closure ((S : Set X) ∪ {a, b}) with hD
  have hDC : D ≤ C := by
    rw [hD, Subgroup.closure_le]
    rintro x (hx | hx | hx)
    · exact hSC hx
    · rw [Set.mem_singleton_iff.1 hx]; exact haC
    · rw [Set.mem_singleton_iff.1 hx]; exact hbC
  have hSD : S ≤ D := fun x hx => Subgroup.subset_closure (Or.inl hx)
  have haD : a ∈ D := Subgroup.subset_closure (Or.inr (Or.inl rfl))
  have hbD : b ∈ D := Subgroup.subset_closure (Or.inr (Or.inr rfl))
  have h1 : 512 ∣ Nat.card D := hS ▸ Subgroup.card_dvd_of_le hSD
  have h2 : 3 ∣ Nat.card D := by
    have := orderOf_dvd_natCard (⟨a, haD⟩ : D)
    rwa [Subgroup.orderOf_mk, ha] at this
  have h3 : 5 ∣ Nat.card D := by
    have := orderOf_dvd_natCard (⟨b, hbD⟩ : D)
    rwa [Subgroup.orderOf_mk, hb] at this
  have h4 : 7680 ∣ Nat.card D := by
    have h12 : 512 * 3 ∣ Nat.card D := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h1 h2
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime (512 * 3) 5) h12 h3
  have h5 : Nat.card D ∣ 7680 := hC ▸ Subgroup.card_dvd_of_le hDC
  have h6 : Nat.card D = 7680 := Nat.dvd_antisymm h5 h4
  exact Subgroup.eq_of_le_of_card_ge hDC (by rw [hC, h6])

open CFSG.EvenSporadicStandard.TwoHS CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native in
theorem burnsideI22P5_odd_conj_mem {X : Type} [Group X] (C : Subgroup X) {s a : X} (hs : s ∈ C)
    (ha : a ∈ C) (hodd : Odd (orderOf a)) :
    s * a * s⁻¹ ∈ {x : X | x ∈ C ∧ Odd (orderOf x)} := by
  refine ⟨C.mul_mem (C.mul_mem hs ha) (C.inv_mem hs), ?_⟩
  have h := orderOf_injective (MulAut.conj s).toMonoidHom (MulAut.conj s).injective a
  have h' : orderOf (s * a * s⁻¹) = orderOf a := h
  rw [h']
  exact hodd

open CFSG.EvenSporadicStandard.TwoHS CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native in
theorem burnsideI22P5_map_mem_normalizer {K X : Type} [Group K] [Group X] (π : K →* X)
    (Q : Subgroup K) {k : K} (hk : k ∈ Subgroup.normalizer (Q : Set K)) :
    π k ∈ Subgroup.normalizer ((Q.map π : Subgroup X) : Set X) := by
  have hk' : k⁻¹ ∈ Subgroup.normalizer (Q : Set K) := (Subgroup.normalizer _).inv_mem hk
  rw [Subgroup.mem_normalizer_iff] at hk hk' ⊢
  intro w
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact ⟨k * q * k⁻¹, (hk q).1 hq, by rw [map_mul, map_mul, map_inv]⟩
  · rintro ⟨q, hq, hqw⟩
    refine ⟨k⁻¹ * q * k, ?_, ?_⟩
    · have := (hk' q).1 hq
      simpa using this
    · rw [map_mul, map_mul, map_inv, hqw]
      group

open CFSG.EvenSporadicStandard.TwoHS CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native in
theorem burnsideI22P5_orderOf_map_prime {K X : Type} [Group K] [Group X] (π : K →* X) {t : K}
    (ht : orderOf t = 2) (hker : π.ker = Subgroup.zpowers t) {p : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) {g : K} (hg : orderOf g = p) : orderOf (π g) = p := by
  have hdvd : orderOf (π g) ∣ p := hg ▸ orderOf_map_dvd π g
  rcases (Nat.dvd_prime hp.out).1 hdvd with h1 | h1
  · exfalso
    have h2 : π g = 1 := orderOf_eq_one_iff.1 h1
    have h3 : g ∈ Subgroup.zpowers t := by rw [← hker]; exact h2
    rcases burnsideI22P5_mem_zpowers_two ht h3 with h | h
    · rw [h, orderOf_one] at hg
      exact hp.out.one_lt.ne hg
    · rw [h, ht] at hg
      exact hp2 hg.symm
  · exact h1

open CFSG.EvenSporadicStandard.TwoHS CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native in
theorem burnsideI22P5_comm_mem_closure {K X : Type} [Group K] [Group X] (π : K →* X)
    (C : Subgroup X) {a g : K} (ha : π a ∈ C) (hg : π g ∈ C) (hodd : Odd (orderOf (π g))) :
    π (a * g * a⁻¹ * g⁻¹) ∈ Subgroup.closure {x : X | x ∈ C ∧ Odd (orderOf x)} := by
  rw [map_mul, map_mul, map_mul, map_inv, map_inv]
  exact Subgroup.mul_mem _ (Subgroup.subset_closure (burnsideI22P5_odd_conj_mem C ha hg hodd))
    (Subgroup.inv_mem _ (Subgroup.subset_closure ⟨hg, hodd⟩))

open CFSG.EvenSporadicStandard.TwoHS CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native in
theorem burnsideI22P5_HSc_rho_mem_gens
    {K : Type} [Group K] (M : CoverModel K) :
    (∀ y ∈ M.T0, M.ρ y ∈ genOf 11200 (harCGens ())) ∧
    M.ρ (burnsideI22P5_HSc_g3 M.toCoverMaps) ∈ genOf 11200 (harCGens ()) ∧
    M.ρ (burnsideI22P5_HSc_g5 M.toCoverMaps) ∈ genOf 11200 (harCGens ()) := by
  obtain ⟨-, -, -, -, -, -, -, hc, -⟩ := burnsideI22P5_HSc_ok1_parts
  have hperm : ∀ g ∈ harCGens (), permOK 11200 g = true := by
    intro g hg'
    have := List.all_eq_true.1 hc g hg'
    exact (Bool.and_eq_true_iff.1 this).1
  refine ⟨?_, ?_, ?_⟩
  · intro y hy
    have h1 := Subgroup.mem_map_of_mem M.ρ hy
    rw [M.map_T0] at h1
    refine (Subgroup.closure_mono ?_) h1
    rintro _ ⟨T, hT, rfl⟩
    refine ⟨T, ?_, rfl⟩
    simp only [List.mem_toArray] at hT ⊢
    exact List.mem_append_left _ hT
  · have hmem : harCG3 () ∈ harCGens () := by simp [harCGens]
    rw [rep_unique (burnsideI22P5_HSc_rep_g3 M.toCoverMaps) (rep_tp (hperm _ hmem))]
    exact tp_mem_genOf hmem
  · have hmem : harCG5 () ∈ harCGens () := by simp [harCGens]
    rw [rep_unique (burnsideI22P5_HSc_rep_g5 M.toCoverMaps) (rep_tp (hperm _ hmem))]
    exact tp_mem_genOf hmem

open CFSG.EvenSporadicStandard.TwoHS CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native CFSG.ASVolI.ChIJK in
theorem burnsideI22P5_HS_c_z1
    {K : Type} [Group K] [Finite K] (hperf : Group.IsPerfect K)
    (hZ : Nat.card (Subgroup.center K) = 2)
    (hq : CFSG.Blueprint.NativeSporadic.IsSporadic (K ⧸ Subgroup.center K) .HS)
    (M : CoverModel K) : UniqueSquareInCoset K M.z1E := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ht : orderOf M.tE = 2 := orderOf_eq_prime M.tE_sq M.tE_ne_one
  have hZt : Subgroup.center K = Subgroup.zpowers M.tE := by
    ext x
    rw [M.mem_center_iff hZ]
    constructor
    · rintro (rfl | rfl)
      · exact one_mem _
      · exact Subgroup.mem_zpowers _
    · intro hx
      exact burnsideI22P5_mem_zpowers_two ht hx
  have hker : M.π.ker = Subgroup.zpowers M.tE := by rw [M.ker_pi_eq, hZt]
  haveI : Finite ↥CFSG.Sporadic.Schreier.hsP := Finite.of_surjective M.π M.π_surj
  set S : Subgroup ↥CFSG.Sporadic.Schreier.hsP := M.T0.map M.π with hS
  have hmemT : ∀ y : K, M.π y ∈ S → y ∈ M.T0 := by
    intro y hy
    obtain ⟨y₀, hy₀, hyy⟩ := hy
    rcases burnsideI22P5_eq_or_mul M.π ht hker hyy with h | h
    · rw [h]; exact hy₀
    · rw [h]; exact M.T0.mul_mem hy₀ M.tE_mem_T0
  have hS2 : IsPGroup 2 S := M.isPGroup_T0.map M.π
  have hScard : Nat.card S = 512 := M.card_map_pi_T0 hZ
  have hSodd : ¬ 2 ∣ S.index := by
    have h := Subgroup.card_mul_index S
    rw [hScard, CFSG.Sporadic.Schreier.card_hsP] at h
    intro hd
    omega
  have hTu : ∀ y : K, M.π y ∈ S → y * M.z1E = M.z1E * y := fun y hy =>
    (M.z1E_comm y (hmemT y hy)).symm
  set C : Subgroup ↥CFSG.Sporadic.Schreier.hsP :=
    Subgroup.centralizer ({M.π M.z1E} : Set ↥CFSG.Sporadic.Schreier.hsP) with hC
  have hπz1 : M.π M.z1E ≠ 1 := by
    intro h
    rcases (M.mem_center_iff hZ).1 ((M.π_ker _).1 h) with h1 | h1
    · exact M.z1E_ne_one h1
    · exact M.z1E_ne_tE h1
  have hCcard : Nat.card C = 7680 :=
    CFSG.EvenSporadicStandard.HSStd.Zassenhaus.card_centralizer_eq_of_sq_eq_one hperf hZ hq M.π
      M.π_surj M.ker_pi_eq M.z1E_sq hπz1
  have hmemC : ∀ y : K, y * M.z1E = M.z1E * y → M.π y ∈ C := fun y hy => by
    rw [hC, Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hy]
  have hSC : S ≤ C := by
    rintro _ ⟨y, hy, rfl⟩
    exact hmemC y (M.z1E_comm y hy).symm
  set g3 := burnsideI22P5_HSc_g3 M.toCoverMaps with hg3
  set g5 := burnsideI22P5_HSc_g5 M.toCoverMaps with hg5
  obtain ⟨hg3o, hg3c⟩ := burnsideI22P5_HSc_g3_facts M
  obtain ⟨hg5o, hg5c⟩ := burnsideI22P5_HSc_g5_facts M
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hπg3 : orderOf (M.π g3) = 3 :=
    burnsideI22P5_orderOf_map_prime M.π ht hker (by norm_num) hg3o
  have hπg5 : orderOf (M.π g5) = 5 :=
    burnsideI22P5_orderOf_map_prime M.π ht hker (by norm_num) hg5o
  have hg3C : M.π g3 ∈ C := hmemC g3 hg3c
  have hg5C : M.π g5 ∈ C := hmemC g5 hg5c
  have hclos : Subgroup.closure ((S : Set ↥CFSG.Sporadic.Schreier.hsP) ∪ {M.π g3, M.π g5}) = C :=
    burnsideI22P5_closure_eq_of_card C S _ _ hCcard hScard hSC hg3C hg5C hπg3 hπg5
  set Qh := burnsideI22P5_HSc_Q M.toCoverMaps with hQh
  set W : Subgroup ↥CFSG.Sporadic.Schreier.hsP := Qh.map M.π with hW
  have hW2 : IsPGroup 2 W := (burnsideI22P5_HSc_Q_isPGroup M).map M.π
  obtain ⟨hρT, hρ3, hρ5⟩ := burnsideI22P5_HSc_rho_mem_gens M
  have hWn : ∀ c ∈ C, ∀ w ∈ W, c * w * c⁻¹ ∈ W := by
    intro c hc w hw
    have hD : C ≤ Subgroup.normalizer (W : Set ↥CFSG.Sporadic.Schreier.hsP) := by
      rw [← hclos, Subgroup.closure_le]
      rintro x (hx | hx | hx)
      · obtain ⟨y, hy, rfl⟩ := hx
        exact burnsideI22P5_map_mem_normalizer M.π Qh (burnsideI22P5_HSc_normalizes M (hρT y hy))
      · rw [Set.mem_singleton_iff.1 hx]
        exact burnsideI22P5_map_mem_normalizer M.π Qh (burnsideI22P5_HSc_normalizes M hρ3)
      · rw [Set.mem_singleton_iff.1 hx]
        exact burnsideI22P5_map_mem_normalizer M.π Qh (burnsideI22P5_HSc_normalizes M hρ5)
    exact ((Subgroup.mem_normalizer_iff.1 (hD hc)) w).1 hw
  have hWodd : W ≤ Subgroup.closure
      {a : ↥CFSG.Sporadic.Schreier.hsP | a ∈ C ∧ Odd (orderOf a)} := by
    rw [hW, hQh]
    unfold burnsideI22P5_HSc_Q
    rw [MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
    have ha : M.π (wordVal M.uE p.1) ∈ C := hmemC _
      (M.z1E_comm _ (M.wordVal_uE_mem (burnsideI22P5_HSc_letters.2.2.2.1 p hp))).symm
    have hg : M.π (if p.2 then g3 else g5) ∈ C ∧
        Odd (orderOf (M.π (if p.2 then g3 else g5))) := by
      cases p.2
      · exact ⟨hg5C, by show Odd (orderOf (M.π g5)); rw [hπg5]; decide⟩
      · exact ⟨hg3C, by show Odd (orderOf (M.π g3)); rw [hπg3]; decide⟩
    exact burnsideI22P5_comm_mem_closure M.π C ha hg.1 hg.2
  have hw₀ : M.π (burnsideI22P5_HSc_x0 M.toCoverMaps) ∈ W :=
    Subgroup.mem_map_of_mem M.π (burnsideI22P5_HSc_x0_mem M)
  have hw₀sq : M.π (burnsideI22P5_HSc_x0 M.toCoverMaps) ^ 2 = M.π M.z1E := by
    rw [← map_pow, burnsideI22P5_HSc_x0_sq M]
  set c := burnsideI22P5_HSc_c M.toCoverMaps with hc
  have hcC : M.π c ∈ C := hmemC c (burnsideI22P5_HSc_c_comm M)
  have htz : M.z1E * M.tE = M.tE * M.z1E := Subgroup.mem_center_iff.1 M.tE_mem_center M.z1E
  refine burnsideI22P5_unique_square_of_data M.π M.π_surj ht hZt hker M.z1E S hS2 hSodd hTu W hW2
    hWn hWodd _ hw₀ hw₀sq {M.π c} (fun g hg => by rw [Set.mem_singleton_iff.1 hg]; exact hcC) ?_
  intro x y _ hy _ hyc _ hy2
  have hyT := hmemT y hy
  have hcy : c * y * c⁻¹ ∈ M.T0 := by
    refine hmemT _ ?_
    have h1 := hyc (M.π c) rfl
    rwa [← map_inv, ← map_mul, ← map_mul] at h1
  exact burnsideI22P5_HSc_L M hyT (hy2.trans htz) hcy

open CFSG.EvenSporadicStandard.TwoHS CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native in
theorem burnsideI22P5_unique_square_mul_central {K : Type} [Group K] {z₀ : K}
    (hz : z₀ ∈ Subgroup.center K) (u : K)
    (h : CFSG.ASVolI.ChIJK.UniqueSquareInCoset K u) :
    CFSG.ASVolI.ChIJK.UniqueSquareInCoset K (z₀ * u) := by
  have hy : ∀ y : K, y * z₀ = z₀ * y := fun y => Subgroup.mem_center_iff.1 hz y
  have hcent : Subgroup.centralizer ({z₀ * u} : Set K) = Subgroup.centralizer ({u} : Set K) := by
    ext y
    rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h1
      have : z₀ * (y * u) = z₀ * (u * y) := by
        calc z₀ * (y * u) = (z₀ * y) * u := by group
          _ = (y * z₀) * u := by rw [hy y]
          _ = y * (z₀ * u) := by group
          _ = (z₀ * u) * y := h1
          _ = z₀ * (u * y) := by group
      exact mul_left_cancel this
    · intro h1
      calc y * (z₀ * u) = (y * z₀) * u := by group
        _ = (z₀ * y) * u := by rw [hy y]
        _ = z₀ * (y * u) := by group
        _ = z₀ * (u * y) := by rw [h1]
        _ = (z₀ * u) * y := by group
  unfold CFSG.ASVolI.ChIJK.UniqueSquareInCoset at h ⊢
  rw [hcent]
  refine (existsUnique_congr (fun v => ?_)).2 h
  refine and_congr ?_ Iff.rfl
  constructor
  · rintro ⟨z, hzc, rfl⟩
    refine ⟨z₀ * z, Subgroup.mul_mem _ hz hzc, ?_⟩
    calc z₀ * u * z = (z₀ * u) * z := rfl
      _ = (u * z₀) * z := by rw [hy u]
      _ = u * (z₀ * z) := by group
  · rintro ⟨z, hzc, rfl⟩
    refine ⟨z₀⁻¹ * z, Subgroup.mul_mem _ (Subgroup.inv_mem _ hz) hzc, ?_⟩
    have e1 : (z₀ * u) * (z₀⁻¹ * z) = u * z := by
      calc (z₀ * u) * (z₀⁻¹ * z) = (u * z₀) * (z₀⁻¹ * z) := by rw [hy u]
        _ = u * z := by group
    exact e1.symm

open CFSG.EvenSporadicStandard.TwoHS CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native CFSG.ASVolI.ChIJK in
theorem burnsideI22P5_HS_c
    {K : Type} [Group K] [Finite K] (hK : CFSG.IsQuasisimple K)
    (hZ : Subgroup.center K ≠ ⊥)
    (h : CFSG.Blueprint.NativeSporadic.IsSporadic (K ⧸ Subgroup.center K) .HS) (u : K)
    (hu : u ∉ Subgroup.center K) (hu2 : u ^ 2 = 1) : UniqueSquareInCoset K u := by
  haveI : Group.IsPerfect K := hK.1
  have hZ2 := CFSG.EvenSporadicStandard.HSStd.Zassenhaus.card_center_eq_two_of_ne_bot this h hZ
  obtain ⟨M⟩ := exists_coverModel this hZ2 h
  have hu1 : u ≠ 1 := fun h1 => hu (h1 ▸ one_mem _)
  have hut : u ≠ M.tE := fun h1 => hu (h1 ▸ M.tE_mem_center)
  obtain ⟨e, he⟩ := M.exists_conj_of_involution hZ2 hu2 hu1 hut
  have hz1 := burnsideI22P5_HS_c_z1 this hZ2 h M
  have h2 : UniqueSquareInCoset K (e * u * e⁻¹) := by
    rcases he with he | he
    · rw [he]; exact hz1
    · rw [he]; exact burnsideI22P5_unique_square_mul_central M.tE_mem_center _ hz1
  have h3 := burnsideI22P5_unique_square_conj e⁻¹ _ h2
  have e1 : e⁻¹ * (e * u * e⁻¹) * e⁻¹⁻¹ = u := by group
  rw [e1] at h3
  exact h3

open CFSG.ASVolI.ChIJK CFSG.Blueprint in
theorem burnsideI22P5_clause_a
    {K : Type} [Group K] [Finite K] (hK : CFSG.IsQuasisimple K)
    (hZ : Subgroup.center K ≠ ⊥)
    (h : ChevalleyExceptionalModel (K ⧸ Subgroup.center K) .G2 2 2 ∨
        NativeSporadic.IsSporadic (K ⧸ Subgroup.center K) .J2 ∨
        NativeSporadic.IsSporadic (K ⧸ Subgroup.center K) .M12 ∨
        NativeSporadic.IsSporadic (K ⧸ Subgroup.center K) .HS) :
    TwoCentralInvolutionsLift K := by
  rcases h with h | h | h | h
  · exact burnsideI22P5_G2_a hK hZ h
  · exact burnsideI22P5_J2_a hK hZ h
  · exact burnsideI22P5_M12_a hK hZ h
  · exact burnsideI22P5_HS_a hK hZ h

open CFSG.ASVolI.ChIJK CFSG.Blueprint in
theorem burnsideI22P5_clause_b1
    {K : Type} [Group K] [Finite K]
    (hK : CFSG.IsQuasisimple K) (hZ : Subgroup.center K ≠ ⊥)
    (h : ChevalleyExceptionalModel (K ⧸ Subgroup.center K) .G2 2 2 ∨
        NativeSporadic.IsSporadic (K ⧸ Subgroup.center K) .J2 ∨
        NativeSporadic.IsSporadic (K ⧸ Subgroup.center K) .M12 ∨
        NativeSporadic.IsSporadic (K ⧸ Subgroup.center K) .HS) :
    NonTwoCentralInvolutionsLiftToOrderFour K := by
  rcases h with h | h | h | h
  · exact burnsideI22P5_G2_b1 hK hZ h
  · exact burnsideI22P5_J2_b1 hK hZ h
  · exact burnsideI22P5_M12_b1 hK hZ h
  · exact burnsideI22P5_HS_b1 hK hZ h

open CFSG.ASVolI.ChIJK CFSG.Blueprint in
theorem burnsideI22P5_clause_b2
    {K : Type} [Group K] [Finite K]
    (hK : CFSG.IsQuasisimple K) (hZ : Subgroup.center K ≠ ⊥)
    (h : ChevalleyExceptionalModel (K ⧸ Subgroup.center K) .G2 2 2 ∨
        NativeSporadic.IsSporadic (K ⧸ Subgroup.center K) .J2 ∨
        NativeSporadic.IsSporadic (K ⧸ Subgroup.center K) .M12 ∨
        NativeSporadic.IsSporadic (K ⧸ Subgroup.center K) .HS) :
    OuterInvolutionsInvertOrderFour K := by
  rcases h with h | h | h | h
  · exact burnsideI22P5_G2_b2 hK hZ h
  · exact burnsideI22P5_J2_b2 hK hZ h
  · exact burnsideI22P5_M12_b2 hK hZ h
  · exact burnsideI22P5_HS_b2 hK hZ h

open CFSG.ASVolI.ChIJK CFSG.Blueprint in
theorem burnsideI22P5_clause_c
    {K : Type} [Group K] [Finite K]
    (hK : CFSG.IsQuasisimple K) (hZ : Subgroup.center K ≠ ⊥)
    (h : ChevalleyExceptionalModel (K ⧸ Subgroup.center K) .G2 2 2 ∨
        NativeSporadic.IsSporadic (K ⧸ Subgroup.center K) .J2 ∨
        NativeSporadic.IsSporadic (K ⧸ Subgroup.center K) .M12 ∨
        NativeSporadic.IsSporadic (K ⧸ Subgroup.center K) .HS) :
    ¬ ChevalleyExceptionalModel (K ⧸ Subgroup.center K) .G2 2 2 →
      ∀ u : K, u ∉ Subgroup.center K → u ^ 2 = 1 → UniqueSquareInCoset K u := by
  intro hnG2 u hu hu2
  rcases h with h | h | h | h
  · exact absurd h hnG2
  · exact burnsideI22P5_J2_c hK hZ h u hu hu2
  · exact burnsideI22P5_M12_c hK hZ h u hu hu2
  · exact burnsideI22P5_HS_c hK hZ h u hu hu2

section

open CFSG.ASVolI.ChIJK CFSG.Blueprint in
theorem burnsideI22P5_part_5 {K : Type} [Group K] [Finite K] (hK : CFSG.IsQuasisimple K)
    (hZ : Subgroup.center K ≠ ⊥) :
    ((ChevalleyExceptionalModel (K ⧸ Subgroup.center K) .G2 2 2 ∨
        NativeSporadic.IsSporadic (K ⧸ Subgroup.center K) .J2 ∨
        NativeSporadic.IsSporadic (K ⧸ Subgroup.center K) .M12 ∨
        NativeSporadic.IsSporadic (K ⧸ Subgroup.center K) .HS) →
      TwoCentralInvolutionsLift K ∧
      (NonTwoCentralInvolutionsLiftToOrderFour K ∧ OuterInvolutionsInvertOrderFour K) ∧
      (¬ ChevalleyExceptionalModel (K ⧸ Subgroup.center K) .G2 2 2 →
        ∀ u : K, u ∉ Subgroup.center K → u ^ 2 = 1 → UniqueSquareInCoset K u)) := by
  intro h
  exact ⟨burnsideI22P5_clause_a hK hZ h,
    ⟨burnsideI22P5_clause_b1 hK hZ h, burnsideI22P5_clause_b2 hK hZ h⟩,
    burnsideI22P5_clause_c hK hZ h⟩

end

end PartBurnsideI22P5

section PartBurnsideI22P7


open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.RuSchreier
  CFSG.EvenSporadicStandard.TwoRu.SzCover in

open CFSG.CosetTable CFSG.Sporadic.Recognition.RuMultiplier CFSG.EvenSporadicStandard.TwoRu
  CFSG.Quasithin.KGC31.RuCover CFSG.Sporadic.RuSchreier CFSG.Monster.B.Co2
  CFSG.Sporadic.SmallF2 CFSG.Monster.B.Co2.Native CFSG.LieType.Multipliers.Tits
  CFSG.Sporadic.Presentation.Ru.Exact in


open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.EvenSporadicStandard.TwoRu.SzCover in

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.RuSchreier
  CFSG.EvenSporadicStandard.TwoRu.SzCover CFSG.EvenSporadicStandard.Induction.RuSz
  CFSG.Quasithin.KGC31.RuCover in

open Subgroup CFSG.Sporadic.Bridge CFSG.Sporadic.Bridge.TwoGen CFSG.LieType.Multipliers
  CFSG.LieType.Multipliers.Sz8 CFSG.EvenSporadicStandard.Induction.RuSz in

open Subgroup CFSG.Sporadic.Bridge CFSG.Sporadic.Bridge.TwoGen CFSG.LieType.Multipliers
  CFSG.LieType.Multipliers.Sz8 CFSG.EvenSporadicStandard.Induction.RuSz in

open Subgroup CFSG.Sporadic.Bridge CFSG.Sporadic.Bridge.TwoGen CFSG.LieType.Multipliers
  CFSG.LieType.Multipliers.Sz8 CFSG.EvenSporadicStandard.Induction.RuSz
  CFSG.Sporadic.RuSchreier in


open CFSG.Sporadic.RuSchreier CFSG.EvenSporadicStandard.Induction.RuSz
  CFSG.EvenSporadicStandard.TwoRu in

open CFSG.Blueprint CFSG.ASVolI.ChIJK CFSG.Sporadic.RuSchreier CFSG.EvenSporadicStandard.TwoRu
  CFSG.EvenSporadicStandard.Induction.RuSz in


open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.RuSchreier
  CFSG.EvenSporadicStandard.TwoRu.CentCover in

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.RuSchreier
  CFSG.EvenSporadicStandard.TwoRu.CentCover in


open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.RuSchreier
  CFSG.EvenSporadicStandard.TwoRu.CentCover in

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.RuSchreier
  CFSG.EvenSporadicStandard.TwoRu.CentCover in

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.RuSchreier
  CFSG.EvenSporadicStandard.TwoRu.CentCover in

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.RuSchreier
  CFSG.EvenSporadicStandard.TwoRu.CentCover in

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.RuSchreier
  CFSG.EvenSporadicStandard.TwoRu.CentCover in

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.RuSchreier
  CFSG.EvenSporadicStandard.TwoRu.CentCover in

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.RuSchreier
  CFSG.EvenSporadicStandard.TwoRu.CentCover in


open CFSG.Sporadic.RuSchreier CFSG.EvenSporadicStandard.TwoRu CFSG.EvenSporadicStandard.TwoRu.CentCover
  CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Quasithin.KGC31.RuCover in


section


end

end PartBurnsideI22P7

section


end

end CFSG.ASVolI
