module

public import CFSG.LocalAnalysis.ComponentClassification.GSLitTripleBranch
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourAlternatingExclusion
import CFSG.Adapters.StatedPSLTwo

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.GSLit


variable {G : Type*} [Group G] [Finite G]


theorem two_le_pRank_of_small_type {X : Type} [Group X] [Finite X] {x : X} {L : Subgroup X}
    (hLx : L ≤ centralizer ({x} : Set X))
    (hL : IsPComponent 2 (L.subgroupOf (centralizer ({x} : Set X))))
    (htype : Nonempty (L ⧸ pPrimeCore 2 L ≃* alternatingGroup (Fin 7)) ∨
      ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ 5 ≤ p ^ f ∧
        Blueprint.LieModel (L ⧸ pPrimeCore 2 L) .PSL 2 p f) : 2 ≤ pRank 2 ↥L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let e : L ⧸ oddCore L ≃* L ⧸ pPrimeCore 2 L :=
    QuotientGroup.quotientMulEquivOfEq (GSLit.oddCore_eq_pPrimeCore_two L)
  have hq : IsQuasisimple (L ⧸ pPrimeCore 2 L) :=
    ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 L _ hLx).1 hL).2.2
  have hA : IsQuasisimple (L ⧸ oddCore L) :=
    (CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_congr e.symm).1 hq
  rcases htype with ⟨⟨e7⟩⟩ | ⟨p, f, hp, hp2, hf, -, hmodel⟩
  · exact UnbalancedGS.small_source_models_force_rank_at_least_two hA
      (Or.inr (Or.inl ⟨e.trans e7⟩))
  · exact UnbalancedGS.small_source_models_force_rank_at_least_two hA
      (Or.inl ⟨p, f, hp, hp.odd_of_ne_two hp2, hf, SectionRank.statedClassicalModel_of_mulEquiv e
        (GSLit.statedClassicalModel_of_lieModel_psl_two hmodel)⟩)


theorem isSimpleGroup_of_lieModel_psl_two {X : Type} [Group X] {p f : ℕ}
    (hL : Blueprint.LieModel X .PSL 2 p f) : IsSimpleGroup X :=
  CFSG.Blueprint.LieModel.isSimpleGroup_psl_two hL

theorem fusionZStar_eq_pPrimeCore_of_simple {Y : Type*} [Group Y]
    (hs : IsSimpleGroup (Y ⧸ pPrimeCore 2 Y)) (hne : Open.fusionZStar Y ≠ ⊤) :
    Open.fusionZStar Y = pPrimeCore 2 Y := by
  have hO := UnbalancingLocal.fusionOddCore_eq_pPrimeCore Y
  let e : Y ⧸ Open.fusionOddCore Y ≃* Y ⧸ pPrimeCore 2 Y := QuotientGroup.quotientMulEquivOfEq hO
  have he : ∀ y : Y, e (QuotientGroup.mk' (Open.fusionOddCore Y) y) = (y : Y ⧸ pPrimeCore 2 Y) :=
    fun y => QuotientGroup.quotientMulEquivOfEq_mk hO y
  have hcen : ∀ y : Y, y ∈ Open.fusionZStar Y ↔
      (y : Y ⧸ pPrimeCore 2 Y) ∈ center (Y ⧸ pPrimeCore 2 Y) := by
    intro y
    show QuotientGroup.mk' (Open.fusionOddCore Y) y ∈ center _ ↔ _
    constructor
    · intro h1
      rw [mem_center_iff]
      intro g
      obtain ⟨g', rfl⟩ := e.surjective g
      have h2 := congrArg e (mem_center_iff.mp h1 g')
      rwa [map_mul, map_mul, he] at h2
    · intro h1
      rw [mem_center_iff]
      intro g
      apply e.injective
      rw [map_mul, map_mul, he]
      exact mem_center_iff.mp h1 (e g)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center (Y ⧸ pPrimeCore 2 Y)) with h | h
  · ext y
    rw [hcen, h, mem_bot, QuotientGroup.eq_one_iff]
  · exfalso
    apply hne
    ext y
    simp only [mem_top, iff_true]
    rw [hcen, h]
    exact mem_top _

theorem false_of_psl34_of_psl_two {J : Type} [Group J] [Finite J] {p f : ℕ}
    (h34 : Blueprint.LieModel (J ⧸ Open.fusionZStar J) .PSL 3 2 2) (hp2 : p ≠ 2)
    (h2 : Blueprint.LieModel (J ⧸ pPrimeCore 2 J) .PSL 2 p f) : False := by
  have h20160 := (PSL3Four.excludes_alternating_models_stated.{0} _
    (GSLit.statedClassicalModel_of_lieModel_psl_three h34)).1
  have hne : Open.fusionZStar J ≠ ⊤ := by
    intro htop
    have h1 : Nat.card (J ⧸ Open.fusionZStar J) = 1 := by
      rw [htop]
      exact Nat.card_eq_one_iff_unique.mpr ⟨QuotientGroup.subsingleton_quotient_top, inferInstance⟩
    omega
  have hZ := fusionZStar_eq_pPrimeCore_of_simple (isSimpleGroup_of_lieModel_psl_two h2) hne
  have hcard1 : Nat.card (J ⧸ pPrimeCore 2 J) = 20160 := by
    rw [← Nat.card_congr (QuotientGroup.quotientMulEquivOfEq hZ).toEquiv]
    exact h20160
  obtain ⟨⟨hp, hf, -, -, -⟩, F, _, _, hF, ⟨e2⟩⟩ := GSLit.statedClassicalModel_of_lieModel_psl_two h2
  have hcard2 := GorensteinWalter.psl2_card_formula F ⟨p, f, hp, hp.odd_of_ne_two hp2, hf, hF⟩
  rw [← Nat.card_congr
    ((e2.trans (Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 F).symm).toEquiv),
    hcard1, hF] at hcard2
  set q := p ^ f with hq
  have key : q * (q ^ 2 - 1) = 40320 ∨ q * (q ^ 2 - 1) = 40321 := by omega
  rcases le_or_gt q 34 with h | h
  · have hle : q * (q ^ 2 - 1) ≤ 34 * (34 ^ 2 - 1) :=
      Nat.mul_le_mul h (Nat.sub_le_sub_right (Nat.pow_le_pow_left h 2) 1)
    norm_num at hle
    omega
  · have hle : 35 * (35 ^ 2 - 1) ≤ q * (q ^ 2 - 1) :=
      Nat.mul_le_mul h (Nat.sub_le_sub_right (Nat.pow_le_pow_left h 2) 1)
    norm_num at hle
    omega


end CFSG.ComponentClassification.GrSLit
