module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoStandardAssembly
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicFinal
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoExceptionalOpen
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltOpen
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltFiveCaseI
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltGenSmall
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltThree
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicBTwoD
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3CensusCertBase
public import CFSG.Sporadic.Co1Patterson.Main

public section

namespace CFSG.ComponentClassification.RankTwoStandard

open CFSG.Blueprint

theorem ct_rank_two_standard_recognition_of_leaves
    (hH1 : GMS78.RuH1Stmt)
    (hdich : CFSG.Sporadic.SuzRecog.SuzMixedCells)
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hK : Assembly.KProper Catalog G) (L : Subgroup G) (hL : Open.standardComponentIsStandard L)
    (hrank : 2 ≤ Open.pRank 2 (Subgroup.centralizer (L : Set G))) :
    (∃ n : ℕ, 9 ≤ n ∧ Nonempty (G ≃* alternatingGroup (Fin n))) ∨
      (NativeSporadic.IsSporadic G .J2 ∨ NativeSporadic.IsSporadic G .Suz ∨
        NativeSporadic.IsSporadic G .He ∨ NativeSporadic.IsSporadic G .Ru ∨
        NativeSporadic.IsSporadic G .Co1) := by
  have h2C : RankTwoSporadic.B.B2CFact := RankTwoSporadic.B.twoC_classFact
  have h2D : RankTwoSporadic.B.B2DFact := RankTwoSporadic.B.twoD_classFact
  have h2 := GMS78.rankTwoBenderStandard_of_open hH1
  have h4 := AS81.rankTwoL3EvenStandard_of_open h2 hdich
  have h6 := RankTwoClassical.rankTwoClassicalEvenStandard_of_open h2 h4
  have h5 := RankTwoExceptional.rankTwoExceptionalEvenStandard_of_open h2 h4 h6
  have h1 := RankTwoAlt.rankTwoAlternatingStandard_of_open
      (RankTwoAltFive.altFiveCaseI_of
          (RankTwoAlt.altGenerationFive_of AS76b.asc08Lemma34 Asc76X.goldschmidtTheoremA))
      (RankTwoAltFive.asc310EpsOne_of Asc76X.goldschmidtTheoremA) RankTwoAltFive.asc310IIb
      RankTwoAlt.altFiveM12NotTop_of RankTwoAlt.altEvenCenterSmall RankTwoAlt.altThreeCover
      (RankTwoAlt.altGenerationSmall_of AS76b.asc08Lemma34 Asc76X.goldschmidtTheoremA)
      RankTwoAlt.altRootFusion (RankTwoAlt.altTypeTwoFusion_of_rootFusion RankTwoAlt.altRootFusion)
      (RankTwoAlt.altTypeTwoCentralizer Asc76X.goldschmidtTheoremA)
  exact ct_rank_two_standard_recognition_of_children h1 h2 RankTwoFoundation.rankTwoOddLieStandard
      h4 h5 h6 (RankTwoSporadic.rankTwoSporadicStandard_of_open h2C h2D) G hnonab hK L hL hrank

end CFSG.ComponentClassification.RankTwoStandard
