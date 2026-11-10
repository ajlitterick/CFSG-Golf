module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveTenFromSpine
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixOfCtx
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.BlockRankCount
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.BlockTypeLThree
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.BlockRankUpper
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.BlockRankLower
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveTenSpine
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section8.O812sixFi22
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section8.KFactFi22SPEHolds
public import CFSG.LocalAnalysis.AGL81I.Section4.FourNineteenHolds
public import CFSG.HardMathSupport.Foote.Coordinator.Downstream
public import CFSG.CGT.PushingUpLit.TwoKHolds
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2LocalCGT3
public import CFSG.LocalAnalysis.AGLEmbedding.AscEightFour
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TenFifteenProof
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveFourOneOf
import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineHolds
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixKbarOfCtx
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixKbarSingleProof
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.NineSixMoreoverPairFiveProof
import CFSG.LocalAnalysis.RankThreeUC.AGL81CKFactThreeFiveRankOne
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TenFifteenKFactParabolic
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TenFifteenKFactOutDerived
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.HGenFinal
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.HSubFinal
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.NineTenBranches
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.OpPrimeCoreLe
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.PCoreCharacteristic
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveTenFinalAD
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveThreeConclusion
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanIdentOffCharGen
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanMonsterThreeCase
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrime
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallAutFix
public import CFSG.LocalAnalysis.AGLEmbedding.OneLieZZK0ShapeFacts
public import CFSG.LocalAnalysis.AGLEmbeddingD2.MonsterRows
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineEightBridge
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankCases
public import CFSG.LocalAnalysis.RankThreeUC.ModuleHypotheses
public import CFSG.LocalAnalysis.RankThreeUC.ModuleRanks
public import CFSG.LocalAnalysis.RankThreeUC.Notation
public import CFSG.LocalAnalysis.RankThreeUC.SourceSetting.AschbacherCommon
public import CFSG.LocalAnalysis.RankThreeUC.WeakModules
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.KInputsSolvableOf
public import CFSG.Quasithin.H13.L32NKGSp6Group
public import CFSG.RankThree.PartOne.S11b.OuterPrimeTwoSporadicOpen
import CFSG.GH74.GLS.IVK.Proofs2.Ivk73G4U3Out
import CFSG.GH74.GLS.IVK.Proofs2.Ivk93Cfg2
import CFSG.GH74.GLS.IVK.Proofs2.Ivk93Field
import CFSG.GH74.GLS.IVK.Proofs2.Ivk93PGU
import CFSG.GH74.GLS.IVK.Proofs2.Ivk93WPGU
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanLieOutFieldG2
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanLieOutModels
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ParabThreeInv
import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.C126GenGlue
import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.C126GenType
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.BaumComponent
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.GOrbPerfect
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.SymDefs
import CFSG.Quasithin.Background.C126Split2
import CFSG.RankThree.PartOne.S11c.Sec66E6

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open


theorem twelveSixKbar_of_twelveCtx_of_isSylowOf {G : Type} [Group G] [Finite G]
    {M : Subgroup G} {p : ℕ} {Q H : Subgroup G} (h : TwelveCtx G M p Q H)
    (hsyl : CFSG.ABGLocalTools.IsSylowOf p Q H)
    (h41 : ∀ d : ℕ, d ∈ sigmaSet G M → ¬ d ∣ Nat.card (H ⊓ M : Subgroup G))
    (h1015 : TenFifteenSigma M H) {d : ℕ} {L₁ L₂ L₃ : Subgroup G} {n₁ n₂ n₃ : ℕ}
    (hd : TwelveFiveData M H d L₁ L₂ L₃ n₁ n₂ n₃) : TwelveSixKbar M H p n₁ n₂ n₃ :=
  twelveSixKbar_of_twelveCtx_of_single
    (twelveSixKbarSingle_of
      CFSG.LocalAnalysis.RankThreeUC.AGL81C.kFactThreeFiveRankOne_holds
      nineSixMoreoverPairFive_holds kFactSz32MulAutThreeFree_holds)
    h hsyl h41 h1015 hd


theorem twelveFourOne_of_twelveCtx {G : Type} [Group G] [Finite G] {M : Subgroup G} {p : ℕ}
    {Q H : Subgroup G} (h : TwelveCtx G M p Q H) (hsyl : CFSG.ABGLocalTools.IsSylowOf p Q H) :
    ∀ d : ℕ, d ∈ sigmaSet G M → ¬ d ∣ Nat.card (H ⊓ M : Subgroup G) :=
  twelveFourOne_of_twelveCtx_of_threeNine CFSG.LocalAnalysis.AGL81I.Section3.threeNine_holds h hsyl

theorem tenFifteenSigma_of_twelveCtx_of_isSylowOf {G : Type} [Group G] [Finite G]
    {M : Subgroup G} {p : ℕ} {Q H : Subgroup G} (h : TwelveCtx G M p Q H)
    (hsyl : CFSG.ABGLocalTools.IsSylowOf p Q H) : TenFifteenSigma M H :=
  tenFifteenSigma_of_twelveCtx CFSG.HardMathSupport.Foote.Coordinator.aschbacherTheoremOneK_proved
    CFSG.CGT.PushingUpLit.aschbacherTheoremTwoK_holds
    CFSG.CGT.PushingUpLit.solomonAlternatingBlockK_holds
    (CFSG.AGLEmbedding.asc81bEightFour_of_factorization
        CFSG.LocalAnalysis.RankThreeTheoremC.aschbacherLocalFactorization_proved) kFactLieParabolicClass_holds
    kFactLieOutDerived_holds h (twelveFourOne_of_twelveCtx h hsyl)

theorem twelveSix_of_twelveCtx_of_isSylowOf {G : Type} [Group G] [Finite G]
    {M : Subgroup G} {p : ℕ} {Q H : Subgroup G} (h : TwelveCtx G M p Q H)
    (hsyl : CFSG.ABGLocalTools.IsSylowOf p Q H) :
    ∀ (d : ℕ) (L₁ L₂ L₃ : Subgroup G) (n₁ n₂ n₃ : ℕ),
      TwelveFiveData M H d L₁ L₂ L₃ n₁ n₂ n₃ → TwelveSix M H p d L₁ L₂ L₃ n₁ n₂ n₃ := by
  intro d L₁ L₂ L₃ n₁ n₂ n₃ hd
  have h41 := twelveFourOne_of_twelveCtx h hsyl
  have h1015 := tenFifteenSigma_of_twelveCtx_of_isSylowOf h hsyl
  have h1 := CFSG.HardMathSupport.Foote.Coordinator.aschbacherTheoremOneK_proved
  have h2 := CFSG.CGT.PushingUpLit.aschbacherTheoremTwoK_holds
  have h25 := CFSG.CGT.PushingUpLit.solomonAlternatingBlockK_holds
  have h84 := CFSG.AGLEmbedding.asc81bEightFour_of_factorization
      CFSG.LocalAnalysis.RankThreeTheoremC.aschbacherLocalFactorization_proved
  obtain ⟨-, hk1, hmdL⟩ := blockRank_count h1 h2 h25 h84
    CFSG.LocalAnalysis.AGL81I.Section4.agl81FourNineteen_holds h h41 h1015
  have hL3 := hL3_of_blocks h1 h2 h25 h hk1
  obtain ⟨h124, h125, hcard⟩ :=
    twelveFour_twelveFive_of_blocks h h1 h2 h25 h84 h41 h1015 hmdL hL3
  have hdvdL := hdvdL_of_blocks hL3 hmdL (pRank_three_le_three_of_twelveCtx h h124)
    (hr3_of_hL3 hL3) (hd3_of_tenFifteenSigma h h124 h1015)
  exact twelveSix_of_twelveCtx h
    (Section8.o812sixGen_of_fi22 Section8.kFactFi22SPEThreeRank) h124 h125 hL3 hdvdL hcard
    (twelveSixKbar_of_twelveCtx_of_isSylowOf h hsyl h41 h1015 hd) hd

theorem twelveTenGen_of_fields : CFSG.LocalAnalysis.AGL81TheoremCD.Section14.TwelveTenGen :=
  twelveTenGen_of_spineV3 fun _ _ _ _ _ _ _ h hsyl =>
    ⟨twelveFourOne_of_twelveCtx h hsyl, tenFifteenSigma_of_twelveCtx_of_isSylowOf h hsyl,
      twelveSix_of_twelveCtx_of_isSylowOf h hsyl⟩

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12
