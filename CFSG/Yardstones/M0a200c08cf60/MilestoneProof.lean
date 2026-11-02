module

public import CFSG.Yardstones.M0a200c08cf60.Goals
public import CFSG.Yardstones.M0a200c08cf60.Reduction
public import CFSG.Milestones.CL_LIT_classical_involution_theorem
public import CFSG.Monster.Existence.StdOdd.Defs
public import Certificates.Data.CFSGNative.Chevalley.C2E6CertLie
public import CFSG.LieType.Chevalley.C2E6StdMatrixData
public import CFSG.Monster.B.Classical.E6AdjointGroup
import Certificates.Kernel.Misc.E6StdSlp
public import CFSG.Blueprint.NativeSporadic
public import CFSG.RankThree.PartOne.CTP.FusionSound
import CFSG.Sporadic.Bridge.BFusSevenGen
public import CFSG.YGroups.Y443.Native.CoverFactsWords
import Certificates.Kernel.KDense.Y443
public import CFSG.YGroups.Y443.Native.Swap13Word
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Co2DfsSound
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Co2Sylow
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Fi22CoverCheck
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Fi23Check
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.ONCheck
public import CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6.AdjDisp
public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.EightTenFour.A7RadicalBase
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerSplit
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwReduction
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.Assembly
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.PlanesSetup
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLin
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.ExcInnerTorus
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.LangFrame
public import CFSG.LargeExtraspecial.GLRElimInv
public import CFSG.LargeExtraspecial.GLRTransfer
public import CFSG.LargeExtraspecial.S12FourteenB
public import CFSG.LargeExtraspecial.S14C10Apply
public import CFSG.LargeExtraspecial.S14W4LocInst
public import CFSG.LargeExtraspecial.S14W4LocRed
public import CFSG.LargeExtraspecial.S4EightC
public import CFSG.LargeExtraspecial.S4EightD
public import CFSG.LargeExtraspecial.S4EightE
public import CFSG.LargeExtraspecial.S4EightMain
public import CFSG.LargeExtraspecial.S5Three
public import CFSG.LargeExtraspecial.S6SevenC
public import CFSG.LargeExtraspecial.S8FusE
public import CFSG.LargeExtraspecial.S8Lin
public import CFSG.LieType.Universal.Spin
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanMonsterThreeCase
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanMonsterThreeIdent
public import CFSG.LocalAnalysis.AGLEmbedding.Norton.OrdinaryProofs.MonsterCarrierSimple
public import CFSG.LocalAnalysis.AGLEmbedding.Norton.OrdinaryProofs.MonsterCaseThreeAssembly
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4LayerB
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4LayerD
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofE7TwistMain
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.CenterAt
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.GlobFactor
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.GlobSetting
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.GlobSylow
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.LocGen
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.Out1SlimEquiv
public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergBLFourUnitaryScalarQuotient
public import CFSG.Quasithin.Background.GoldschmidtRankOneFacts
public import CFSG.Quasithin.Vol2.Ch10SecKRefA312
public import CFSG.RankThree.PartOne.K133H.G2Plane
public import CFSG.RankThree.PartOne.KE.E6FourPlane
public import CFSG.RankThree.PartOne.KE.E7FourPlane
public import CFSG.RankThree.PartOne.KE.E7ThreeFinal
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.FixedFieldCard
public import CFSG.Sporadic.Recognition.LyonsFinalDist2

public section

namespace CFSG.Yardstones.M0a200c08cf60

theorem lc_gl_embedding_theorem_d1_rank_four_of_goals
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hK : CFSG.Open.IsKProper G) (hchar : CFSG.Open.IsCharTwoType G)
    (he : 4 ≤ CFSG.Open.evenRank G) (hpre : CFSG.Open.GLBPreuniqueness G)
    (p : ℕ) (hp : p ∈ CFSG.Open.GLBBetaFour G) (P : Sylow p G)
    (M : Subgroup G) (hM : CFSG.Open.GLBIsMaxTwoLocal M)
    (hWM : CFSG.Open.GLBWeakCore p (P : Subgroup G) ≤ M)
    (H : Subgroup G) (hH : CFSG.Open.IsTwoLocal H) (hHM : 3 ≤ CFSG.Open.pRank p (H ⊓ M)) :
    H ≤ M :=
  lc_gl_embedding_theorem_d1_rank_four_of_yardstones
    twistedE6TypeBound_holds
    orthMinusCentOb_holds
    e0NonShortNotCaseIStatement_holds
    excAnisotropicF4Residuals_holds
    excAnisotropicE6E8Residuals_holds
    excAnisotropicThreeResiduals_holds
    subfieldPairOmegaPlusF2_holds
    subfieldPairOmegaMinusF2_holds
    excOuterLeOneResiduals_holds
    subfieldPairReeG2_holds
    trialityPhi6Placements_holds
    kFactSeitzOuterCubeRankTwo_holds
    p1OffCharNonNormalRest_holds
    cit3Inductive_holds
    tightLiftSimple_holds
    CFSG.Milestones.cl_lit_classical_involution_theorem_models
    G hnonab hK hchar he hpre p hp P M hM hWM H hH hHM

end CFSG.Yardstones.M0a200c08cf60
