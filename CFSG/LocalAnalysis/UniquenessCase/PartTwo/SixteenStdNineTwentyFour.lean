module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Nine24XMain
public import CFSG.LocalAnalysis.UniquenessCase.UCKInputs2
public import CFSG.CGT.PushingUpLit.CGT6.SixThreeCore
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Nine24XThreeElts
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Nine24XKDHolds
import CFSG.LocalAnalysis.UniquenessCase.UCFront09R99
import CFSG.LocalAnalysis.UniquenessCase.UCFront09R9R5
import CFSG.LocalAnalysis.UniquenessCase.UCFront09R911
import CFSG.LocalAnalysis.UniquenessCase.UCFront09R92b
public import CFSG.LocalAnalysis.UniquenessCase.UC6R640Cert
public import CFSG.CGT.PushingUpLit.TwoKHolds
public import CFSG.HardMathSupport.Foote.Coordinator.Downstream
public import CFSG.LocalAnalysis.UniquenessCase.UC1K32
public import CFSG.LocalAnalysis.UniquenessCase.UC1K462Holds
public import CFSG.LocalAnalysis.AGLEmbedding.CatalogSchreier
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeDefs
public import CFSG.CGT.PushingUpLit.BHS6.NestedBasic
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk95J3
public import CFSG.GH74.GLS.IVK.Proofs2.Stmt111c
public import CFSG.GH74.Generic.S45.LEvSporFacts
public import CFSG.LargeExtraspecial.DWModelSplit
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVL34FFDefs
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddAssembly
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitKGTools
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Lemma39
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec4
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitN36AltPerm
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitN36MType
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitN36SporMult
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicCo1Cen2BData
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.Extremal
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKDQuot
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.S628Common
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.StrongMain
public import CFSG.LocalAnalysis.RankFourTheoremC.PPointLemma32
public import CFSG.LocalAnalysis.RankFourTheoremC.RelativePair.ZJGe
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5KFacts
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank614L615
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank627L32Data
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62yDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.InvariantTwoBalanceThree
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.P622KDOddHolds
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.P622KDQuot
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Setup
public import CFSG.LocalAnalysis.SteinbergCEOddResidualE6Graph
public import CFSG.Monster.Existence.TwoPoint.Fi22Iso
public import CFSG.Monster.Existence.TwoPoint.Fi23RelsLongJ
public import CFSG.Monster.Existence.TwoPoint.Fi23RelsLongM
public import CFSG.Monster.Existence.TwoPoint.Fi23RelsLongP
public import CFSG.Monster.Existence.TwoPoint.Fi23S4CommBase
public import CFSG.Monster.Existence.TwoPoint.Fi23S4ConjBase
public import CFSG.Monster.Existence.TwoPoint.Fi23S4CubeBase
public import CFSG.Monster.Existence.TwoPoint.GammaExclCheck
public import CFSG.Monster.Existence.TwoPoint.GammaExclTwoBCheck
public import CFSG.Monster.Existence.TwoPoint.Y433MF213
public import CFSG.Monster.Existence.TwoPoint.Y433MF312
public import CFSG.Monster.Existence.TwoPoint.Y433MSpider
public import CFSG.Quasithin.Background.D14Normal
public import CFSG.Quasithin.H13.A5S1327j
public import CFSG.Quasithin.Vol2.Ch10SecD33
public import CFSG.Quasithin.Vol2.Ch10SecDClA
public import CFSG.Quasithin.Vol2.Ch11SecA11Main
public import CFSG.Quasithin.Vol2.Ch11SecSMain
public import CFSG.Quasithin.Vol2.Ch11SecSShape2
public import CFSG.Quasithin.Vol2.Ch11SecSSym2
public import CFSG.Quasithin.Vol2.Ch11SecSSym4
public import CFSG.Quasithin.Vol2.Ch11SecSSym5
public import CFSG.RankThree.PartOne.SPOR.OuterSimple
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary.Cover3
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.OrderCheckF
public import CFSG.Sporadic.Co1.Cover.Checks
public import CFSG.Walter.W67.W2Lemma26A
public import CFSG.YGroups.Y443.Native.Parabolic2CheckB
public import CFSG.YGroups.Y443.Native.Parabolic2CheckW
public import Certificates.Data.CFSGNative.Co1.CoTwoAutData
public import Certificates.Data.CFSGNative.Co1.CoTwoAutOrbit
public import Certificates.Kernel.J4Count.Prim

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

section



theorem r9_24X_of_r6_3 {D : Data G} (h63 : UC6.R6_3 D) : R9_24X D :=
  r9_24X_of_inputs D h63
      (F09.r912L2_of_inputs D (F09.r99_holds D) (F09.r910_holds D)
          (F09.r911_of
              (CFSG.CGT.PushingUpLit.CGT6.aschbacherSixThreeCore_of_embeddingK
                  CFSG.HardMathSupport.Foote.Coordinator.aschbacherEmbeddingK_proved) D
              (UC6.r6_40_1_holds CFSG.CGT.PushingUpLit.aschbacherTheoremTwoK_holds
                  CFSG.CGT.PushingUpLit.solomonAlternatingBlockK_holds D)) (F09.r9R5_holds D))
      (F09.r92_of_inputs CFSG.LocalAnalysis.UniquenessCase.UCK.k32_holds
          CFSG.AGLEmbedding.kFactCatalogSchreier_holds D) kFactL2EvenThreeElts_holds
      kFact913L2Even_holds CFSG.LocalAnalysis.UniquenessCase.UCK.k462_holds
      CFSG.AGLEmbedding.kFactCatalogSchreier_holds

theorem S168e3Std.r9_24X {D : Data G} (s : S168e3Std D) : R9_24X D :=
  r9_24X_of_r6_3 s.h63

end

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
