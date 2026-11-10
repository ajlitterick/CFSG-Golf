module

public import CFSG.Assembly.StandardTypeRecognitionDefs
public import CFSG.Yardstones.M3f9567aba59d.Reduction
import CFSG.Assembly.E6FourCentHolds
import CFSG.Assembly.E6FourFieldRigid
import CFSG.Assembly.E6FourLabelArith
import CFSG.LocalAnalysis.GLTheoremA.CatA.CentQChar2Index
import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompIdxLinear
import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompIdxUnitary
import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompIdxClassical
import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompIdxTriality
import CFSG.LocalAnalysis.StandardType.MarkingDict
import CFSG.Assembly.E6FourLemma55
import CFSG.Assembly.E6FourNeighbourFacts
import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrder
import CFSG.LocalAnalysis.StandardType.GGReverseMarkingRaw
import CFSG.LocalAnalysis.StandardType.GGTwE6SCFourCoverMark
import CFSG.LocalAnalysis.StandardType.Marking
import CFSG.LieType.Chevalley.ExceptionalLargeEvenCoverTorus
import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotHR6X
import CFSG.LieType.Chevalley.GraphFixedFinitePerfect
import CFSG.LieType.Chevalley.GraphFixedCenterTrivial
import CFSG.LieType.Chevalley.GraphFixedParameterFields
import CFSG.LocalAnalysis.SectionRank.ClassicalEven.Torus
import CFSG.HardMathSupport.Solomon.Coordinator.LayerCentralFix
import CFSG.Assembly.E6FourCoverQuot
import CFSG.Assembly.Subnormal
import CFSG.LieType.Steinberg.CentralExt.GriessNativeModels
import CFSG.LocalAnalysis.StandardType.GGNbrCenterPCyclicHolds
import CFSG.LieType.Steinberg.CentralExt.PSUMultiplier
import CFSG.LieType.Steinberg.CentralExt.SUOddClosed
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyEvenOrthogonal
import CFSG.GH74.Filter.Orthogonal.EvenEichler
import CFSG.Timmesfeld.Orders.ClassicalOrthogonal
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointIsometryRegular
import CFSG.LocalAnalysis.StandardType.GGTableBOrthogonalBasic
import CFSG.LieType.Steinberg.CentralExt.GriessClassical
import CFSG.LocalAnalysis.StandardType.MarkingClassical
import CFSG.LocalAnalysis.StandardType.GGRoundFourSmallBIsoAssembly
import CFSG.LocalAnalysis.StandardType.GGInndiagCommRest
import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompIdxExc2
import CFSG.Yardstones.M3f9567aba59d.Goals

public section

universe u v w

namespace CFSG.Assembly.LargeEven

open scoped MatrixGroups in
theorem _root_.CFSG.Milestones.lc_gl_standard_type_lie_char_two_recognition_rank_four
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hK : KProper InCatalog G) (hchar : IsCharTwoType G)
    (he : 4 ≤ evenRank G) (p : ℕ) (hp : p ∈ LargeEvenBeta 4 G) (B : Subgroup G) (x : G)
    (L : Subgroup G) (hS : LargeEvenSStar p B x L) (hst : LargeEvenStandardType p B x L) :
    InLieTypeCharTwoCatalog G :=
  CFSG.Yardstones.M3f9567aba59d.lc_gl_standard_type_lie_char_two_of_yardstones
    CFSG.Yardstones.M3f9567aba59d.ggRemainderStdSubTableB_holds
    CFSG.Yardstones.M3f9567aba59d.ggRemainderTableBL_holds
    CFSG.Yardstones.M3f9567aba59d.ggRemainderCoxeterLabel_holds
    CFSG.Yardstones.M3f9567aba59d.ggRemainderSecFiveWeyl_holds
    CFSG.Yardstones.M3f9567aba59d.ggRemainderSecFiveTypeA_holds
    CFSG.Yardstones.M3f9567aba59d.ggRemainderSecFiveHalfSp_holds
    CFSG.Yardstones.M3f9567aba59d.ggRemainderCorFiveTwenty_holds
    CFSG.Yardstones.M3f9567aba59d.ggRemainderStepOneExc_holds
    CFSG.Yardstones.M3f9567aba59d.ggRemainderStepOneConfig_holds
    CFSG.Yardstones.M3f9567aba59d.ggRemainderStepTwo_holds
    CFSG.Yardstones.M3f9567aba59d.ggRemainderRootCentralizer_holds
    CFSG.Yardstones.M3f9567aba59d.ggRemainderStepThreeExc_holds
    CFSG.Yardstones.M3f9567aba59d.kFactSeitzRankTwo_holds
    CFSG.Yardstones.M3f9567aba59d.holtUniqueFixedPointSimple_holds
    G hnonab hK hchar he p hp B x L hS hst

open scoped MatrixGroups in
theorem _root_.CFSG.Milestones.lc_gl_standard_type_recognition_rank_four
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hK : KProper InCatalog G) (hchar : IsCharTwoType G)
    (he : 4 ≤ evenRank G) (p : ℕ) (hp : p ∈ LargeEvenBeta 4 G) (B : Subgroup G) (x : G)
    (L : Subgroup G) (hS : LargeEvenSStar p B x L) (hst : LargeEvenStandardType p B x L) :
    InCatalog G :=
  inCatalog_of_inLieTypeCharTwoCatalog G
    (CFSG.Milestones.lc_gl_standard_type_lie_char_two_recognition_rank_four
      G hnonab hK hchar he p hp B x L hS hst)

end CFSG.Assembly.LargeEven
