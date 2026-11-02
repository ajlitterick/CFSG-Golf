module

public import CFSG.Yardstones.Md42047359a2a.Goals
public import CFSG.Yardstones.Md42047359a2a.Reduction
public import CFSG.Sporadic.Schreier.LyCheckSep
public import CFSG.Sporadic.Ly.KeySpec
public import CFSG.Sporadic.He.FpSpec
import Certificates.Kernel.SporSch.Ly.SepGlue
public import CFSG.Monster.Existence.StdOdd.Defs
public import Certificates.Data.CFSGNative.Chevalley.C2E6CertLie
public import CFSG.LieType.Chevalley.C2E6StdMatrixData
public import CFSG.Monster.B.Classical.E6AdjointGroup
import Certificates.Kernel.Misc.E6StdSlp
public import CFSG.YGroups.Y443.Native.CoverFactsWords
import Certificates.Kernel.KDense.Y443
public import CFSG.YGroups.Y443.Native.Swap13Word
public import CFSG.Sporadic.Ly.FiveFacts
import CFSG.Sporadic.Ly.Certificate
public import CFSG.CGT.PushingUpLit.CGT6.EmbLift
public import CFSG.CGT.PushingUpLit.CGT6.SixFour
public import CFSG.CGT.PushingUpLit.CGT6.SixSixteen
public import CFSG.CGT.PushingUpLit.Glue.ClassXBasic
public import CFSG.CGT.PushingUpLit.Glue.RadicalSylow
public import CFSG.GH74.GLS.IVK.Proofs2.Lemma12hb
public import CFSG.GH74.GLS.IVK.Proofs2.Lemma13d
public import CFSG.GH74.GLS.IVK.Proofs2.Lemma13e
public import CFSG.GH74.GLS.IVK.Proofs2.Lemma13g
public import CFSG.HardMathSupport.Solomon.Coordinator.I19SporCrit
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterElevenEbarData
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThirteenEbarData
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Census219.M24Tc
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J4CentCEHj
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J4RRep
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J4TI
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSporadicCasesC
public import CFSG.LocalAnalysis.ComponentClassification.Foote5CoreBalB
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitFixedA7
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListAlt7
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureSporB
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureSporSuz
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureSporTh
public import CFSG.Monster.B.TwoA.Base.FourNorm
public import CFSG.Monster.SteinbergMY443SimpleIsomorphism
public import CFSG.Quasithin.Vol2.KGFactC31RuRef
public import CFSG.Quasithin.Vol2.KGFactC31RuRefBase
public import CFSG.RankThree.Native.Fi22FiveCheckInputs
public import CFSG.RankThree.PartOne.KLR.Final
public import CFSG.RankThree.PartOne.KS.HeSevenCheck
public import CFSG.RankThree.PartOne.N143.QEqual
public import CFSG.RankThree.PartOne.S12.Sec159Defs
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoOtherDefs
public import CFSG.RankThree.PartTwo.Sec8.Steps
public import CFSG.Sporadic.HeldB.AllFixed
public import Certificates.Data.HSFiveCheck

public section

namespace CFSG.Yardstones.Md42047359a2a

theorem lBalance_of_goals
    : CFSG.Open.LBalanceStatement :=
  milestone_of_yardstones
    alternatingTwoBp_holds
    sporadicMathieuLeechBp_holds
    sporadicMonsterSectionBp_holds
    sporadicPariahBp_holds
    lieSemisimpleCentLinearUnitary_holds
    lieSemisimpleCentSymplecticOrthogonal_holds
    lieSemisimpleCentExceptional_holds
    lieSemisimpleCentSuzukiReeTits_holds
    lieDefCharOuter_holds
    lieClassicalOddCharTwoBp_holds
    lieExceptionalOddCharTwoBp_holds
    lieEvenCharTwoBp_holds
    elementCaseBp_holds

end CFSG.Yardstones.Md42047359a2a
