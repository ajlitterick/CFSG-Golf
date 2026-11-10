module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5BadEight510
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5CentralCard510
import Certificates.Kernel.LocalComp.L34T3.Glue
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Lemma510
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitL34OrbitStep
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitL34PairStep
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitL34TypeWeak
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SKuClosed58
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SKuClosed59P
public import CFSG.Quasithin.H13.J4Order

public section

namespace CFSG.ComponentClassification.GrSLit.GrS5

open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

theorem l34Lemma510_of_prop41_ku
    (hS : SchreierFor Blueprint.Catalog) (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome)
    (hMax : MaximalTwoComponentInput) (hRank : OddStandard.RankTwoL3FourStandard)
    (hCIT : StandardRecognition.ClassicalInvolutionTheoremModels)
    (hEven : OddStandard.L34CyclicEvenCenter) (hComp : L34Cor217ComponentStep)
    (hKu : GrS5S.L34Sec5KuOddStep) (hCard : L34Lemma510CentralCardStep)
    (hBadE : L34Lemma510BadEightStep) (h41 : L34Prop41) :
    L34Lemma510 := by
  have hHeldInput' := KProperRelativeB.heldInput
  have hSolomonCommutingCoreInput' := solomonCommutingCoreInput
  have hGorensteinWalterConnectedInput' := gorensteinWalterConnectedInput
  have hInvolutionCentralizerFact' := L34Facts.l34InvolutionCentralizerFact
  have hSec5ComponentInvariantStep' := l34Sec5ComponentInvariantStep_of_comp hMax hComp
  have hLemma58' := l34Lemma58_closed_ku hS hU hMax hSec5ComponentInvariantStep' hKu
  have hLemma59' := l34Lemma59_of_prop41_ku hS hU hMax hRank hCIT hEven hComp hKu h41
  have hElementaryCenterSylowFact' := l34ElementaryCenterSylowFact
  have hElementaryRankFact' := l34ElementaryRankFact
  have hMaxElementaryThreeFact' := l34MaxElementaryThreeFact
  have hUnbalancingUnitaryStep' := L34Facts.l34UnbalancingUnitaryStep
  have hUnitaryAutFact' := HSFLit.AutL34.l34UnitaryAutFact
  have hL2UnbalancingAutFact' := HSFLit.AutL2.l2UnbalancingAutFact
  have hSylowCentralLiftFact' := l34SylowCentralLiftFact
  have hAutSylowCenterFact' := HSFLit.AutL34.l34AutSylowCenterFact
  have hStandardEvenInput' := GSThmB.l34StandardEvenInput_of_cases hRank hCIT
    OddStandard.oddLieNoStandardL34_holds hEven
  have hLemma510CentralStep' := l34Lemma510CentralStep_of_card hS hU hHeldInput'
    hSolomonCommutingCoreInput' hGorensteinWalterConnectedInput' hMax hInvolutionCentralizerFact'
    hCard
  have hLemma510OTwoBoundStep' := l34Lemma510OTwoBoundStep_of_badEight hS hU hHeldInput' hMax hComp
    hBadE
  have hLemma55TypeStep' := HSFLit.L34Inv.l34Lemma55TypeStep_of_inputs hS hU hHeldInput'
    hSolomonCommutingCoreInput' hGorensteinWalterConnectedInput'
  have hLemma511CenterStep' := HSFLit.L34Uniq.l34Lemma511OrbitStep_of_inputs hS hU hHeldInput'
    hSolomonCommutingCoreInput' hGorensteinWalterConnectedInput' hMax hInvolutionCentralizerFact'
  have hLemma511PairStep' := HSFLit.L34Uniq.l34Lemma511PairStep_of_inputs hS hU hHeldInput'
    hSolomonCommutingCoreInput' hGorensteinWalterConnectedInput' hMax hInvolutionCentralizerFact'
  exact l34Lemma510_of_inputs hS hU hHeldInput' hSolomonCommutingCoreInput'
    hGorensteinWalterConnectedInput' hMax hInvolutionCentralizerFact' hLemma58' hLemma59'
    hElementaryCenterSylowFact' hElementaryRankFact' hMaxElementaryThreeFact'
    hUnbalancingUnitaryStep' hUnitaryAutFact' hComp hL2UnbalancingAutFact' hSylowCentralLiftFact'
    hAutSylowCenterFact' hStandardEvenInput' h41 hLemma510CentralStep' hLemma510OTwoBoundStep'
    hLemma55TypeStep' hLemma511CenterStep' hLemma511PairStep'

end CFSG.ComponentClassification.GrSLit.GrS5
