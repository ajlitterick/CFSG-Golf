module

import Certificates.Kernel.LocalComp.L34T3.Glue
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SCentral
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SBadCover
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SCoverProof
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SKuClosed511P

public section

namespace CFSG.ComponentClassification.GrSLit.GrS5S

open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

theorem l34Lemma511_closedQ_ku
    (hS : SchreierFor Blueprint.Catalog) (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome)
    (hMax : MaximalTwoComponentInput) (hRank : OddStandard.RankTwoL3FourStandard)
    (hCIT : StandardRecognition.ClassicalInvolutionTheoremModels)
    (hEven : OddStandard.L34CyclicEvenCenter) (hComp : L34Cor217ComponentStep)
    (hKu : L34Sec5KuOddStep) (h41 : L34Prop41) :
    L34Lemma511 := by
  have h58 := GrS5.l34Lemma58_closed_ku hS hU hMax
    (GrS5.l34Sec5ComponentInvariantStep_of_comp hMax hComp) hKu
  have h59 := GrS5.l34Lemma59_of_prop41_ku hS hU hMax hRank hCIT hEven hComp hKu h41
  have hCov := l34Lemma510CoverInvolutionStep_of_inputs hS hU KProperRelativeB.heldInput
    solomonCommutingCoreInput gorensteinWalterConnectedInput hMax
    L34Facts.l34InvolutionCentralizerFact h58 h59 HSFLit.AutL34.l34AutSylowCenterFact hComp
    (HSFLit.L34Inv.l34Lemma55TypeStep_of_inputs hS hU KProperRelativeB.heldInput
      solomonCommutingCoreInput gorensteinWalterConnectedInput)
    L34Facts.l34UnbalancingUnitaryStep
  exact GrS5.l34Lemma511_of_prop41_ku hS hU hMax hRank hCIT hEven hComp hKu
    (l34Lemma510CentralCardStep_of_moves hS hU KProperRelativeB.heldInput solomonCommutingCoreInput
      gorensteinWalterConnectedInput hMax L34Facts.l34InvolutionCentralizerFact h58 h59
      HSFLit.AutL34.l34AutSylowCenterFact hComp)
    (l34Lemma510BadEightStep_of_cover hS hU KProperRelativeB.heldInput solomonCommutingCoreInput
      gorensteinWalterConnectedInput hMax L34Facts.l34InvolutionCentralizerFact h58 h59
      HSFLit.AutL34.l34AutSylowCenterFact L34Facts.l34UnbalancingUnitaryStep
      HSFLit.AutL34.l34UnitaryAutFact l34ElementaryRankFact l34MaxElementaryThreeFact hCov) h41

end CFSG.ComponentClassification.GrSLit.GrS5S
