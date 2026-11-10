module

public import CFSG.LocalAnalysis.StandardType.GGAssemblySevenDefs
public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordShapeSL
public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordShapeSp
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutClassicalOmRest
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutOutdiag
public import CFSG.LocalAnalysis.StandardType.GGSpNonsplitFrame
public import CFSG.LocalAnalysis.StandardType.GGSixBstarOrthFrameD4
public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitKGClHerm
public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitKGClAltSix

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

section Lie

@[expose] def GGStepTwoToralRound8 : Prop :=
  GGSpCoordModelNonsplitInput ∧ GGStepTwoCoordModelOn .PSU ∧ GGStepTwoCoordModelOn .POmegaPlus ∧
    GGStepTwoCoordModelOn .POmegaMinus ∧ GGStepTwoToralWitnessRestInput

theorem ggStepTwoToralRound5_of_round8 (h : GGStepTwoToralRound8) : GGStepTwoToralRound5 :=
  ⟨ggStepTwoCoordModelOn_PSL_holds, h.2.1, ggStepTwoCoordModelOn_PSp_of_nonsplit h.1, h.2.2.1,
    h.2.2.2.1, h.2.2.2.2⟩

theorem ggSixBstarNoOffenderRestOm_of_round8 (h : GGSixBstarNoOffenderAt .F4 ∧
    GGSixBstarNoOffenderAt .E6 ∧ GGSixBstarNoOffenderAt .E7 ∧ GGSixBstarNoOffenderAt .E8 ∧
    GGSixBstarNoOffenderAt .twistedE6) :
    GGSixBstarNoOffenderRestOm :=
  ggSixBstarNoOffenderRestOm_of_rest ggSixBstarNoOffenderOn_PSpNonsplit h.1 h.2.1 h.2.2.1 h.2.2.2.1
    h.2.2.2.2


end Lie

section Exc


end Exc

section NonsplitCX


end NonsplitCX

end CFSG.StandardType
