module

public import CFSG.LocalAnalysis.StandardType.GGKGroupFusionSeitzExcLTwoEight
public import CFSG.LocalAnalysis.StandardType.GGKGroupFusionSeitzExcSolv
public import CFSG.LocalAnalysis.StandardType.GGKGroupFusionSeitzExcSz
public import CFSG.LocalAnalysis.StandardType.GGKGroupFusionSeitzExcGenuine
public import CFSG.LocalAnalysis.StandardType.GGKGroupFusionAltAssembly

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.AGLEmbeddingD2

@[expose] def GGSeitzExcInputs : Prop :=
  GGSeitzExcUFourTwoInput ∧ GGSeitzExcTitsThreeInput ∧
    GGSeitzExcTitsFiveInput ∧ GGSeitzExcSpEightOvergroupInput ∧
    GGSeitzExcSpEightCentralizerInput ∧ GGSeitzExcSpSixOvergroupInput ∧
    GGSeitzExcSpSixCentralizerInput ∧ GGSeitzExcLThreeFourOvergroupInput ∧
    GGSeitzExcLThreeFourCentralizerInput

section Assembly


end Assembly

end CFSG.StandardType
