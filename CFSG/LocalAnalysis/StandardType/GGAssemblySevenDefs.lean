module

public import CFSG.LocalAnalysis.StandardType.GGAssemblySixDefs
public import CFSG.LocalAnalysis.StandardType.GGLayerCycModelLabels
public import CFSG.LocalAnalysis.StandardType.GGLayerCycModelOmegaInnerSU33
public import CFSG.LocalAnalysis.StandardType.GGTableBE6ThreeEndRecipe
public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordModelSLComp
public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordModelSp
public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordModelSpComp
public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordContrary
public import CFSG.LocalAnalysis.StandardType.GGSixAutKFinerTailAssembly
public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitKGSLTag
public import CFSG.LocalAnalysis.StandardType.GGSixBstarNoOffenderPSLRest

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank


section LayerCentre


end LayerCentre

section TableBE6

theorem ggStdSubPreInputOn_round5_of_round7 (hT : E6ThreeEnd.GGE6TwoToralInput)
    (hL : E6ThreeEnd.GGE6TwoLayerInput) (h : GGStdSubPreInputOn GGTableBOtherRound6) :
    GGStdSubPreInputOn GGTableBOtherRound5 :=
  ((ggStdSubPreInputOn_E6_three_of_twoInputs hT hL).or h).mono_split fun p lab hR hs => by
    by_cases hE6 : lab.tag = .E6 ∧ p = 3
    · exact Or.inl (ggTableBE6LabelThree_of_split hE6.1 hE6.2 hs)
    · exact Or.inr ⟨hR, hE6⟩

end TableBE6

section TableB

theorem ggStdSubPreInputOn_rest4_of_round7 (hT : E6ThreeEnd.GGE6TwoToralInput)
    (hL : E6ThreeEnd.GGE6TwoLayerInput) (hS : TableBExcSmallRanks.GGTwF4ThreeRankInput)
    (h : GGStdSubPreInputOn GGTableBOtherRound6) : GGStdSubPreInputOn GGTableBOtherRest4 :=
  ggStdSubPreInputOn_rest4_of_round5 TableBF4TwoInputs.ggF4TwoLocalEndNodeInput_holds
    TableBF4TwoInputs.ggF4TwoOuterRankInput_holds
    ⟨ggE7TwoRootFusionInput_holds, ggE8TwoRootFusionInput_holds⟩
    (ggTableBSmallRankRound5_of_round6 hS) (ggStdSubPreInputOn_round5_of_round7 hT hL h)

end TableB

section StepTwo


@[expose] def GGLayerNotDFourTwoRound7 : Prop :=
  GGLayerNotDFourTwoTag .PSU ∧ GGLayerNotDFourTwoTag .PSp ∧ GGLayerNotDFourTwoTag .POmegaPlus ∧
    GGLayerNotDFourTwoTag .POmegaMinus ∧ GGLayerNotDFourTwoTag .F4 ∧ GGLayerNotDFourTwoTag .E6 ∧
      GGLayerNotDFourTwoTag .E7 ∧ GGLayerNotDFourTwoTag .E8 ∧ GGLayerNotDFourTwoTag .twistedE6


end StepTwo

section NoOffender


end NoOffender

section NonsplitCX


end NonsplitCX

section NonsplitCXTags


end NonsplitCXTags

end CFSG.StandardType
