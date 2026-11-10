module

public import CFSG.LocalAnalysis.StandardType.GGAssemblyNineDefs
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutNonsplitOm
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutNonsplitFieldSp
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutNonsplitFieldSUDelta
public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordModelSpCont
public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordModelURound8
public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionWitSpBlk
public import CFSG.LocalAnalysis.StandardType.GGSixFieldFiveTags

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

section Lie

@[expose] def GGSixLSixElevenKGRound10 : Prop :=
  (∀ t, ¬ GGOrdPSmallTag t → t ≠ .PSL → t ≠ .PSp → t ≠ .PSU → t ≠ .POmegaPlus →
      t ≠ .POmegaMinus → GGOrdPInnerConjAt t) ∧
    GGOrdPFieldConjPOmegaPlusRest ∧ GGOrdPFieldConjPOmegaMinusNonsplit ∧
    (∀ t, ¬ GGOrdPSmallTag t → t ≠ .PSL → t ≠ .PSp → t ≠ .PSU → t ≠ .POmegaPlus →
      t ≠ .POmegaMinus → GGOrdPFieldConjAt t) ∧
    GGOrdPOutdiagAt .E6 ∧ GGOrdPOutdiagAt .twistedE6 ∧ GGOrdPTrialityInput


theorem ggSixLSixElevenKGRound9_of_round10 (h : GGSixLSixElevenKGRound10) :
    GGSixLSixElevenKGRound9 := by
  obtain ⟨hI, hFOP, hFOM, hF, hO2, hO3, hT⟩ := h
  exact ⟨ggOrdPInnerConjPOmegaPlusNonsplit_holds, ggOrdPInnerConjPOmegaMinusNonsplit_holds, hI,
    ggOrdPFieldConjPSpNonsplit_holds, ggOrdPFieldConjPSURest_holds, hFOP, hFOM, hF, hO2, hO3, hT⟩


end Lie

section FieldFive


end FieldFive

end CFSG.StandardType
