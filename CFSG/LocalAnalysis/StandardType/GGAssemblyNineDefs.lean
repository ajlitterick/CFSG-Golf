module

public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutNonsplitRest
public import CFSG.LocalAnalysis.StandardType.GGSixAutKFinerTagsAssembly
public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitKGOmRound8
public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionWitSpNsBlock
public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionWitOmRest
public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordModelSpNsComp

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

section Lie

@[expose] def GGSixLSixElevenKGRound9 : Prop :=
  GGOrdPInnerConjPOmegaPlusNonsplit ∧ GGOrdPInnerConjPOmegaMinusNonsplit ∧
    (∀ t, ¬ GGOrdPSmallTag t → t ≠ .PSL → t ≠ .PSp → t ≠ .PSU → t ≠ .POmegaPlus →
      t ≠ .POmegaMinus → GGOrdPInnerConjAt t) ∧
    GGOrdPFieldConjPSpNonsplit ∧ GGOrdPFieldConjPSURest ∧ GGOrdPFieldConjPOmegaPlusRest ∧
    GGOrdPFieldConjPOmegaMinusNonsplit ∧
    (∀ t, ¬ GGOrdPSmallTag t → t ≠ .PSL → t ≠ .PSp → t ≠ .PSU → t ≠ .POmegaPlus →
      t ≠ .POmegaMinus → GGOrdPFieldConjAt t) ∧
    GGOrdPOutdiagAt .E6 ∧ GGOrdPOutdiagAt .twistedE6 ∧ GGOrdPTrialityInput


theorem ggSixLSixElevenKGRest9_of_round9 (h : GGSixLSixElevenKGRound9) :
    GGSixLSixElevenKGRest9 := by
  obtain ⟨hOP, hOM, hI, hFSp, hFU, hFOP, hFOM, hF, hO2, hO3, hT⟩ := h
  exact ⟨hOP, hOM, hI, hFSp, hFU, hFOP, hFOM, hF, ggOrdPOutdiagAt_PSU, hO2, hO3, hT⟩


@[expose] def GGLayerNotDFourTwoRound9 : Prop :=
  GGLayerNotDFourTwoTag .F4 ∧ GGLayerNotDFourTwoTag .E6 ∧ GGLayerNotDFourTwoTag .E7 ∧
    GGLayerNotDFourTwoTag .E8 ∧ GGLayerNotDFourTwoTag .twistedE6

@[expose] def GGLayerNotUFourAltSixRound9 : Prop :=
  GGLayerNotUFourAltSixTag .F4 ∧ GGLayerNotUFourAltSixTag .E6 ∧ GGLayerNotUFourAltSixTag .E7 ∧
    GGLayerNotUFourAltSixTag .E8 ∧ GGLayerNotUFourAltSixTag .twistedE6


end Lie

section Exc

theorem ggSixLSixElevenKGInput_of_round9 (h : GGSixLSixElevenKGRound9) :
    GGSixLSixElevenKGInput :=
  ggSixLSixElevenKGInput_of_rest9 (ggSixLSixElevenKGRest9_of_round9 h)

end Exc

section NonsplitCX


end NonsplitCX

end CFSG.StandardType
