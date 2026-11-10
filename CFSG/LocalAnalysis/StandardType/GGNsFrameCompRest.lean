module

public import CFSG.LocalAnalysis.StandardType.GGNsFrameCompPSU
public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitKGClHerm
public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitKGClAltSix

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21

section Inputs

@[expose] def GGSixSeventeenWitnessRest9 : Prop :=
  GGSixSeventeenWitnessDvdOn GGPSpNonsplit ∧
    GGSixSeventeenWitnessDvdOn (fun t _ _ _ => t = .POmegaPlus) ∧
    GGSixSeventeenWitnessDvdOn (fun t _ _ _ => t = .POmegaMinus) ∧
    GGSixSeventeenE8SevenInput ∧ GGSixSeventeenRootWitnessInputFor GGExceptionalTag


theorem ggSixSeventeenWitnessRest8_of_rest9 (h : GGSixSeventeenWitnessRest9) :
    GGSixSeventeenWitnessRest8 :=
  ⟨ggSixSeventeenWitnessDvdOn_PSUNonsplit, h⟩

end Inputs

section Wiring


theorem ggSixSeventeenWitnessInput_of_rest9 (hPl : GGNonsplitTag .POmegaPlus)
    (hMi : GGNonsplitTag .POmegaMinus) (h : GGSixSeventeenWitnessRest9) :
    GGSixSeventeenWitnessInputFor fun _ => True :=
  ggSixSeventeenWitnessInput_of_rest8 ggNonsplitTag_PSU_holds ggNonsplitTag_PSp_holds hPl hMi
    (ggSixSeventeenWitnessRest8_of_rest9 h)

end Wiring

end CFSG.StandardType
