module

public import CFSG.LocalAnalysis.StandardType.GGSixSeventeenWitSL
public import CFSG.LocalAnalysis.StandardType.GGSixSeventeenWitSU
public import CFSG.LocalAnalysis.StandardType.GGSixSeventeenWitSp

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21

section Inputs

@[expose] def GGSixSeventeenWitnessRest6 : Prop :=
  GGSixSeventeenWitnessOn GGPSLNonsplit ∧ GGSixSeventeenWitnessOn GGPSUNonsplit ∧
    GGSixSeventeenWitnessOn GGPSpNonsplit ∧
    GGSixSeventeenWitnessOn (fun t _ _ _ => t = .POmegaPlus) ∧
    GGSixSeventeenWitnessOn (fun t _ _ _ => t = .POmegaMinus) ∧
    GGSixSeventeenE8SevenInput ∧ GGSixSeventeenRootWitnessInputFor GGExceptionalTag

theorem ggSixSeventeenWitnessInputFor_linearUnitary_of_nonsplit
    (hSLn : GGSixSeventeenWitnessOn GGPSLNonsplit) (hSUn : GGSixSeventeenWitnessOn GGPSUNonsplit) :
    GGSixSeventeenWitnessInputFor GGLinearUnitaryTag :=
  ggSixSeventeenWitnessInputFor_linearUnitary_of_on ggSixSeventeenWitnessOn_PSLSplit hSLn
    ggSixSeventeenWitnessOn_PSUSplit hSUn

theorem ggSixSeventeenWitnessOn_PSp_of_nonsplit (hSpn : GGSixSeventeenWitnessOn GGPSpNonsplit) :
    GGSixSeventeenWitnessOn fun t _ _ _ => t = .PSp :=
  ggSixSeventeenWitnessOn_of_split (Q := fun _ _ f p => p ∣ 2 ^ f - 1)
    ggSixSeventeenWitnessOn_PSpSplit hSpn

theorem ggSixSeventeenWitnessInput_of_rest6 (h : GGSixSeventeenWitnessRest6) :
    GGSixSeventeenWitnessInputFor fun _ => True := by
  obtain ⟨hSLn, hSUn, hSpn, hPlus, hMinus, hE8, hex⟩ := h
  exact ggSixSeventeenWitnessInput_of_families
    (ggSixSeventeenWitnessInputFor_linearUnitary_of_nonsplit hSLn hSUn)
    (ggSixSeventeenWitnessInputFor_otherClassical_of_on
      (ggSixSeventeenWitnessOn_PSp_of_nonsplit hSpn) hPlus hMinus)
    (ggSixSeventeenWitnessInputFor_of_root hE8 hex)


end Inputs

end CFSG.StandardType
