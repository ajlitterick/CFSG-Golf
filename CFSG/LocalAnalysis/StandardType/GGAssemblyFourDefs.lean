module

public import CFSG.LocalAnalysis.StandardType.GGOppositeRadicalSpUPSU
public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsCoresFinal
public import CFSG.LocalAnalysis.StandardType.GGTableBExcRest
public import CFSG.LocalAnalysis.StandardType.GGTableBF4TwoEndNode
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutPSLRestMain
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutGraphAssembly
public import CFSG.LocalAnalysis.StandardType.GGKGroupFusionAltAssembly
public import CFSG.LocalAnalysis.StandardType.GGSixStepThreeCFSeventeenCases
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylB

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

section Lie


@[expose] def GGSecFiveWeylRest4 : Prop :=
  GGSecFiveWeylAInput ∧ GGSecFiveWeylBRestInput ∧ GGSecFiveWeylDInput ∧ GGSecFiveWeylEInput ∧
    GGSecFiveWeylF4Input ∧ GGSecFiveWeylG2Input


end Lie

section Exc


end Exc


section F4

@[expose] def GGTableBOtherRest4NoF4 (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGTableBOtherRest4 p lab ∧ ¬ GGTableBF4AllLabel p lab

theorem ggBstarInputOn_rest4_of_noF4 (h : GGBstarInputOn GGTableBOtherRest4NoF4) :
    GGBstarInputOn GGTableBOtherRest4 :=
  (ggBstarInputOn_F4_all.or h).mono fun p lab _ _ hl => by
    by_cases hF : GGTableBF4AllLabel p lab
    exacts [Or.inl hF, Or.inr ⟨hl, hF⟩]

theorem ggStdSubPreInputOn_rest4_of_noF4 (hE1 : TableBF4Two.GGF4TwoLocalEndNodeInput)
    (hE2 : TableBF4Two.GGF4TwoOuterRankInput) (h : GGStdSubPreInputOn GGTableBOtherRest4NoF4) :
    GGStdSubPreInputOn GGTableBOtherRest4 :=
  ((ggStdSubPreInputOn_F4_all_of_inputs hE1 hE2).or h).mono fun p lab _ _ hl => by
    by_cases hF : GGTableBF4AllLabel p lab
    exacts [Or.inl hF, Or.inr ⟨hl, hF⟩]

end F4

end CFSG.StandardType
