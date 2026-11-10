module

public import CFSG.Quasithin.Background.C1PackS1461Five
public import CFSG.Quasithin.Background.C1PackS14612One
public import CFSG.Quasithin.EmptyFaithful.S146E12
public import CFSG.Quasithin.EmptyFaithful.S146GoldA

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

theorem stageSection146_of_inputs_two_central (h1413 : StageLemma1413) (h11 : StageLemma14111)
    (h113 : StageLemma14113) (hcab : GoldschmidtCentralAbelianBound)
    (hA : Stage146BranchACore) (hB : Stage146BranchBCore) (h9 : Stage1469)
    (h105 : Stage14610Five) (h6 : Stage1461Six) (h634 : Stage1463Four) : StageSection146 :=
  stageSection146_of_inputs_central h11 h113 hcab hA hB h9 h105 stage1463_one_proof (stage1463_two_of h6)
    (stage1463_three_proof h1413) h634

end CFSG.Quasithin
