module

public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL45RestTorus
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL45ConfigAssembly
public import CFSG.LocalAnalysis.StandardType.GGRecipeField

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggRawPCyclicOn_notD4Three_of_split
    (hdone : GGRawPCyclicOn fun _ => GGRawPCyclicDoneLabel)
    (h : GGRawPCyclicOn fun p lab => GGNotD4Three p lab ∧ ¬ GGRawPCyclicDoneLabel lab) :
    GGRawPCyclicOn GGNotD4Three := fun p hp hp2 lab hlab hne => by
  by_cases hd : GGRawPCyclicDoneLabel lab
  · exact hdone p hp hp2 lab hlab hd
  · exact h p hp hp2 lab hlab ⟨hne, hd⟩


end CFSG.StandardType

end
