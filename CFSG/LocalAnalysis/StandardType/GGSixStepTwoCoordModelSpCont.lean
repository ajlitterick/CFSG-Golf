module

public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordModelSpContZero
public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordModelSpContClass
public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordShapeSp

public section

namespace CFSG.StandardType


section Certified

theorem ggSpCoordModelNonsplitInput_holds : GGSpCoordModelNonsplitInput :=
  ggSpCoordModelNonsplitInput_of_cont ggSpNsZeroContInput_holds ggSpNsClassContInput_holds


end Certified

end CFSG.StandardType
