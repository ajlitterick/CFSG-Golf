module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf10Beta
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf9Seven
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf10Prim5
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf10Prim6
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf10Prim7
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf9Aut

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TC CFSG.ClassicalInvolution.Q3.TC.Graph
  CFSG.ClassicalInvolution.Q3.TC.Thin
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

set_option linter.unusedSectionVars false

namespace TwinThinPf10


theorem aeBlocks_small {n : ℕ} (hn5 : 5 ≤ n) (hn7 : n ≤ 7) : AEBlocks' n := by
  refine aeBlocks_of_prim hn5 hn7 ?_
  interval_cases n
  · exact fourSetPrim_five
  · exact fourSetPrim_six
  · exact fourSetPrim_seven

end TwinThinPf10

namespace TwinThin


namespace Setting


end Setting

end TwinThin

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
