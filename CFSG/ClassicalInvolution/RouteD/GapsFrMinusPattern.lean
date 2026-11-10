module

public import CFSG.ClassicalInvolution.RouteD.GapsFrMinusZ
public import CFSG.ClassicalInvolution.RouteD.GapsFrMinusNodesImg
public import CFSG.ClassicalInvolution.RouteD.TypeTwistedDChain
public import CFSG.ClassicalInvolution.RouteD.TypeTwistedDDischarge

public section

namespace CFSG.ClassicalInvolution.RouteD.Gaps

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.RouteD CFSG.Assembly.LowTwoRank CFSG.LieType CFSG.LieType.Universal
  CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted CFSG.LieType.CurtisTits

local macro "fr_idx" : tactic =>
  `(tactic| first
    | (simp [DNodes.adj_def]; done)
    | (simp [DNodes.adj_def]; omega)
    | (simp; done)
    | (simp; omega)
    | omega)

section Main


end Main

end CFSG.ClassicalInvolution.RouteD.Gaps
