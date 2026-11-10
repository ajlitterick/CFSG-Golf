module

public import CFSG.Milestones.ASVolI.F429.aC2cU4Mat
import all CFSG.Milestones.ASVolI.F4
public import CFSG.Milestones.ASVolI.F429.aC5corrU4

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.ASVolI.ChF CFSG.Quasithin

section Generic


end Generic

section Rank


end Rank

section U4Model

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.Quasithin.H13.U4Par CFSG.Quasithin.H13.Sec53F.Unit


end U4Model

section Chart

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.Quasithin.H13.U4Par CFSG.ASVolI.ChF.ClassicalRoots


end Chart

end CFSG.ASVolI
