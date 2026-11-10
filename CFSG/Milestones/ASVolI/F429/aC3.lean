module

public import CFSG.Milestones.ASVolI.F429.Base
public import CFSG.Milestones.ASVolI.F429.aU5Chart
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtRk2ExtSp4
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtRk2ExtL3
import all CFSG.Milestones.ASVolI.F4

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.ASVolI.ChF CFSG.Quasithin

section Generic


end Generic

section U4

open CFSG.ClassicalGroups.UnitaryFlag CFSG.Quasithin.H13.U4Par


end U4

section Sp4

open CFSG.QuasithinUnique.Setup.X7a CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag


end Sp4

section L3

open CFSG.ASVolI.ChF.ClassicalRoots CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.QuasithinUnique.Setup.X7a


end L3

section U5

open CFSG.ClassicalGroups.UnitaryFlag CFSG.Quasithin.H13.Sec53F.Unit


end U5

section Classical


end Classical

end CFSG.ASVolI
