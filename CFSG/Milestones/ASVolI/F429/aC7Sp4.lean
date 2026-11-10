module

public import CFSG.Milestones.ASVolI.F429.aC7Gen
import all CFSG.Milestones.ASVolI.F4

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.ASVolI.ChF CFSG.Quasithin

section Sp4Model

open Matrix CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.X7a
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl


end Sp4Model

section Sp4Final

open Matrix CFSG.ASVolI.ChF.ClassicalRoots CFSG.QuasithinUnique.Setup.X7a
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl


end Sp4Final

end CFSG.ASVolI
