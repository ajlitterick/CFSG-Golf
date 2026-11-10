module

import all CFSG.Milestones.ASVolI.F4
public import CFSG.Milestones.ASVolI.F431.JRed2

public section

namespace CFSG.ASVolI

section MixedCent

open Matrix CFSG.Open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl CFSG.QuasithinUnique.Setup.X7a
  CFSG.ASVolI.ChF


end MixedCent

section Burnside

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChF


end Burnside

section CentLe

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChF


end CentLe

section Sp4Gp

open Matrix CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl CFSG.QuasithinUnique.Setup.X7a
  CFSG.ASVolI.ChF CFSG.ASVolI.ChF.ClassicalRoots


end Sp4Gp

end CFSG.ASVolI
