module

public import CFSG.Milestones.ASVolI.F4
import all CFSG.Milestones.ASVolI.F4

public section

namespace CFSG.ASVolI

open CFSG.Open

section Geometry

open CFSG.Quasithin


end Geometry

section Incl

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
  CFSG.ASVolI.ChF


end Incl

section Transfer

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
  CFSG.ASVolI.ChF


end Transfer

section Assembly

open CFSG.Quasithin CFSG.ASVolI.ChF


end Assembly

section F427

open CFSG.ASVolI.ChF


end F427

section L3

open CFSG.ASVolI.ChF CFSG.ASVolI.ChF.ClassicalRoots


section L3Entries


end L3Entries

section L3Final


end L3Final

end L3

end CFSG.ASVolI
