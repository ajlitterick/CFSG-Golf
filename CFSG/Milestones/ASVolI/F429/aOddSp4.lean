module

public import CFSG.Milestones.ASVolI.F429.aOddGen
public import CFSG.Milestones.ASVolI.F429.aC7Sp4
public import CFSG.RankThree.PartTwo.KFacts.AutPSp4Even

public section

namespace CFSG.ASVolI

section Rank

open Matrix CFSG.QuasithinUnique.Lin2.Five


end Rank

section SpModel

open Matrix CFSG.Open CFSG.ASVolI.ChF CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher CFSG.QuasithinUnique.Setup.X7a
  CFSG.QuasithinUnique.Lin2.Five CFSG.ComponentClassification.OuterAutomorphisms


end SpModel

section Main

open CFSG.Open CFSG.ASVolI.ChF CFSG.Quasithin CFSG.ASVolI.ChF.ClassicalRoots
  CFSG.QuasithinUnique.Setup.X7a CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag


end Main

end CFSG.ASVolI
