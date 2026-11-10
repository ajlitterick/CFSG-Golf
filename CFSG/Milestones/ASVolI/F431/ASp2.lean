module

public import CFSG.Milestones.ASVolI.F4TISets

public section

namespace CFSG.ASVolI

section Mat

open Matrix CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl CFSG.QuasithinUnique.Setup.X7a
  CFSG.ASVolI.ChF


end Mat

section AntiSp

open Matrix CFSG.ComponentClassification.UnbalancedCatalog.SpChain
  CFSG.QuasithinUnique.Setup.X7b CFSG.RankThree.PartOne.KCRootAxis
  CFSG.QuasithinUnique.Borel252 CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13.F431
  CFSG.Quasithin.H13.F431.SpModel


end AntiSp

section ShapeMap

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431 CFSG.ASVolI.ChF


end ShapeMap

end CFSG.ASVolI
