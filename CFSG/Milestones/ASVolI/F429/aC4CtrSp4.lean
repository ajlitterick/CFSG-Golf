module

public import CFSG.Milestones.ASVolI.F429.aC4Gen
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsSpAut

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.ASVolI.ChF CFSG.Quasithin

section Generic


end Generic

section SpModel

open Matrix CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.Quasithin.SteinbergBS
  CFSG.QuasithinUnique.Fin257.Sp4 CFSG.RankThree.PartOne.KCRootAxis CFSG.Quasithin.H13.F431
  CFSG.Quasithin.H13.F431.SpOut2 CFSG.Quasithin.H13.F431.SpModel CFSG.Quasithin.H13.Sec53F


end SpModel

section Sp4

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.Quasithin.H13.F431
  CFSG.Quasithin.H13.F431.SpModel CFSG.Quasithin.H13.Sec53F


end Sp4

end CFSG.ASVolI
