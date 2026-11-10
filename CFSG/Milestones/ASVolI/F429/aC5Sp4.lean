module

public import CFSG.Milestones.ASVolI.F429.aR5Gen
public import CFSG.Milestones.ASVolI.F429.Defs
public import CFSG.Milestones.ASVolI.F429.aC3
public import CFSG.Milestones.ASVolI.F429.aC4Gen
public import CFSG.Milestones.ASVolI.F429.aOddGen
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsSpAut

public section

namespace CFSG.ASVolI

section SpModel

open Matrix CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.Quasithin.SteinbergBS
  CFSG.QuasithinUnique.Fin257.Sp4 CFSG.RankThree.PartOne.KCRootAxis CFSG.Quasithin.H13.F431
  CFSG.Quasithin.H13.F431.SpOut2 CFSG.Quasithin.H13.F431.SpModel CFSG.Quasithin.H13.Sec53F
  CFSG.Open CFSG.ASVolI.ChF CFSG.Quasithin


end SpModel

section Key

open CFSG.Open CFSG.ASVolI.ChF CFSG.Quasithin
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.Quasithin.H13.F431
  CFSG.Quasithin.H13.F431.SpModel CFSG.Quasithin.H13.Sec53F CFSG.Quasithin.H13.F431.SpOut2
  CFSG.RankThree.PartOne.KCRootAxis


end Key

end CFSG.ASVolI
