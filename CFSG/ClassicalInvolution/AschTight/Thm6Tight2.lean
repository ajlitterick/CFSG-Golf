module

public import CFSG.ClassicalInvolution.AschTight.C195Main
public import CFSG.ClassicalInvolution.AschTight.E2StarTargets
public import CFSG.ClassicalInvolution.AschTight.Sec19Targets2
public import CFSG.ClassicalInvolution.Asc77.AscL62Final

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77

variable (p f : ℕ) [Fact p.Prime]

theorem l6_2ModTmp : L6_2ModTmp p f :=
  Asc77.l6_2 p f


end CFSG.ClassicalInvolution.Disconnected.AschTight
