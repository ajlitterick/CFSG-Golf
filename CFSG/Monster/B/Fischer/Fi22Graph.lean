
module

public import CFSG.Monster.B.Fischer.Fi22GraphBase

public import CFSG.Monster.B.Fischer.Fi22GraphCheck

public noncomputable section

namespace CFSG.Monster.B.Fischer

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

theorem rep_fi22U : Rep 3510 fi22GraphOuterArr fi22U :=
  (rep_permOfArr fi22Graph_check.2).1


end CFSG.Monster.B.Fischer
