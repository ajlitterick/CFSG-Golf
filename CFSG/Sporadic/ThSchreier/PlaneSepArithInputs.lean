module

public import CFSG.Sporadic.ThSchreier.PlaneSepData
public import CFSG.Sporadic.Th.FormBase
public meta import CFSG.Sporadic.ThSchreier.PlaneSepData
public meta import CFSG.Sporadic.Th.FormBase

public section

namespace CFSG.Sporadic.ThSchreier

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Th.Max3 CFSG.Sporadic.Th.FormBase
  Pointwise Matrix

@[expose] def sepGramRows : Array V4 :=
  mulRows (mulRows sepCRows sepFRows) (transposeRows sepCRows)


@[expose] def sepTree : List ℕ := natsOf (include_str "Data/SepTree.txt")


end CFSG.Sporadic.ThSchreier
