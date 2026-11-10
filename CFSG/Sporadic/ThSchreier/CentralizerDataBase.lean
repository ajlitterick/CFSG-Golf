
module

public meta import CFSG.Sporadic.ThSchreier.Text
public import CFSG.Sporadic.ThSchreier.CentralizerDataInputs

@[expose] public section

namespace CFSG.Sporadic.ThSchreier

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Th.Max3 Pointwise

@[expose] def transporterWord : List ℤ :=
  [2, 2, 1, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2,
    1, 2, 2]

end CFSG.Sporadic.ThSchreier
