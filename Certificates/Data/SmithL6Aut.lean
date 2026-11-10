module

public import Certificates.Data.SmithL6Orbit

public section

namespace CFSG.SmithL6

@[expose] def dualIdx (i : Nat) : Nat :=
  ((List.range 1395).find? fun j => maskArr[j]! == annArr[i]!).getD 1395

@[expose] def chkSwapPlanes : Bool :=
  (List.range 1395).all fun i => let j := dualIdx i
    decide (j < 1395) && maskArr[j]! == annArr[i]! && annArr[j]! == maskArr[i]!


@[expose] def chkPtFix : Bool :=
  (List.range 1953).all fun b => b == 0 ||
    (List.range 1953).any fun q => tvTab[q]![0]! == 0 && tvTab[q]![b]! != b

end CFSG.SmithL6
