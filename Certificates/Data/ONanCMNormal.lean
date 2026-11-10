module

public import Certificates.Data.ONanCMTab

public section

namespace CFSG.OddStandard.ONanRec.CM


@[expose] def invWord (w : List Nat) : List Nat :=
  (w.map fun c => if c % 2 = 0 then c + 1 else c - 1).reverse


end CFSG.OddStandard.ONanRec.CM
