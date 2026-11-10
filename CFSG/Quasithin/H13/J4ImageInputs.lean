module

public import CFSG.Quasithin.H13.J4Quot
public import CFSG.Quasithin.H13.J4Chain12Spec
public meta import Certificates.Data.CFSGNative.H13.J4Chain12
public meta import Certificates.Data.CFSGNative.H13.J4Data
import Certificates.Data.CFSGNative.H13.J4Data

public noncomputable section

namespace CFSG.Quasithin.H13.J4

open CFSG.Quasithin.H13.J4.Native

@[expose] def uvPairs12 : Array Pr12 :=
  #[(uRows12, uRows12),
    (vRows12, CFSG.Sporadic.SmallF2.Native.mulRows 12 vRows12 vRows12)]


end CFSG.Quasithin.H13.J4
