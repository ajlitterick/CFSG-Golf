module

public import CFSG.Certificates.Kernel.YModel.Y332.Chain
import CFSG.Certificates.Kernel.Common.Each

public section

set_option maxRecDepth 100000

namespace CFSG.KD.YMY332

open CFSG.KC.YModel

@[expose] noncomputable def ch10099word (i : Nat) : Bool := wordOK 15 32 9 T0 WP0 WL0 i

@[expose] noncomputable def ch10099lev (i : Nat) : Bool :=
  levelOK 15 28162 21 T0 (CFSG.KD.YM332C.F 0) R0 M0 Z0 i

#kc_each ch10099word 0 12
#kc_each ch10099lev 0 9


end CFSG.KD.YMY332

end
