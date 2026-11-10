module

public import Certificates.Data.Kernel.Hall82K.Defs
import CFSG.Certificates.Kernel.Common.EachTrue

set_option maxRecDepth 100000

public section

namespace CFSG.KC.Hall82K

#kc_each ch840004red r (fun x => bor (Nat.beq (bitN q0K x) 1) (srchK 5 x)) 1 64


end CFSG.KC.Hall82K
