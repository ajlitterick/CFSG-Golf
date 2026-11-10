module

public import Certificates.Data.Kernel.M24R.R3Orb
public import CFSG.Certificates.Kernel.Common.ForallChunks
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Repo

public section

set_option profiler true
set_option profiler.threshold 200

#kc_repo #kc_ktree CFSG.KC.M24R3 OR
  "Certificates/Kernel/M24R/data/orb.bin" 66 4 1330560 9119718571786199805

namespace CFSG.KC.M24R3


#kc_forall_chunks ch21194_orbAll (fun k => orbBlk OR (504 * k) 504 = true) 40
  CFSG.KC.M24R3.ch21194_orb 1


end CFSG.KC.M24R3

end
