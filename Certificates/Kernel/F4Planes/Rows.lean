module

public import Certificates.Kernel.F4Planes.Pins
public import Certificates.Kernel.F4Planes.ModelChk
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.EachTrue
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Harness

public section

#kc_repo #kc_json_gz CFSG.KD.F4Planes "Certificates/Kernel/F4Planes/data/rows.json.gz" 499190
  8694890198642737951 (gens : List (List (Nat × Nat × Nat × Nat × Nat × Nat)))
  (tgs : List (List (List Nat)))

#kc_each CFSG.KD.F4Planes.ch14950rw r (fun r => CFSG.KC.F4Planes.rowP CFSG.KD.F4Planes.pS
  CFSG.KD.F4Planes.PR CFSG.KD.F4Planes.gens CFSG.KD.F4Planes.tgs r) 0 67

namespace CFSG.KD.F4Planes

open CFSG.KC.F4Planes


end CFSG.KD.F4Planes

end
