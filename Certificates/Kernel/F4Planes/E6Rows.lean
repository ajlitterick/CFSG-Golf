module

public import Certificates.Kernel.F4Planes.E6Pins
public import Certificates.Kernel.F4Planes.ModelChk
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.EachTrue
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Harness

public section

#kc_repo #kc_json_gz CFSG.KD.F4PlanesE6 "Certificates/Kernel/F4Planes/data/e6rows.json.gz"
  616701 5673021577970917268 (ij : List (Nat × Nat)) (gens : List (List (Nat × Nat × Nat × Nat)))
  (tgs : List (List (List Nat)))

#kc_each CFSG.KD.F4PlanesE6.ch14949rw r (fun r => CFSG.KC.F4PlanesE6.rowAt CFSG.KD.F4PlanesE6.LP
  CFSG.KD.F4PlanesE6.IP CFSG.KD.F4PlanesE6.IPi CFSG.KD.F4PlanesE6.pS6 CFSG.KD.F4Planes.PR
  CFSG.KD.F4PlanesE6.ij CFSG.KD.F4PlanesE6.gens CFSG.KD.F4PlanesE6.tgs r) 0 67

namespace CFSG.KD.F4PlanesE6

open CFSG.KC.F4PlanesE6


end CFSG.KD.F4PlanesE6

end
