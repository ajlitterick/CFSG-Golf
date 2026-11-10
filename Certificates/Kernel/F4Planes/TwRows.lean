module

public import Certificates.Data.Kernel.F4PlanesTw
public import Certificates.Kernel.F4Planes.E6Pins
public import Certificates.Kernel.F4Planes.ModelChk
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.EachTrue
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_json_gz CFSG.KD.F4PlanesTw "Certificates/Kernel/F4Planes/data/tw.json.gz"
  272441 15854018672204135071 (X8 : Nat) (X9 : Nat) (ij : List (Nat × Nat))
  (gens : List (List (Nat × Nat × Nat))) (zs : List (List (List Nat)))

#kc_each CFSG.KD.F4PlanesTw.ch14946tw r (fun r => CFSG.KC.F4PlanesTw.rowAtT CFSG.KD.F4PlanesE6.IP
  CFSG.KD.F4PlanesTw.X8 CFSG.KD.F4PlanesTw.X9 CFSG.KD.F4PlanesE6.pS6 CFSG.KD.F4Planes.PR
  CFSG.KD.F4PlanesTw.ij CFSG.KD.F4PlanesTw.gens CFSG.KD.F4PlanesTw.zs r) 0 67

namespace CFSG.KD.F4PlanesTw

open CFSG.KC.F4PlanesTw


end CFSG.KD.F4PlanesTw

end
