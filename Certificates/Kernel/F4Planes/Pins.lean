module

public import Certificates.Data.Kernel.F4PlanesRow
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_json_gz CFSG.KD.F4Planes "Certificates/Kernel/F4Planes/data/pins.json.gz" 7284
  12852867051033098006 (gw : List Nat) (gl : List Nat) (paths : List (List Nat)) (pS : List Nat)

namespace CFSG.KD.F4Planes

open CFSG.KC.F4Planes

theorem pin_ok : pinP gw gl paths pS = true := by quickRfl

theorem rel_ok : relP pS = true := by quickRfl


end CFSG.KD.F4Planes

end
