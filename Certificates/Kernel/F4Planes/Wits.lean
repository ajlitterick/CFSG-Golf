module

public import Certificates.Data.Kernel.F4PlanesWit
public import Certificates.Kernel.F4Planes.Pins
public import Certificates.Kernel.F4Syl3.ModelChk
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Harness

public section

#kc_repo #kc_json_gz CFSG.KD.F4Planes "Certificates/Kernel/F4Planes/data/wits.json.gz" 8905
  10153431797724067980 (ww : List (Nat × Nat × Nat × Nat)) (wk : List Nat)

namespace CFSG.KD.F4Planes

open CFSG.KC.F4Planes

theorem wit_ok : witP pS ww wk CFSG.KD.F4Syl3.reps = true := by quickRfl


end CFSG.KD.F4Planes

end
