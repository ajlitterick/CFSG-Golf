module

public import Certificates.Kernel.PhanD4Dce.CTData
public import Certificates.Data.Kernel.Misc.Coset.ActOrbit
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.JsonGz

set_option maxRecDepth 100000

#kc_repo #kc_json_gz CFSG.KAct.PhanD4Chain "Certificates/Kernel/PhanD4Dce/data/D4Chain.json.gz"
  12635 10213036681829461284 (LV : List (Nat × List Nat × List Nat))

public section

namespace CFSG.KAct.PhanD4CT

open CFSG.KC.MiscCoset.Act

theorem levels : levelsOK CFSG.KAct.PhanD4CT.A (nat_lit 58) (nat_lit 1120) CFSG.KAct.PhanD4Chain.LV
    [] = true := by
  decide +kernel


end CFSG.KAct.PhanD4CT

end
