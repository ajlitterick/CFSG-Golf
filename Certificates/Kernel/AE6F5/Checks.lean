module

public import Certificates.Data.Kernel.AE6F5K
import CFSG.Certificates.Kernel.Common.EachTrue
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

set_option maxRecDepth 100000
set_option maxHeartbeats 0

#kc_repo #kc_json_gz CFSG.KD.AE6F5 "Certificates/Kernel/AE6F5/data/f5.json.gz" 179222
  17645552689080162309
  (D : List Nat) (FP : Nat) (FS : Nat) (CT : Nat) (CP : Nat) (HT : Nat) (HP : Nat) (GN : Nat)

public noncomputable section

namespace CFSG.KD.AE6F5

open CFSG.KC.AE6F5K


end CFSG.KD.AE6F5

end

open CFSG.KC.AE6F5K CFSG.KD.AE6F5

#kc_each CFSG.KD.AE6F5 ch517508_treeC (fun _ => treeOK 216 CT CP GN 7) 0 1

#kc_each CFSG.KD.AE6F5 ch517508_treeH (fun _ => treeOK 1296 HT HP GN 9) 0 1

#kc_each CFSG.KD.AE6F5 ch517508_p (fun t => piOK GN CT HT FP FS t (D.getD t 0)) 0 24
