module

public import Certificates.Data.Kernel.F4Syl3Rel
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_json_gz CFSG.KD.F4Syl3 "Certificates/Kernel/F4Syl3/data/rel.json.gz" 250
  15168432961141368234 (w4 : Nat) (l4 : Nat) (w5 : Nat) (l5 : Nat)

namespace CFSG.KD.F4Syl3

open CFSG.KC.F4Syl3

theorem rel_ok : relN w4 l4 w5 l5 = 1 := by decide +kernel


end CFSG.KD.F4Syl3

end
