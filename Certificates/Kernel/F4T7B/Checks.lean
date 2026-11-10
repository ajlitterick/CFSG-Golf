module

public import Certificates.Data.Kernel.F4T7B
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_json_gz CFSG.KD.F4T7B "Certificates/Kernel/F4T7B/data/t7b.json.gz" 48662
  10878697852267138895
  (C : List (List Nat)) (K : List (List Nat))

namespace CFSG.KD.F4T7B

open CFSG.KC.F4M3B CFSG.KC.F4T7B

theorem ch188006_len : (C.map List.length == [1080, 1080, 1080, 1080, 1080, 1080] &&
    K.map List.length == [3, 3, 3, 3, 3, 3]) = true := by decide +kernel

theorem ch188006_0 : chkAll (omC 0) (C.getD 0 []) (K.getD 0 []) = true := by decide +kernel

theorem ch188006_1 : chkAll (omC 1) (C.getD 1 []) (K.getD 1 []) = true := by decide +kernel

theorem ch188006_2 : chkAll (omC 2) (C.getD 2 []) (K.getD 2 []) = true := by decide +kernel

theorem ch188006_3 : chkAll (omC 3) (C.getD 3 []) (K.getD 3 []) = true := by decide +kernel

theorem ch188006_4 : chkAll (omC 4) (C.getD 4 []) (K.getD 4 []) = true := by decide +kernel

theorem ch188006_5 : chkAll (omC 5) (C.getD 5 []) (K.getD 5 []) = true := by decide +kernel


end CFSG.KD.F4T7B

end
