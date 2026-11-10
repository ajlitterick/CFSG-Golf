module

public import Certificates.Data.Kernel.D42Cls
public import Certificates.Kernel.D4Plane.Checks
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.EachTrue

public section

#kc_repo #kc_json_gz CFSG.KD.D42A "Certificates/Kernel/D42Cls/data/a.json.gz" 375451
  3669998975996202135 (N : Nat) (n : Nat) (T : List Nat) (TW : List Nat) (DP : Nat) (Vm : Nat)
  (sW : List (List Nat)) (kW : List Nat) (rows : List (List (Nat × Nat × Nat × List Nat)))
  (CR : List (List (Nat × Nat × Nat))) (W1 : List (Nat × Nat × Nat)) (W2 : List (Nat × Nat × Nat))
  (roots : List (List Nat × List Nat × Nat × List Nat × List Nat)) (xyW : List (List Nat))

namespace CFSG.KD.D42A

open CFSG.KC.D42Cls CFSG.KC.D4PlaneP CFSG.KD.D4Plane

theorem shapeOK : (N == 1512 && T.length == 24 && TW.length == 24 && rows.length == 24 &&
    CR.length == 8 && roots.length == 118) = true := by decide +kernel

#kc_each CFSG.KD.D42A dc3arw
  (fun j => rowsOK N T TW DP Vm (sW.map (wordP ls)) rows j) 0 24

#kc_each CFSG.KD.D42A dc3acr (fun i => crOK T CR i) 0 8

theorem w1OK : wOK TW W1 0 = true := by decide +kernel

theorem w2OK : wOK TW W2 1 = true := by decide +kernel

#kc_each CFSG.KD.D42A dc3art
  (fun j => rootsOK ls (wordP ls kW) Vm N (wordP ls [14, 16, 17]) (wordP ls [15, 12, 15, 5])
    (sW.map (wordP ls)) (sW.map fun w => wordP ls w.reverse) CR W1 W2 roots j) 0 8

theorem classOK' : classOK (wordP ls kW) n N (sW.map (wordP ls))
    (sW.map fun w => wordP ls w.reverse) roots = true := by decide +kernel

theorem xyOK' : xyOK ls (wordP ls [14, 16, 17]) (wordP ls [15, 12, 15, 5])
    (wordP ls [17, 16, 14]) (wordP ls [5, 15, 12, 15]) xyW = true := by decide +kernel


end CFSG.KD.D42A

end
