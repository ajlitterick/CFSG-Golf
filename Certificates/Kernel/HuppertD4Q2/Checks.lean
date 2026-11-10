module

public import Certificates.Data.Kernel.HD4Q2K
public import Certificates.Kernel.D4Plane.Checks
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_json_gz CFSG.KD.HD4Q2 "Certificates/Kernel/HuppertD4Q2/data/hd4q2.json.gz" 96268
  9090308713242222626
  (recs : List CFSG.KC.HD4Q2K.Rec) (prs : List (List (Nat × Nat))) (r1 : List (Nat × Nat))
  (r2 : List (Nat × Nat)) (cg : List (List (Nat × Nat))) (ci : List (List (Nat × Nat)))

namespace CFSG.KD.HD4Q2

open CFSG.KC.HD4Q2K CFSG.KD.D4Plane

@[expose] noncomputable def es : List (Nat × Nat) := recs.map fun m => m.2.1

theorem enumOK : enumQ ls es = true := by decide +kernel

theorem sylowOK : sylowQ ls es = true := by decide +kernel

theorem prsOK : prsQ es prs = true := by decide +kernel

theorem rowsOK : rowsQ ls es prs r1 r2 = true := by decide +kernel

theorem recsOK : recsQ es prs recs = true := by decide +kernel

theorem coverOK : coverQ recs = true := by decide +kernel

theorem classOK : (List.range 6).all (classQ ls cg ci) = true := by decide +kernel

theorem centerOK : centerQ ls es = true := by decide +kernel


end CFSG.KD.HD4Q2
