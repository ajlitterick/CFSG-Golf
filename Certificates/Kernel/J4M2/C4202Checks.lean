module

public import Certificates.Data.Kernel.J4M2Hex
public import CFSG.Certificates.Kernel.Common.Each

set_option maxRecDepth 100000

public section

namespace CertificateChecks.KernelJ4M2

open CFSG.KC.Enum CFSG.KC.LQT.L CFSG.KS.PK CFSG.KC.J4M2K CFSG.Quasithin.J4M2
  CFSG.QuasithinUnique.Vol2Native.A312L.M22Lat

@[expose] noncomputable def ch4202sig (n : Nat) : Bool :=
  (List.range 77).all fun i => ((sigPerm n) (Fin.ofNat 77 i)).val == (sigData.getD n []).getD i 0

#kc_each ch4202sig 0 32

theorem ch4202hexLab :
    (hexLab.length == 77 && hexLab.all (fun h => h.length == 6 && h.all (· < 22))) = true := by
  decide +kernel

theorem ch4202dist : distChk = true := by decide +kernel

@[expose] noncomputable def ch4202gen (k : Nat) : Bool := hexGenK k

#kc_each ch4202gen 0 25

theorem ch4202words : wordsChk = true := by decide +kernel

theorem ch4202t : tChk = true := by decide +kernel

@[expose] noncomputable def ch4202class (j : Nat) : Bool := classK j

#kc_each ch4202class 0 6

theorem ch4202p0 : p0Chk = true := by decide +kernel


end CertificateChecks.KernelJ4M2

end
