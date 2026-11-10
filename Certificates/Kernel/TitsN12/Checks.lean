module

public import Certificates.Kernel.SporSch.Tits.GenSurv
public import Certificates.Kernel.SporSch.Tits.GenAll5
public import Certificates.Kernel.Sporadic.Tits.LocH
public import Certificates.Kernel.Sporadic.Tits.LocN
public import Certificates.Kernel.Sporadic.Tits.LocJ
public import Certificates.Kernel.Sporadic.Tits.LocK
public import Certificates.Kernel.TitsOct.Data
public import Certificates.Data.Kernel.TitsN12K
public import CFSG.Certificates.Kernel.Common.JsonGz
public import CFSG.Certificates.Kernel.Common.Repo
public meta import CFSG.Sporadic.Schreier.TitsCentralCheckInputs
public meta import CFSG.Sporadic.Schreier.TitsEnum
public meta import CFSG.Sporadic.Schreier.TitsActionCheckInputs
public meta import Certificates.Data.RuF45Geom
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelTitsN12

open CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier.Tits

meta def swp (a : Array Nat) (x y : Nat) : Bool :=
  ((a[1]! == x && a[2]! == y) || (a[1]! == y && a[2]! == x)) &&
    ((a[x]! == 1 && a[y]! == 2) || (a[x]! == 2 && a[y]! == 1))

meta def pH (a : Array Nat) : Bool :=
  a[0]! == 0 && (swp a 3 4 || swp a 5 7 || swp a 9 13 || swp a 17 25) &&
    eqA 1755 (compA 1755 a a) (idA 1755)

meta def farPts : List Nat :=
  let lay := (CFSG.RuF45.layBFS titsLinePtArr (CFSG.RuF45.mkPtL titsLinePtArr) 0).1
  (List.range 1755).filter fun p => lay[p]! == 8

meta def lH : List (Array Nat) := survivors5 1755 titsHLevels pH

meta def lF : List (Array Nat) := lH.filter fun a => farPts.any fun p => a[p]! == p

meta def pN (a : Array Nat) : Bool :=
  (a[0]! == 1 || a[0]! == 2) && a[a[0]!]! == 0 && eqA 1755 (compA 1755 a a) (idA 1755)

meta def lN : List (Array Nat) := survivors5 1755 titsNLevels pN

end CertificateChecks.KernelTitsN12

#kst_surv CertificateChecks.KernelTitsN12.SH 11 CFSG.Sporadic.Schreier.Tits.titsHLevels
  CertificateChecks.KernelTitsN12.lH
#kst_surv CertificateChecks.KernelTitsN12.SF 11 CFSG.Sporadic.Schreier.Tits.titsHLevels
  CertificateChecks.KernelTitsN12.lF
#kst_surv CertificateChecks.KernelTitsN12.SN 11 CFSG.Sporadic.Schreier.Tits.titsNLevels
  CertificateChecks.KernelTitsN12.lN

#kc_repo #kc_json_gz CertificateChecks.KernelTitsN12.D "Certificates/Kernel/TitsN12/data/n12.json.gz"
  1051 13072867592665378660 (U : List Nat) (R1 : List Nat) (E1 : List (Nat × Nat × Nat)) (R2 : List Nat)
  (E2 : List (Nat × Nat × Nat)) (R4 : List Nat) (E4 : List (Nat × Nat × Nat)) (R8 : List Nat)
  (E8 : List (Nat × Nat × Nat))

namespace CertificateChecks.KernelTitsN12

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CFSG.KC.TitsN12K
open CertificateChecks.KernelSpor

@[expose] noncomputable def PH (t0 t1 t2 t3 t4 : Nat) : Bool := swT TitsH.BP (gptR t0 t1 t2 t3 t4)

@[expose] noncomputable def QH : Nat → Nat → Nat → Nat → Nat → Nat → Bool := survQ PH SH.M

@[expose] noncomputable def PN (t0 t1 t2 t3 t4 : Nat) : Bool := n2T TitsN.BP (gptR t0 t1 t2 t3 t4)

@[expose] noncomputable def QN : Nat → Nat → Nat → Nat → Nat → Nat → Bool := survQ PN SN.M

end CertificateChecks.KernelTitsN12

#kst_all5 CertificateChecks.KernelTitsN12.EH 1755 11 10 8 CertificateChecks.KernelSpor.TitsH.LR
  CertificateChecks.KernelSpor.TitsH.TR CertificateChecks.KernelTitsN12.QH
#kst_all5 CertificateChecks.KernelTitsN12.EN 1755 11 24 2 CertificateChecks.KernelSpor.TitsN.LR
  CertificateChecks.KernelSpor.TitsN.TR CertificateChecks.KernelTitsN12.QN

namespace CertificateChecks.KernelTitsN12

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CFSG.KC.TitsN12K
open CertificateChecks.KernelSpor


end CertificateChecks.KernelTitsN12

end
