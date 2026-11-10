
module

public import Certificates.Data.Kernel.J4Count
public import Certificates.Kernel.SporSch.J4S.NoCK
public import Certificates.Kernel.SporSch.J4S.Orbits
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4Count

open CFSG.KC.Enum CFSG.KC.J4Count CFSG.KC.J4Q CertificateChecks.KernelSporSch
open CertificateChecks.KernelSporSch.J4NoCK

@[expose] def RC : List Nat := [2048, 2, 1, 1, 16, 512, 128]

@[expose] noncomputable def basisOK (BS PS : List (List Nat)) (l : Nat) : Bool :=
  bAnd(Nat.beq (List.length (getL PS l)) (List.length (getL BS l)),
  bAnd(Nat.beq (Nat.shiftLeft 1 (List.length (getL BS l))) (getN 0 RC l),
  bAnd(allL (getL BS l) (fun b => bAnd(Nat.blt b 2048, Nat.beq (etaK (J4RV l) b) (J4RV l))),
    allN (Nat.shiftLeft 1 (List.length (getL BS l)))
      (fun m => Nat.beq (decode (getL PS l) (combo (getL BS l) m)) m))))

@[expose] noncomputable def cntZ (BS PS : List (List Nat)) (l : Nat) : Nat :=
  cntK 1771 (fun i => Nat.beq (combo (getL BS l) (decode (getL PS l) (J4O1.PT i))) (J4O1.PT i))

theorem basis_ok : allN 7 (basisOK BS PS) = true := by quickRfl

theorem cnt_ok : allN 7 (fun l => Nat.beq (cntZ BS PS l) (getN 0 CZ l)) = true := by quickRfl


end CertificateChecks.KernelJ4Count

end
