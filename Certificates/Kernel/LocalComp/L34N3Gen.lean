module

public import Certificates.Kernel.LocalComp.L34NGen
public import Certificates.Kernel.LocalComp.L34Gen2
public meta import Certificates.Kernel.LocalComp.L34NGen
public meta import Certificates.Kernel.LocalComp.L34Gen2

public section

namespace CertificateChecks.KernelLC.L34N3Gen

open CFSG.PSL3Four.Native
open CertificateChecks.KernelLC.L34Gen CertificateChecks.KernelLC.L34NGen
open CFSG.KS.RawGen (pack)

meta def rep (c : Nat) : Nat := (codes.findIdx? fun v => v / 8 == c + 1).getD 0


meta def cI (c : Nat) : Array Nat :=
  let r := rRun.1[rep c]!
  (Array.range sPts.size).filter fun j => comp 42 sPts[j]! r == comp 42 r sPts[j]!


end CertificateChecks.KernelLC.L34N3Gen

end
