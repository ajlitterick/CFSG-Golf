module

public import Certificates.Kernel.SporSch.Co3.StabIt
public import CFSG.Certificates.Kernel.Lie.CT.Core
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.Co3SIC.Neg

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CertificateChecks.KernelSpor
open CFSG.KLie.CT (notB)


theorem neg_sift :
    notB (Co3C.sift (Nat.lor 1 (Nat.shiftLeft (Nat.shiftRight (pidn 276 9) 18) 18))) = true := by
  quickRfl


end CertificateChecks.KernelSporSch.Co3SIC.Neg

end
