module

public import Certificates.Kernel.SporSch.Ru.LB2255
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.SporSch.Ru.CChain
public import Certificates.Kernel.SporSch.Ru.LChain

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.RuLB.Neg

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Ru2250 CFSG.KS.Ru2255
  CertificateChecks.KernelSporSch CertificateChecks.KernelSporSch.RuG
  CertificateChecks.KernelSporSch.RuLB
open CFSG.KLie.CT (notB)


theorem neg_sq : notB (pSq (pidn 4060 12) (pidn 4060 12) (pidn 4060 12)) = true := by quickRfl


end CertificateChecks.KernelSporSch.RuLB.Neg

end
