module

public import Certificates.Data.ThSevenPerfect
import Certificates.Kernel.ThCent.Perf7Glue

public section

namespace Certificates

open CertificateChecks

theorem certificate10143 : CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSevenPerfect.thPerfOK = true :=
  KernelThList.thPerfOK_K

end Certificates
