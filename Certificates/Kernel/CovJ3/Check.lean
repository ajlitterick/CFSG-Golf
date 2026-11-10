module

public import Certificates.Kernel.J3Local.Seeds
public import Certificates.Data.Kernel.CovJ3
public import CFSG.GH74.KGroups.CoverJ3Inputs
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelCovJ3

open CFSG.KC.CovJ3 CFSG.KC.OpsK CFSG.GH74.KGroups.J3 CertificateChecks.KernelJ3L

theorem ch5111_K : conjT (opsF2K 80) JA.M JB.M j3Words (List.range 80) = true := by
  quickRfl


end CertificateChecks.KernelCovJ3

end
