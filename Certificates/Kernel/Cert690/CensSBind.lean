module

public import Certificates.Data.Kernel.Cert690.CensusSBind
public import Certificates.Kernel.Cert690.CensSPB
public import Certificates.Kernel.Cert690.CensSMB

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelC690.CensSBind

open CFSG.KC.C690S

theorem bindP : bindS false CertificateChecks.KernelC690.CensSP.base = true := by decide +kernel

theorem bindM : bindS true CertificateChecks.KernelC690.CensSM.base = true := by decide +kernel


end CertificateChecks.KernelC690.CensSBind

end
