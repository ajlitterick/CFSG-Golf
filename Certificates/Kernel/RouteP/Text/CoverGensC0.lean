module

public import Certificates.Kernel.RouteP.Text.CoverGensChunks
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 1000000

#kc_each CertificateChecks.KernelRouteP.pcgPc 0 8

namespace CertificateChecks.KernelRouteP

open CFSG.KC CFSG.KC.RouteP CFSG.KD.RouteP


end CertificateChecks.KernelRouteP

end
