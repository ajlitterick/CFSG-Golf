module

public import Certificates.Kernel.SimsF5.Data
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelSimsF5

open CFSG.KC.Ord CFSG.KC.SimsF5

set_option maxRecDepth 100000


#kc_each ch7600m0 0 5


end CertificateChecks.KernelSimsF5

end
