module

public import Certificates.Kernel.LocalComp.L34GrDefs
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.LocalComp.L34NDefs

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.L34Gr

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.L34K
open CertificateChecks.KernelLC.L34X
open CFSG.KLie.CT (andB orB notB)

theorem kTop : top = true := by quickRfl

theorem kY : grY (pidn 42 6) X0 = true := by quickRfl


end CertificateChecks.KernelLC.L34Gr

end
