module

public import Certificates.Kernel.Co1P.PinEDefs
import Certificates.Kernel.J4Q.AllN
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Sporadic.Co1Patterson.GraphTreeData

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1P

open CFSG.KC.Co1B CFSG.KC.Co1P CFSG.KLie.CT CFSG.Sporadic.Co1Patterson.Native

theorem recsE_pin : recsEqK recE (recsT orbEMasks) 0 = true := by quickRfl

#j4q_all CertificateChecks.KernelCo1P.KeyE CertificateChecks.KernelCo1P.keyE_chunk 197


end CertificateChecks.KernelCo1P

end
