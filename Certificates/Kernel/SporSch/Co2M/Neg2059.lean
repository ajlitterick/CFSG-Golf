
module

public import Certificates.Kernel.SporSch.Co2M.FratSD
public import Certificates.Kernel.SporSch.Co2M.FratTr
public import Certificates.Kernel.SporSch.Co2M.FratMD
public import Certificates.Kernel.SporSch.Co2M.ChainSD
public import Certificates.Data.Kernel.SporSch.Co2Prof
public import Certificates.Data.Kernel.Co2InvS
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelSporSch.Co2M

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Co2M CFSG.KC.Co2InvS CFSG.KS.Co2P
open CFSG.Sporadic.Co2Schreier


end CertificateChecks.KernelSporSch.Co2M

end
