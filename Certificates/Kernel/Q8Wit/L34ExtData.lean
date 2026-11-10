module

public import Certificates.Kernel.SporSch.Th.GenV4
public import Certificates.Data.TwinPerpSmSp1WitL34
meta import Certificates.Data.TwinPerpSmSp1WitL34
meta import Certificates.Kernel.LocalComp.BfsGen
meta import Certificates.Kernel.Sporadic.RawGen
import Certificates.Kernel.LocalComp.BfsGen
public import CFSG.Certificates.Kernel.Bounds.Core3
import CFSG.Certificates.Kernel.Bounds.Load

namespace CertificateChecks.KernelQ8W.L34E

open CFSG.PSL3Four.Native


end CertificateChecks.KernelQ8W.L34E

public section

set_option maxRecDepth 400000

#kc_items CertificateChecks.KernelQ8W.L34.W include_bytes "data/L34ExtData.W.items" 1416 6790868933677084381

end
