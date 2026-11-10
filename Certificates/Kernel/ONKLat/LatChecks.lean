module

public import Certificates.Kernel.ONKLat.LatData
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelONKLat

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc.Clos CFSG.KC.CosetLat

set_option maxRecDepth 100000

theorem ch812105t : tOK = true := by quickRfl

theorem ch812105u : uOK = true := by quickRfl

#kc_each ch812105m 0 3

theorem ch812105repM : repMOK = true := by quickRfl

theorem ch812105rep : repOK = true := by quickRfl

theorem ch812105join : joinOK = true := by quickRfl

theorem ch812105h3 : h3OK = true := by quickRfl


end CertificateChecks.KernelONKLat

end
