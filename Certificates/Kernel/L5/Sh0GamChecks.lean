module

public import Certificates.Data.Kernel.L5.Sh0Gam
import CFSG.Certificates.Kernel.Common.Each

public section

namespace CFSG.Certificates.Kernel.L5S

set_option maxRecDepth 100000

theorem wdChkK_true : wdChkK = true := by decide +kernel

theorem relsChkK_true : relsChkK = true := by decide +kernel

#kc_each CFSG.Certificates.Kernel.L5S.gamK 0 4


end CFSG.Certificates.Kernel.L5S

end
