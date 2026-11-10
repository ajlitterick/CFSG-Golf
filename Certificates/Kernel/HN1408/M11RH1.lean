module

public import Certificates.Kernel.HN1408.M11DefsR
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.HN1408.M11Defs
public import Certificates.Kernel.HN1408.M11Words

public section

set_option maxRecDepth 400000
set_option maxHeartbeats 0
set_option Elab.async false

#kc_each CFSG.KD.HN1408.hvR 8 16
#kc_each CFSG.KD.HN1408.hsR 0 2

namespace CFSG.KD.HN1408

open CFSG.KC.Enum CFSG.KS CFSG.KS.PEnumR


end CFSG.KD.HN1408

end
