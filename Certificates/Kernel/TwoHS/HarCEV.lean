module

public import Certificates.Kernel.TwoHS.HarCKV
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.TwoHS.HarCK

public section

set_option maxRecDepth 400000
set_option Elab.async false

#kc_each CFSG.KD.TwoHS.ch7291hv 0 16

namespace CFSG.KD.TwoHS

open CFSG.KC.Enum CFSG.KS CFSG.KS.MulH CFSG.KS.PEnumB

theorem ch7291hsv_ok : ch7291hsv = true := by
  quickRfl


end CFSG.KD.TwoHS

end
