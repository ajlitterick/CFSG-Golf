module

public import Certificates.Kernel.FrameE78.Data
public import Certificates.Data.Kernel.FrameE78RootK
import CFSG.Certificates.Kernel.Common.EachTrue

set_option maxRecDepth 400000

public section

namespace CFSG.KD.FrameE78

open CFSG.KC.Enum CFSG.KC.OrbRow CFSG.KC.FrameE78

#kc_each CFSG.KD.FrameE78 ch709549r_
  (fun k => rtRep 7 63 RP7 V7 (getS b7 k) (getS (getLs Q7 k) 0) 0 1093) 0 5


end CFSG.KD.FrameE78

end
