module

public import Certificates.Data.Kernel.LocalQT.SixRank
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000

public section

namespace CFSG.KD.LQT.C4051

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.LQT.X6

theorem hrank : rankOK = true := by quickRfl


end CFSG.KD.LQT.C4051

end
