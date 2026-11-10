module

public import Certificates.Kernel.TWDK.D39
import CFSG.Certificates.Kernel.Common.EachTrue

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public section

namespace CFSG.KD.TWDK39

open Certificates.TWDK

theorem frame : kFrameOK 3 9 F = true := by decide +kernel

theorem cover : kCover 9 S R = true := by decide +kernel

theorem lenS : S.length = 20 := by decide +kernel

theorem lenR : R.length = 4 := by decide +kernel


end CFSG.KD.TWDK39

#kc_each CFSG.KD.TWDK39 s (Certificates.TWDK.kSingleAt 3 9 CFSG.KD.TWDK39.F CFSG.KD.TWDK39.S) 0 20

#kc_each CFSG.KD.TWDK39 r (Certificates.TWDK.kResAt 3 9 CFSG.KD.TWDK39.F CFSG.KD.TWDK39.R) 0 4

end
