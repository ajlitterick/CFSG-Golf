module

public import Certificates.Kernel.TWDK.D36
import CFSG.Certificates.Kernel.Common.EachTrue

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public section

namespace CFSG.KD.TWDK36

open Certificates.TWDK Certificates.TWDK36

theorem frame : kFrameOK 3 6 F = true := by decide +kernel

theorem cover : kCover36 6 S T = true := by decide +kernel

theorem lenS : S.length = 14 := by decide +kernel

theorem lenT : T.length = 8 := by decide +kernel


end CFSG.KD.TWDK36

#kc_each CFSG.KD.TWDK36 s (Certificates.TWDK36.kOneAt 3 6 CFSG.KD.TWDK36.F CFSG.KD.TWDK36.O
  CFSG.KD.TWDK36.S) 0 14

#kc_each CFSG.KD.TWDK36 t (Certificates.TWDK36.kTwoAt 3 6 CFSG.KD.TWDK36.F CFSG.KD.TWDK36.O
  CFSG.KD.TWDK36.T) 0 8

end
