module

public import Certificates.Kernel.TWLK.D36
import CFSG.Certificates.Kernel.Common.EachTrue

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public section

namespace CFSG.KD.TWLK36

open Certificates.TWLK

theorem frame : kFrameOK 3 6 FV FW = true := by decide +kernel

theorem roots : kRootsOK 3 6 RF = true := by decide +kernel

theorem cover : kCover 6 S T = true := by decide +kernel

theorem lenS : S.length = 14 := by decide +kernel

theorem lenT : T.length = 8 := by decide +kernel


end CFSG.KD.TWLK36

#kc_each CFSG.KD.TWLK36 l36s
  (Certificates.TWLK.kPat1At 3 6 CFSG.KD.TWLK36.RF
    (Certificates.TWLK.kRT6 3 6 CFSG.KD.TWLK36.H CFSG.KD.TWLK36.Z CFSG.KD.TWLK36.F)
    CFSG.KD.TWLK36.S) 0 14

#kc_each CFSG.KD.TWLK36 l36t
  (Certificates.TWLK.kPat2At 3 6 CFSG.KD.TWLK36.RF
    (Certificates.TWLK.kRT6 3 6 CFSG.KD.TWLK36.H CFSG.KD.TWLK36.Z CFSG.KD.TWLK36.F)
    CFSG.KD.TWLK36.T) 0 8

end
