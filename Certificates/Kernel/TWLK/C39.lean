module

public import Certificates.Kernel.TWLK.D39
import CFSG.Certificates.Kernel.Common.EachTrue

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public section

namespace CFSG.KD.TWLK39

open Certificates.TWLK

theorem roots : kRootsOK 3 9 RF = true := by decide +kernel

theorem cover : kCover 9 S T = true := by decide +kernel

theorem lenS : S.length = 20 := by decide +kernel

theorem lenT : T.length = 8 := by decide +kernel


end CFSG.KD.TWLK39

#kc_each CFSG.KD.TWLK39 l39s
  (Certificates.TWLK.kPat1At 3 9 CFSG.KD.TWLK39.RF
    (Certificates.TWLK.kRT8 3 9 CFSG.KD.TWLK39.H CFSG.KD.TWLK39.E) CFSG.KD.TWLK39.S) 0 20

#kc_each CFSG.KD.TWLK39 l39t
  (Certificates.TWLK.kPat2At 3 9 CFSG.KD.TWLK39.RF
    (Certificates.TWLK.kRT8 3 9 CFSG.KD.TWLK39.H CFSG.KD.TWLK39.E) CFSG.KD.TWLK39.T) 0 8

end
