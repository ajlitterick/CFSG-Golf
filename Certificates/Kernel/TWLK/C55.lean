module

public import Certificates.Kernel.TWLK.D55
import CFSG.Certificates.Kernel.Common.EachTrue

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public section

namespace CFSG.KD.TWLK55

open Certificates.TWLK

theorem roots : kRootsOK 5 5 RF = true := by decide +kernel

theorem cover : kCover 5 S T = true := by decide +kernel

theorem lenS : S.length = 12 := by decide +kernel

theorem lenT : T.length = 8 := by decide +kernel


end CFSG.KD.TWLK55

#kc_each CFSG.KD.TWLK55 l55s
  (Certificates.TWLK.kPat1At 5 5 CFSG.KD.TWLK55.RF
    (Certificates.TWLK.kRTPZ 5 5 CFSG.KD.TWLK55.H CFSG.KD.TWLK55.Z) CFSG.KD.TWLK55.S) 0 12

#kc_each CFSG.KD.TWLK55 l55t
  (Certificates.TWLK.kPat2At 5 5 CFSG.KD.TWLK55.RF
    (Certificates.TWLK.kRTPZ 5 5 CFSG.KD.TWLK55.H CFSG.KD.TWLK55.Z) CFSG.KD.TWLK55.T) 0 8

end
