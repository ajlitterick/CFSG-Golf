module

public import Certificates.Kernel.DELK.D
import CFSG.Certificates.Kernel.Common.EachTrue

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option profiler true
set_option Elab.async false

public section

namespace CFSG.KD.DELK

open Certificates.TwoDepSmallLow Certificates.DELK

theorem cover : kCover O T = true := by decide +kernel

theorem groupsCover : kGroupsCover P S C = true := by decide +kernel

theorem lenO : O.length = 3 := by decide +kernel

theorem lenT : T.length = 6 := by decide +kernel

theorem lenS : S.length = 2 := by decide +kernel

theorem lenC : C.length = 2 := by decide +kernel


end CFSG.KD.DELK

#kc_each CFSG.KD.DELK ch709539c (Certificates.DELK.kConjAt CFSG.KD.DELK.P CFSG.KD.DELK.S
  CFSG.KD.DELK.C) 0 2

#kc_each CFSG.KD.DELK ch709539g (Certificates.DELK.kBaseAt CFSG.KD.DELK.P CFSG.KD.DELK.S) 0 2

#kc_each CFSG.KD.DELK ch709539o (Certificates.DELK.kPat1At CFSG.KD.DELK.H CFSG.KD.DELK.Z
  CFSG.KD.DELK.P CFSG.KD.DELK.O) 0 3

#kc_each CFSG.KD.DELK ch709539t (Certificates.DELK.kPat2At CFSG.KD.DELK.H CFSG.KD.DELK.Z
  CFSG.KD.DELK.P CFSG.KD.DELK.T) 0 6

end
