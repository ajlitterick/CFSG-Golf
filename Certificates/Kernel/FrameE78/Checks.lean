module

public import Certificates.Kernel.FrameE78.Data
public import Certificates.Data.Kernel.FrameE78K
import CFSG.Certificates.Kernel.Common.EachTrue

set_option maxRecDepth 400000

public section

namespace CFSG.KD.FrameE78

open CFSG.KC.Enum CFSG.KC.OrbRow CFSG.KC.FrameE78

theorem ch709548p7 : ptsOK 7 1093 V7 = true := by quickRfl

theorem ch709548p8 : ptsOK 8 3280 V8 = true := by quickRfl

#kc_each CFSG.KD.FrameE78 ch709548g7_ (fun j => genJ 7 C7 1093 S7 V7 j) 0 7
#kc_each CFSG.KD.FrameE78 ch709548g8_ (fun j => genJ 8 C8 3280 S8 V8 j) 0 8

theorem ch709548r7 : bAnd(rootOK 7 C7 63 RP7, bAnd(simpleOK 7 RP7, bAnd(closOK 7 63 RP7 CL7,
    bAnd(parOK 7 63 CL7 PT7, distOK 63 RP7)))) = true := by quickRfl

theorem ch709548r8 : bAnd(rootOK 8 C8 120 RP8, bAnd(simpleOK 8 RP8, bAnd(closOK 8 120 RP8 CL8,
    bAnd(parOK 8 120 CL8 PT8, distOK 120 RP8)))) = true := by quickRfl

#kc_each CFSG.KD.FrameE78 ch709548t7_ (fun k => bAnd(Nat.blt (getS b7 k) 1093,
  rowsK 1093 12 4095 S7 7 127 (getS D7 k) (getS b7 k) (getS c7 k) (getLs R7 k))) 0 5
#kc_each CFSG.KD.FrameE78 ch709548t8_ (fun k => bAnd(Nat.blt (getS b8 k) 3280,
  rowsK 3280 12 4095 S8 8 255 (getS D8 k) (getS b8 k) (getS c8 k) (getLs R8 k))) 0 4

theorem ch709548c7 : coverOK 1093 5 D7 = true := by quickRfl

theorem ch709548c8 : coverOK 3280 4 D8 = true := by quickRfl

#kc_each CFSG.KD.FrameE78 ch709548x7_ (fun k => repK 7 63 RP7 V7 (getS b7 k) (getLs Q7 k)) 0 5
#kc_each CFSG.KD.FrameE78 ch709548x8_ (fun k => repK 8 120 RP8 V8 (getS b8 k) (getLs Q8 k)) 0 4


end CFSG.KD.FrameE78

end
