module

public import CFSG.Certificates.Kernel.Bounds.HNAlt.Data.Disp
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.EachUnfold

public section

namespace CFSG.KD.HNA

open CFSG.KC.HNA.DceS


theorem xWords : wordsOK WD CFSG.KC.HNA.rel LI NL NR WH nW = true := by quickRfl


theorem xW : andB (Nat.beq W ONEP) (Nat.beq Wi ONEP) = true := by quickRfl


@[expose] noncomputable def okE (D : Nat) : Bool := stabStart (Ed D)

end CFSG.KD.HNA

#kc_each_unfold CFSG.KD.HNA.okE 1 7 as CFSG.KD.HNA.xE

#kc_each_unfold CFSG.KD.HNA.okE 8 82 as CFSG.KD.HNA.xE

end
