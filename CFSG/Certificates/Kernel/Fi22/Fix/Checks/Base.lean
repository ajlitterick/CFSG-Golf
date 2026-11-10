module

public import CFSG.Certificates.Kernel.Fi22.Fix.Sel
public import CFSG.Certificates.Kernel.Fi22.Bound.Data.P_Sel
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Fi22.Fix.Defs

public noncomputable section

namespace CFSG.KD.Fi22F

open CFSG.KC.Fi22F


@[expose] def rg (c : Nat) : Bool := rangeOK (Lsel c)


theorem lv0 : Nat.beq (lv LV 0) 0 = true := by quickRfl


end CFSG.KD.Fi22F

#kc_each CFSG.KD.Fi22F.rg 0 4
#kc_each CFSG.KD.Fi22F.«let» 0 4

end
