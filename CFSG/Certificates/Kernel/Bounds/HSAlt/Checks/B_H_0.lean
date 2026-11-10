module

public import CFSG.Certificates.Kernel.Bounds.HSAlt.Data.B_Sel
import CFSG.Certificates.Kernel.Common.Harness

public noncomputable section

namespace CFSG.KD.HSKB

theorem sH0 : CFSG.KC.LceS.wordsOK selWT selRT selST INV INV8 (nat_lit 512) HS = true := by
  quickRfl

theorem sH1 : CFSG.KC.LceS.invOK INV INV8 (nat_lit 4) = true := by
  quickRfl


end CFSG.KD.HSKB

end
