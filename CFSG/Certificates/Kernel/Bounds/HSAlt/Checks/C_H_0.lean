module

public import CFSG.Certificates.Kernel.Common.LceS
public import CFSG.Certificates.Kernel.Bounds.HSAlt.Data.C_Sel
import CFSG.Certificates.Kernel.Common.Harness

public noncomputable section

namespace CFSG.KD.HSKC

theorem sH0 : CFSG.KC.LceS.wordsOK selWT selRT selST INV INV8 (nat_lit 2048) HS = true := by
  quickRfl

theorem sH1 : CFSG.KC.LceS.invOK INV INV8 (nat_lit 4) = true := by
  quickRfl


theorem sH6 : CFSG.KC.HSK.hintsLt selWT (nat_lit 2048) (nat_lit 30) HS = true := by
  quickRfl

end CFSG.KD.HSKC

end
