module

public import CFSG.Certificates.Kernel.He.Bound.Data.C_Sel
import CFSG.Certificates.Kernel.Common.Harness

public noncomputable section

namespace CFSG.KD.HeBC

theorem sH0 : CFSG.KC.LceS.wordsOK selWT selRT selST INV INV8 (nat_lit 2048) HS = true := by
  quickRfl

theorem sH1 : CFSG.KC.LceS.invOK INV INV8 (nat_lit 4) = true := by
  quickRfl

theorem sH3 : Nat.beq nC (nat_lit 943) = true := by
  quickRfl


theorem sH6 : CFSG.KC.HeB.hintsLt selWT (nat_lit 2048) (nat_lit 2) HS = true := by
  quickRfl

end CFSG.KD.HeBC

end
