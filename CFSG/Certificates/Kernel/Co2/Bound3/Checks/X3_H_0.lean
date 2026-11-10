module

public import CFSG.Certificates.Kernel.Common.BindMap
public import CFSG.Certificates.Kernel.Co2.Bound3.Data.X3_Sel
import CFSG.Certificates.Kernel.Common.EachUnfold
import CFSG.Certificates.Kernel.Common.Harness

public noncomputable section

namespace CFSG.KD.Co2KX3

theorem sH0 : CFSG.KC.LceS.wordsOK selWT selRT selST INV INV8 (nat_lit 512) HS = true := by
  quickRfl

theorem sH1 : CFSG.KC.LceS.invOK INV INV8 (nat_lit 10) = true := by
  quickRfl

theorem sH2 : CFSG.KC.LceS.aliveOK LVs (nat_lit 11) (nat_lit 42078) (nat_lit 1024) = true := by
  quickRfl

theorem sH3 : Nat.beq nC (nat_lit 42078) = true := by
  quickRfl

@[expose] def relMap (_ : Nat) : Nat := CFSG.KC.Bind.ofPairs ((List.range 5).map fun g => (g, g))

@[expose] def sH4r (k : Nat) : Bool := CFSG.KC.Bind.subRel (relMap k) (CFSG.KD.Co2KM.XRs k) (litRT k)

#kc_each_unfold CFSG.KD.Co2KX3.sH4r 0 23 eval CFSG.KD.Co2KX3.relMap


end CFSG.KD.Co2KX3

end
