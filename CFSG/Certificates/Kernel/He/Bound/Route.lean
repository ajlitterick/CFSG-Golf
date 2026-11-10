module

public import CFSG.Certificates.Kernel.He.Bound.Data.P_Sel
public import CFSG.Certificates.Kernel.He.Bound.Data.Q_Sel
public import CFSG.Certificates.Kernel.He.Bound.Data.C_Sel
public import CFSG.Certificates.Kernel.He.Bound.Lab
public import CFSG.Certificates.Kernel.Common.LceS
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Common.Lce
public import CFSG.Certificates.Kernel.Common.RelNorm
import CFSG.Certificates.Kernel.He.Bound.Checks.C_H_0
import CFSG.Certificates.Kernel.He.Bound.Checks.Q

public section

namespace CFSG.KC.HeB.Route

@[expose] def kC : Nat := 2


theorem norm_Q : CFSG.KC.relsNorm CFSG.KD.HeBQ.selRT (nat_lit 6) = true := by quickRfl


theorem q_sq : Nat.beq (CFSG.KD.HeBQ.selRT (nat_lit 0)) (nat_lit 8) = true := by quickRfl

theorem q_sub : Nat.beq (CFSG.KD.HeBQ.selST (nat_lit 0)) (nat_lit 8196) = true := by quickRfl

theorem q_pow : Nat.beq (CFSG.KD.HeBQ.selRT (nat_lit 1)) (nat_lit 13563782407139352) = true := by
  quickRfl

theorem order : Nat.beq (Nat.mul (Nat.mul CFSG.KD.HeBP.nLive CFSG.KD.HeBQ.nLive) (nat_lit 6))
    (nat_lit 4030387200) = true := by quickRfl

end CFSG.KC.HeB.Route

end
