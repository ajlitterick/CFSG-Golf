module

public import CFSG.Certificates.Kernel.Ru.BoundAlt.Data.M_Sel
public import CFSG.Certificates.Kernel.Ru.BoundAlt.Data.B_Sel
public import CFSG.Certificates.Kernel.Ru.Bound.Data.P_Sel
public import CFSG.Certificates.Kernel.Ru.Bound.Data.C_Sel
public import CFSG.Certificates.Kernel.Ru.Bound.Data.A
public import CFSG.Certificates.Kernel.McL.Perm
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Common.RelNorm
import CFSG.Certificates.Kernel.Ru.Bound.Checks.C_H_0
import CFSG.Certificates.Kernel.Ru.BoundAlt.Checks.M_H_0
import CFSG.Certificates.Kernel.Ru.BoundAlt.Checks.B_H_0

public section

namespace CFSG.KC.RuBA

open CFSG.KC

@[expose] noncomputable def qToP (e : Nat) : Nat :=
  Nat.add (Nat.mul (nat_lit 4) (LceS.wLen e))
    (Nat.shiftLeft (Nat.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun q acc => Nat.lor acc (Nat.shiftLeft
        (Nat.add (wLet (LceS.wWord e) q) (Nat.land (wLet (LceS.wWord e) q) (nat_lit 2)))
        (Nat.mul (nat_lit 8) q))) (LceS.wLen e)) (nat_lit 12))

@[expose] noncomputable def derivedOK (k : Nat) : Bool :=
  andB (Nat.beq (qToP (CFSG.KD.RuBAM.selRT (Nat.add (nat_lit 7) k))) (CFSG.KD.RuBA.TW k))
    (Nat.beq (CFSG.KD.RuBA.TL k) (McL.pid CFSG.KD.RuBA.d))

end CFSG.KC.RuBA

namespace CFSG.KC.RuBA.Route


@[expose] def kC : Nat := 2


@[expose] def kM : Nat := 10


theorem q_sq : Nat.beq (CFSG.KD.RuBAM.selRT (nat_lit 0)) (nat_lit 2105352) = true := by quickRfl


theorem a_nT : Nat.beq CFSG.KD.RuBA.nT (nat_lit 9) = true := by quickRfl

theorem derived_0 : CFSG.KC.RuBA.derivedOK (nat_lit 0) = true := by quickRfl
theorem derived_1 : CFSG.KC.RuBA.derivedOK (nat_lit 1) = true := by quickRfl
theorem derived_2 : CFSG.KC.RuBA.derivedOK (nat_lit 2) = true := by quickRfl
theorem derived_3 : CFSG.KC.RuBA.derivedOK (nat_lit 3) = true := by quickRfl
theorem derived_4 : CFSG.KC.RuBA.derivedOK (nat_lit 4) = true := by quickRfl
theorem derived_5 : CFSG.KC.RuBA.derivedOK (nat_lit 5) = true := by quickRfl
theorem derived_6 : CFSG.KC.RuBA.derivedOK (nat_lit 6) = true := by quickRfl
theorem derived_7 : CFSG.KC.RuBA.derivedOK (nat_lit 7) = true := by quickRfl
theorem derived_8 : CFSG.KC.RuBA.derivedOK (nat_lit 8) = true := by quickRfl

theorem bot_sub0 : Nat.beq (CFSG.KD.RuBAB.selST (nat_lit 0)) (nat_lit 4) = true := by quickRfl
theorem bot_sub1 : Nat.beq (CFSG.KD.RuBAB.selST (nat_lit 1)) (nat_lit 8196) = true := by quickRfl

theorem bot_p0sq : Nat.beq (CFSG.KD.RuBAB.selRT (nat_lit 0)) (nat_lit 8) = true := by quickRfl
theorem bot_p1sq : Nat.beq (CFSG.KD.RuBAB.selRT (nat_lit 1)) (nat_lit 2105352) = true := by quickRfl
theorem bot_p0p1sq : Nat.beq (CFSG.KD.RuBAB.selRT (nat_lit 4)) (nat_lit 137441050640) = true := by quickRfl

theorem order : Nat.beq (Nat.mul (Nat.mul (Nat.mul CFSG.KD.RuBP.nLive CFSG.KD.RuBAM.nLive) CFSG.KD.RuBAB.nLive) (nat_lit 4))
    (nat_lit 145926144000) = true := by quickRfl

end CFSG.KC.RuBA.Route

end
