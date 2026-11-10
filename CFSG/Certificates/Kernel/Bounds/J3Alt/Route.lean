module

public import CFSG.Certificates.Kernel.Bounds.J3Alt.Data.B_Sel
public import CFSG.Certificates.Kernel.Bounds.J3Alt.Data.T_Sel
public import CFSG.Certificates.Kernel.Common.LabF
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Common.Lce
public import CFSG.Certificates.Kernel.Common.RelNorm
import CFSG.Certificates.Kernel.Bounds.J3Alt.Checks.T_H_0
import CFSG.Certificates.Kernel.Bounds.J3Alt.Checks.B_H_0

public section

namespace CFSG.KC.J3A.Route


@[expose] def kT : Nat := 2


theorem bot_sub : Nat.beq (CFSG.KD.J3AB.selST (nat_lit 0)) (nat_lit 4) = true := by quickRfl

theorem bot_pow : Nat.beq (CFSG.KD.J3AB.selRT (nat_lit 0)) (nat_lit 8) = true := by quickRfl

@[expose] noncomputable def powE (e k : Nat) : Nat :=
  (fun n W => Nat.add (Nat.mul (Nat.mul (nat_lit 4) n) k)
    (Nat.shiftLeft (Nat.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun i acc => Nat.lor acc (Nat.shiftLeft W (Nat.mul (Nat.mul (nat_lit 8) n) i))) k) (nat_lit 12)))
    (Nat.land (Nat.shiftRight e (nat_lit 2)) (nat_lit 1023)) (Nat.shiftRight e (nat_lit 12))

@[expose] def kPow : Nat := 2


theorem order : Nat.beq (Nat.mul (Nat.mul CFSG.KD.J3AT.nLive CFSG.KD.J3AB.nLive) kPow) (nat_lit 50232960) = true := by quickRfl

end CFSG.KC.J3A.Route

end
