module

public import CFSG.Certificates.Kernel.Common.Lce
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KC

@[expose] noncomputable def relsNorm (RT : Nat → Nat) (R : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun k acc => andB acc ((fun e =>
      Nat.blt (Nat.shiftRight e (nat_lit 12))
        (Nat.shiftLeft (nat_lit 1) (Nat.mul (nat_lit 8) (Nat.land (Nat.shiftRight e (nat_lit 2)) (nat_lit 1023)))))
    (RT k))) R

namespace RelNormNeg


end RelNormNeg

end CFSG.KC

end
