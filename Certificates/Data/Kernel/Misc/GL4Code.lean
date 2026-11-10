module

public import Certificates.Data.Kernel.Misc.Base

public section

namespace CFSG.KC.Misc.GL4

open CFSG.KC.Ord CFSG.KC.LQT.P

@[expose] noncomputable def mul4F (a b : Nat) : Nat :=
  CFSG.KC.Misc.letN a fun a => CFSG.KC.Misc.letN b fun b =>
    Nat.xor (Nat.xor (Nat.xor
      (Nat.land (Nat.mul (Nat.land a (nat_lit 4369)) (nat_lit 15))
        (Nat.mul (Nat.land b (nat_lit 15)) (nat_lit 4369)))
      (Nat.land (Nat.mul (Nat.land (Nat.shiftRight a (nat_lit 1)) (nat_lit 4369)) (nat_lit 15))
        (Nat.mul (Nat.land (Nat.shiftRight b (nat_lit 4)) (nat_lit 15)) (nat_lit 4369))))
      (Nat.land (Nat.mul (Nat.land (Nat.shiftRight a (nat_lit 2)) (nat_lit 4369)) (nat_lit 15))
        (Nat.mul (Nat.land (Nat.shiftRight b (nat_lit 8)) (nat_lit 15)) (nat_lit 4369))))
      (Nat.land (Nat.mul (Nat.land (Nat.shiftRight a (nat_lit 3)) (nat_lit 4369)) (nat_lit 15))
        (Nat.mul (Nat.land (Nat.shiftRight b (nat_lit 12)) (nat_lit 15)) (nat_lit 4369)))

@[expose] noncomputable def id4 : Nat := nat_lit 33825

@[expose] noncomputable def fld (x o w : Nat) : Nat :=
  Nat.mod (Nat.shiftRight x o) (Nat.shiftLeft (nat_lit 1) w)


end CFSG.KC.Misc.GL4

end
