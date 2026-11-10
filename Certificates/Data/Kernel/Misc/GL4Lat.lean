module

public import Certificates.Data.Kernel.Misc.GL4Code

public section

namespace CFSG.KC.Misc.GL4

open CFSG.KC.Ord CFSG.KC.LQT.P

@[expose] noncomputable def invW (c d : Nat) : Bool :=
  andB (Nat.blt c (nat_lit 65536)) (andB (Nat.blt d (nat_lit 65536)) (Nat.beq (mul4F c d) id4))


end CFSG.KC.Misc.GL4

end
