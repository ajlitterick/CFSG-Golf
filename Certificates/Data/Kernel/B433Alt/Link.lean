module

public import Certificates.Data.Kernel.B433Alt.Net

public section

namespace CFSG.KC.Y333

@[expose] noncomputable def tagOK (B x : Nat) : Bool :=
  Nat.beq (Nat.shiftRight B (nat_lit 81920)) (Nat.shiftRight x (nat_lit 12))

@[expose] noncomputable def untag (B : Nat) : Nat :=
  Nat.land B (Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 81920)) (nat_lit 1))


end CFSG.KC.Y333

end
