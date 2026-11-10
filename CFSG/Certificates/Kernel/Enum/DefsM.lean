module

public import CFSG.Certificates.Kernel.Enum.Defs

public section

namespace CFSG.KC.Enum

@[expose] noncomputable def mrow (d rm M i : Nat) : Nat := fld(M, Nat.mul d i, rm)

@[expose] noncomputable def mmul (d rm C M N : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun j acc => Nat.xor acc (Nat.mul (Nat.land (Nat.shiftRight M j) C) (mrow d rm N j))) d


end CFSG.KC.Enum

end
