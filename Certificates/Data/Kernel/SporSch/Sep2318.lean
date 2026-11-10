module

public import Certificates.Data.Kernel.SporSch.ThRows

public section

namespace CFSG.KS.SporSch

open CFSG.KC.Enum

@[expose] noncomputable def sepBit (x k : Nat) : Nat := Nat.land (Nat.shiftRight x k) (nat_lit 1)

@[expose] noncomputable def sepTrK (R T : Nat → Nat) (i : Nat) : Bool :=
  allN (nat_lit 248) (fun j => Nat.beq (sepBit (T j) i) (sepBit (R i) j))

@[expose] noncomputable def sepCodeK (G : Nat → Nat) (i j : Nat) : Nat :=
  Nat.add (Nat.add (Nat.add (sepBit (G (Nat.mul (nat_lit 2) i)) (Nat.mul (nat_lit 2) j))
    (Nat.mul (nat_lit 2) (sepBit (G (Nat.mul (nat_lit 2) i)) (Nat.succ (Nat.mul (nat_lit 2) j)))))
    (Nat.mul (nat_lit 4) (sepBit (G (Nat.succ (Nat.mul (nat_lit 2) i))) (Nat.mul (nat_lit 2) j))))
    (Nat.mul (nat_lit 8)
      (sepBit (G (Nat.succ (Nat.mul (nat_lit 2) i))) (Nat.succ (Nat.mul (nat_lit 2) j))))


end CFSG.KS.SporSch

end
