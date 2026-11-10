module

public section

namespace CFSG.KC.Y333

@[expose] noncomputable def dsw (s m x : Nat) : Nat :=
  (fun t => Nat.xor x (Nat.xor t (Nat.shiftLeft t s)))
    (Nat.land (Nat.xor (Nat.shiftRight x s) x) m)

@[expose] noncomputable def str20 : Nat :=
  nat_lit 0x10000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001

@[expose] noncomputable def magic20 : Nat :=
  nat_lit 0x10000000000000002000000000000000400000000000000080000000000000010000000000000002000000000000000400000000000000080000000000000010000000000000002000000000000000400000000000000080000000000000010000000000000002000000000000000400000000000000080000000000000010000000000000002000000000000000400000000000000080000

@[expose] noncomputable def colGet (B o : Nat) : Nat :=
  Nat.land (Nat.shiftRight (Nat.mul (Nat.land (Nat.shiftRight B o) str20) magic20) (nat_lit 1216))
    (nat_lit 1048575)

@[expose] noncomputable def rep2 (P m : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 1)
    (fun i r => Nat.lor r (Nat.shiftLeft r (Nat.mul P (Nat.shiftLeft (nat_lit 1) i)))) m


@[expose] noncomputable def idx (k : Nat) : Nat :=
  (fun b => Nat.mul (rep2 (Nat.shiftLeft b (nat_lit 1)) (Nat.sub (nat_lit 19) k))
      (Nat.shiftLeft (Nat.sub (Nat.shiftLeft (nat_lit 1) b) (nat_lit 1)) b))
    (Nat.shiftLeft (nat_lit 1) k)

@[expose] noncomputable def cat (s lo hi : Nat) : Nat := Nat.lor lo (Nat.shiftLeft hi s)

@[expose] noncomputable def pget (P i : Nat) : Nat :=
  Nat.land (Nat.shiftRight P (Nat.mul (nat_lit 15) i)) (nat_lit 32767)


@[expose] noncomputable def colOff (x : Nat) : Nat :=
  Nat.add (Nat.mul (nat_lit 1280) (Nat.land (Nat.shiftRight x (nat_lit 6)) (nat_lit 63)))
    (Nat.land x (nat_lit 63))


end CFSG.KC.Y333

end
