module

public section

namespace CFSG.Certificates.Kernel.UT3F4


@[expose] noncomputable def FT : Nat := nat_lit 2625168384

@[expose] noncomputable def fmN (u v : Nat) : Nat :=
  Nat.land (Nat.shiftRight FT (Nat.add (Nat.shiftLeft u 3) (Nat.shiftLeft v 1))) 3

@[expose] noncomputable def mulN (x y : Nat) : Nat :=
  Nat.xor (Nat.xor x y) (Nat.shiftLeft (fmN (Nat.land x 3) (Nat.land (Nat.shiftRight y 2) 3)) 4)

@[expose] noncomputable def sel4 (k v0 v1 v2 v3 : Nat) : Nat :=
  Bool.rec (Bool.rec (Bool.rec v3 v2 (Nat.beq k 2)) v1 (Nat.beq k 1)) v0 (Nat.beq k 0)

@[expose] noncomputable def eA (x y a : Nat) : Nat := sel4 a 0 x y (mulN x y)

@[expose] noncomputable def eZ (x0 x1 x2 z : Nat) : Nat :=
  sel4 z 0 (mulN x0 (mulN x2 (mulN x0 x2))) (mulN x1 (mulN x2 (mulN x1 x2)))
    (mulN x0 (mulN x2 (mulN x0 (mulN x2 (mulN x1 (mulN x2 (mulN x1 x2)))))))


end CFSG.Certificates.Kernel.UT3F4

end
