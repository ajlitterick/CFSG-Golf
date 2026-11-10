module

public import Init

public section

namespace CFSG.KC.Q9SL


@[expose] noncomputable def fl (x i : Nat) : Nat := Nat.land (Nat.shiftRight x i) 15


@[expose] noncomputable def m11 (x : Nat) : Nat := fl x 0


end CFSG.KC.Q9SL
