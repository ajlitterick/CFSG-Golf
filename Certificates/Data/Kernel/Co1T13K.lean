module

public import Certificates.Data.Kernel.Co1BBound
public import Certificates.Data.Kernel.SporSch.Co1MatW

public section

namespace CFSG.KC.Co1T13K

open CFSG.KC.Loop CFSG.KC.M1F2 CFSG.KC.Co1F2 CFSG.KC.Co1B CFSG.KLie.CT CFSG.KC.Enum
  CFSG.KC.Co1BBound

@[expose] noncomputable def pvK (YT : List Nat) (p v : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun t acc => nIf(bit p t, Nat.xor (vmF (nat_lit 24) (getL (nat_lit 0) YT t) v) acc, acc))
    (nat_lit 12)

@[expose] noncomputable def inSK (XB : Nat → Nat) (YT : List Nat) (p q v : Nat) : Bool :=
  andB (memK XB (pvK YT p v)) (memK XB (pvK YT q v))

@[expose] noncomputable def orbK (YT : List Nat) (r : Nat) : List Nat :=
  (List.range 13).map fun t => vmF (nat_lit 24) (getL (nat_lit 0) YT t) r

@[expose] noncomputable def orbsK (YT : List Nat) (R : List Nat) : List Nat :=
  R.flatMap (orbK YT)

@[expose] noncomputable def inL (x : Nat) (L : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun y _ ih => Bool.rec ih true (Nat.beq x y)) L

@[expose] noncomputable def nodupK (L : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun x l ih => andB (notB (inL x l)) ih) L

@[expose] noncomputable def setOK (XB : Nat → Nat) (YT : List Nat) (p q : Nat) (R : List Nat) :
    Bool :=
  andB ((orbsK YT R).all fun v => andB (memK XB v) (inSK XB YT p q v)) (nodupK (orbsK YT R))


end CFSG.KC.Co1T13K

end
