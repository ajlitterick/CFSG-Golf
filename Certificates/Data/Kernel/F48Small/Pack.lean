module

public import Certificates.Data.Kernel.LocalQT.Lat

public section

namespace CFSG.KC.F48S

open CFSG.KC.Ord CFSG.KC.LQT.L

@[expose] noncomputable def encL (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun a _ ih => Nat.add a (Nat.shiftLeft ih (nat_lit 6))) l

@[expose] noncomputable def pget (p j : Nat) : Nat :=
  Nat.land (Nat.shiftRight p (Nat.mul (nat_lit 6) j)) (nat_lit 63)

@[expose] noncomputable def pcomp (p : Nat) (k : Nat) : Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
    (fun _ ih q => Nat.add (pget p (Nat.land q (nat_lit 63)))
      (Nat.shiftLeft (ih (Nat.shiftRight q (nat_lit 6))) (nat_lit 6))) k


@[expose] noncomputable def getK (l : List Nat) (i : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
    (fun x _ ih j => Bool.rec (motive := fun _ => Nat) (ih (Nat.sub j 1)) x (Nat.beq j 0)) l i


@[expose] noncomputable def letK {n : Nat} (LP LPi : List Nat) (l : Fin n × Bool) : Nat :=
  getK (Bool.rec (motive := fun _ => List Nat) LPi LP l.2) l.1

@[expose] noncomputable def evFrom {n : Nat} (N : Nat) (LP LPi : List Nat) (w : List (Fin n × Bool)) :
    Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
    (fun l _ ih acc => ih (pcomp acc N (letK LP LPi l))) w

@[expose] noncomputable def evK {n : Nat} (N : Nat) (LP LPi : List Nat) (w : List (Fin n × Bool)) :
    Nat :=
  evFrom N LP LPi w (encL (List.range N))


end CFSG.KC.F48S
