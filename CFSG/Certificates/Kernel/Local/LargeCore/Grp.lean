module

public import CFSG.Certificates.Kernel.Common.Loop

public section

namespace CFSG.KC.LL

open CFSG.KC.Loop

@[expose] noncomputable def letB (v : Nat) (k : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) (k (nat_lit 0)) (fun n _ => k (Nat.succ n)) v

@[expose] noncomputable def fldW (r o w : Nat) : Nat :=
  Nat.land (Nat.shiftRight r o) (Nat.sub (Nat.shiftLeft (nat_lit 1) w) (nat_lit 1))

@[expose] noncomputable def getRec (blk : Nat → Nat) (RB i : Nat) : Nat :=
  strictN (Nat.shiftRight i (nat_lit 6)) (fun k =>
    fldW (blk k) (Nat.mul (Nat.land i (nat_lit 63)) RB) RB)

@[expose] noncomputable def recVal (blk : Nat → Nat) (RB vb i : Nat) : Nat :=
  fldW (getRec blk RB i) (nat_lit 0) vb

@[expose] noncomputable def pickL (l : List Nat) (j : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
    (fun x _ ih k => Nat.rec (motive := fun _ => Nat) x (fun k' _ => ih k') k) l j


@[expose] noncomputable def conjL (mul : Nat → Nat → Nat) (gs gis : List Nat) (j x : Nat) : Nat :=
  mul (mul (pickL gis j) x) (pickL gs j)


@[expose] noncomputable def memAt (blk : Nat → Nat) (RB vb n k x : Nat) : Bool :=
  bAnd(Nat.blt k n, Nat.beq (recVal blk RB vb k) x)

@[expose] noncomputable def wordR (mul : Nat → Nat → Nat) (gen : Nat → Nat) (ONE : Nat)
    (w : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
    (fun a _ ih acc => strictN (mul acc (gen a)) ih) w ONE


@[expose] noncomputable def commM (mul : Nat → Nat → Nat) (x y : Nat) : Bool :=
  Nat.beq (mul x y) (mul y x)

end CFSG.KC.LL

end
