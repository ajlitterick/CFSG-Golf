module

public import CFSG.Certificates.Kernel.Orders.Cert

public section

namespace CFSG.KC.Fam

open CFSG.KC.Loop CFSG.KC.Ord


@[expose] noncomputable def treeOK (PJ Top : Nat → Nat) (mul : Nat → Nat → Nat) (vld : Nat → Bool) (ONE nop PT d : Nat) : Bool :=
  andB (Nat.beq (PJ (nat_lit 0)) ONE) (Nat.rec (motive := fun _ => Bool) true
    (fun s ih => andB ih ((fun j => (fun pj tj => andB (vld (PJ j)) (andB (Nat.blt pj j) (andB (Nat.blt tj nop)
        (Nat.beq (PJ j) (mul (Top tj) (PJ pj))))))
      (bitsN PT (Nat.mul (nat_lit 16) j) (nat_lit 8)) (bitsN PT (Nat.add (Nat.mul (nat_lit 16) j) (nat_lit 8)) (nat_lit 8)))
      (Nat.succ s))) (Nat.sub d (nat_lit 1)))

@[expose] noncomputable def colsMat (PJ : Nat → Nat) (mul : Nat → Nat → Nat) (w d C0v : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun j acc => Nat.lor acc (Nat.shiftLeft (mul (PJ j) C0v) (Nat.mul w j))) d


@[expose] noncomputable def colOf (w S d v : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i acc => Nat.lor acc (Nat.shiftLeft (bitsN v (Nat.mul w i) w) (Nat.mul S i))) d

@[expose] noncomputable def lincomb (RB : Nat → Nat) (p w T L H nreg : Nat) (Ls : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun x _ ih => (fun c r => nIf(andB (Nat.blt c p) (regBelow r nreg),
        redP w L H p T (Nat.add ih (Nat.mul (RB r) c)), nat_lit 0))
      (Nat.land x (nat_lit 255)) (Nat.shiftRight x (nat_lit 8))) Ls

@[expose] noncomputable def treeVecOK (V : Nat → Nat) (vm : Nat → Nat → Nat) (G0 G1 v0 PT d : Nat) : Bool :=
  andB (Nat.beq (V (nat_lit 0)) v0) (Nat.rec (motive := fun _ => Bool) true
    (fun s ih => andB ih ((fun i => (fun pi li => andB (Nat.blt pi i) (andB (Nat.ble li (nat_lit 1))
        (Nat.beq (V i) (vm (V pi) (nIf(Nat.beq li (nat_lit 0), G0, G1))))))
      (bitsN PT (Nat.mul (nat_lit 24) i) (nat_lit 16)) (bitsN PT (Nat.add (Nat.mul (nat_lit 24) i) (nat_lit 16)) (nat_lit 8)))
      (Nat.succ s))) (Nat.sub d (nat_lit 1)))

@[expose] noncomputable def rkerOK (p w T L H CM ONE : Nat) (mul : Nat → Nat → Nat) (vld vldV : Nat → Bool)
    (C Y C0v ur : Nat) : Bool :=
  andB (vld Y) (andB (vld C0v) (andB (Nat.beq (Nat.land C0v CM) C0v) (andB (vldV ur)
    (Nat.beq (redP w L H p T (Nat.add (mul Y C) (Nat.mul C0v ur))) ONE))))


@[expose] noncomputable def diagProd (p w S d U : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 1)
    (fun i acc => Nat.mod (Nat.mul acc (bitsN U (Nat.add (Nat.mul S i) (Nat.mul w i)) w)) p) d


end CFSG.KC.Fam

end
