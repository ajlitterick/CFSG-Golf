module

public import Certificates.Data.Kernel.LocalQT.BaseW

public section

namespace CFSG.KC.LQT.BT

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.LQT.S CFSG.KC.LQT.L CFSG.KC.LQT.PW CFSG.KC.LQT.BC
open CFSG.KC.LQT.PP CFSG.KC.LQT.BW

@[expose] noncomputable def nodesT (n w : Nat) (prog : List (Nat × Nat)) (TF : Nat → Nat)
    (lo len : Nat) : Bool :=
  allR lo len fun j => impB (andB (Nat.ble 2 j) (Nat.blt j (Nat.add (lenA prog) 2)))
    ((fun p => Nat.beq (TF j) (mulW n w (TF p.1) (TF p.2))) (nthP prog (Nat.sub j 2)))

@[expose] noncomputable def rowW (w x k : Nat) : Nat :=
  Nat.land (Nat.shiftRight x (Nat.mul (Nat.mul 64 w) k))
    (Nat.sub (Nat.shiftLeft 1 (Nat.mul 64 w)) 1)

@[expose] noncomputable def imgR (w RS : Nat) (RT : Nat → Nat) (t p : Nat) : Nat :=
  Nat.land (Nat.shiftRight (RT (Nat.add (Nat.mul t RS) (Nat.shiftRight p 6)))
    (Nat.mul w (Nat.land p 63))) (Nat.sub (Nat.shiftLeft 1 w) 1)

@[expose] noncomputable def imgsR (w RS : Nat) (RT : Nat → Nat) (t : Nat) (l : List Nat) :
    List Nat :=
  List.rec (motive := fun _ => List Nat) []
    (fun x _ ih => letLs (imgR w RS RT t x) fun y => List.cons y ih) l

@[expose] noncomputable def rowsT (w RS : Nat) (RT : Nat → Nat) (G : List Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun g _ ih t => andB (allR 0 RS fun k => Nat.beq (RT (Nat.add (Nat.mul t RS) k)) (rowW w g k))
      (ih (Nat.succ t))) G 0

@[expose] noncomputable def rangeK (m : Nat) : List Nat :=
  Nat.rec (motive := fun _ => Nat → List Nat) (fun _ => [])
    (fun _ ih i => List.cons i (ih (Nat.succ i))) m 0

@[expose] noncomputable def fstT (TF : Nat → Nat) (qp : List (Nat × Nat)) : List Nat :=
  List.rec (motive := fun _ => List Nat) [] (fun p _ ih => List.cons (TF p.1) ih) qp


end CFSG.KC.LQT.BT

end
