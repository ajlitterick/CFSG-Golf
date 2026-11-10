module

public import CFSG.Certificates.Kernel.Common.Lce
public import CFSG.Certificates.Kernel.Common.Loop
public import CFSG.Certificates.Kernel.MonsterConv.Orb

public section

namespace CFSG.KC.MonsterConv.MatChain

open CFSG.KC CFSG.KC.Loop CFSG.KC.MonsterConv.Orb

@[expose] noncomputable def lows (d : Nat) : Nat :=
  Nat.div (Nat.sub (Nat.shiftLeft (nat_lit 1) (Nat.mul d d)) (nat_lit 1))
    (Nat.sub (Nat.shiftLeft (nat_lit 1) d) (nat_lit 1))

@[expose] noncomputable def mmul (d Lw O A B : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun l acc => Nat.xor acc
      (Nat.land (Nat.mul (Nat.land (Nat.shiftRight A l) Lw) O)
        (Nat.mul (fldW B (Nat.mul d l) d) Lw)))
    d

@[expose] noncomputable def vmul (d v M : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun l acc => Nat.xor acc
      (Nat.mul (fldW v l (nat_lit 1)) (fldW M (Nat.mul d l) d)))
    d

@[expose] noncomputable def ident (d : Nat) : Nat :=
  Nat.div (Nat.sub (Nat.shiftLeft (nat_lit 1) (Nat.mul (Nat.add d (nat_lit 1)) d)) (nat_lit 1))
    (Nat.sub (Nat.shiftLeft (nat_lit 1) (Nat.add d (nat_lit 1))) (nat_lit 1))

@[expose] noncomputable def invOK (d : Nat) (S Si : Nat → Nat) (m : Nat) : Bool :=
  allBelow m (Nat.add (Nat.shiftRight m (nat_lit 6)) (nat_lit 1))
    (fun s => Nat.beq (mmul d (lows d) (Nat.sub (Nat.shiftLeft (nat_lit 1) d) (nat_lit 1)) (S s) (Si s)) (ident d))

@[expose] noncomputable def wordMat (d : Nat) (S Si : Nat → Nat) (W n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (ident d)
    (fun q acc => strictN acc (fun a =>
      mmul d (lows d) (Nat.sub (Nat.shiftLeft (nat_lit 1) d) (nat_lit 1)) a
        ((fun c => Bool.rec (motive := fun _ => Nat) (S (Nat.shiftRight c (nat_lit 1)))
            (Si (Nat.shiftRight c (nat_lit 1))) (Nat.beq (Nat.land c (nat_lit 1)) (nat_lit 1)))
          (fldW W (Nat.mul (nat_lit 8) q) (nat_lit 8)))))
    n


@[expose] noncomputable def treeOK (d : Nat) (S bv gl : Nat → Nat) (blk tm : Nat → Nat → Nat)
    (F n l lo c : Nat) : Bool :=
  andB
    (orbRange (blk l) (fun g y => Bool.rec (motive := fun _ => Nat) (Nat.shiftLeft (nat_lit 1) d)
        (vmul d y (S g)) (Nat.blt (nat_lit 0) (Nat.land (gl l) (Nat.shiftLeft (nat_lit 1) g))))
      F n (bv l) lo c)
    (allBelow c (Nat.add (Nat.shiftRight c (nat_lit 6)) (nat_lit 1)) (fun j =>
      (fun i => (fun vb pb gb db => (fun r => andB
          (Nat.beq (vmul d (bv l) (tm l i)) (fldW r (nat_lit 0) vb))
          (Bool.rec (motive := fun _ => Bool)
            (Nat.beq (mmul d (lows d) (Nat.sub (Nat.shiftLeft (nat_lit 1) d) (nat_lit 1))
              (tm l (fldW r vb pb)) (S (fldW r (Nat.add vb pb) gb))) (tm l i))
            (Nat.beq (tm l i) (ident d))
            (Nat.beq (fldW r (Nat.add (Nat.add vb pb) gb) db) (nat_lit 0))))
        (getRec (blk l) (Nat.add (Nat.add vb pb) (Nat.add gb db)) i))
        (Nat.land F (nat_lit 255)) (Nat.land (Nat.shiftRight F (nat_lit 8)) (nat_lit 255))
        (Nat.land (Nat.shiftRight F (nat_lit 16)) (nat_lit 255)) (Nat.shiftRight F (nat_lit 24)))
      (Nat.add lo j)))


@[expose] noncomputable def memOK (d : Nat) (osz : Nat → Nat) (tm : Nat → Nat → Nat) (L ib M e : Nat) : Bool :=
  (fun acc => andB (Nat.beq (Nat.land acc (nat_lit 1)) (nat_lit 1)) (Nat.beq (Nat.shiftRight acc (nat_lit 1)) M))
  (Nat.rec (motive := fun _ => Nat) (Nat.add (Nat.shiftLeft (ident d) (nat_lit 1)) (nat_lit 1))
    (fun k acc => strictN acc (fun a =>
      (fun lk yk => Bool.rec (motive := fun _ => Nat) (nat_lit 0)
          (Nat.add (Nat.shiftLeft (mmul d (lows d) (Nat.sub (Nat.shiftLeft (nat_lit 1) d) (nat_lit 1)) (tm lk yk)
            (Nat.shiftRight a (nat_lit 1))) (nat_lit 1)) (nat_lit 1))
          (andB (Nat.beq (Nat.land a (nat_lit 1)) (nat_lit 1)) (andB (Nat.blt lk L) (Nat.blt yk (osz lk)))))
        (fldW e (Nat.add (nat_lit 4) (Nat.mul (Nat.add ib (nat_lit 4)) k)) (nat_lit 4))
        (fldW e (Nat.add (nat_lit 8) (Nat.mul (Nat.add ib (nat_lit 4)) k)) ib)))
    (fldW e (nat_lit 0) (nat_lit 4)))

end CFSG.KC.MonsterConv.MatChain

end
