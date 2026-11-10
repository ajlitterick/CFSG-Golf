module

public import CFSG.Certificates.Kernel.Orders.Mat

public section

namespace CFSG.KC.Ord

open CFSG.KC.Loop

@[expose] noncomputable def add3 (N x1 x2 y1 y2 : Nat) : Nat :=
  (fun t => Nat.add (Nat.xor (Nat.lor x2 y2) t) (Nat.shiftLeft (Nat.xor (Nat.lor x1 y1) t) N))
    (Nat.xor (Nat.lor x1 y2) (Nat.lor x2 y1))

@[expose] noncomputable def addP3 (N LO acc y1 y2 : Nat) : Nat :=
  add3 N (Nat.land acc LO) (Nat.shiftRight acc N) y1 y2

@[expose] noncomputable def step3 (d N LO CI RM A B k acc : Nat) : Nat :=
  (fun a1 a2 b1 b2 => addP3 N LO acc (Nat.add (Nat.mul a1 b1) (Nat.mul a2 b2))
      (Nat.add (Nat.mul a1 b2) (Nat.mul a2 b1)))
    (Nat.land (Nat.shiftRight A k) CI) (Nat.land (Nat.shiftRight A (Nat.add N k)) CI)
    (Nat.land (Nat.shiftRight B (Nat.mul d k)) RM) (Nat.land (Nat.shiftRight B (Nat.add N (Nat.mul d k))) RM)

@[expose] noncomputable def mul3 (d N LO CI RM A B : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun k acc => strictN acc (fun a => step3 d N LO CI RM A B k a)) d

@[expose] noncomputable def mulLoop3 (d N CI RM A1 A2 B1 B2 : Nat) : Nat → Nat → Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → Nat) (fun _ x1 x2 => Nat.add x1 (Nat.shiftLeft x2 N))
    (fun _ ih k x1 x2 =>
      (fun a1 a2 b1 b2 => (fun q m => (fun t => strictN (Nat.xor (Nat.lor x2 m) t) (fun z1 =>
          strictN (Nat.xor (Nat.lor x1 q) t) (fun z2 => ih (Nat.succ k) z1 z2)))
          (Nat.xor (Nat.lor x1 m) (Nat.lor x2 q)))
        (Nat.add (Nat.mul a1 b1) (Nat.mul a2 b2)) (Nat.add (Nat.mul a1 b2) (Nat.mul a2 b1)))
      (Nat.land (Nat.shiftRight A1 k) CI) (Nat.land (Nat.shiftRight A2 k) CI)
      (Nat.land (Nat.shiftRight B1 (Nat.mul d k)) RM) (Nat.land (Nat.shiftRight B2 (Nat.mul d k)) RM))

@[expose] noncomputable def mul3s (d N LO CI RM A B : Nat) : Nat :=
  strictN (Nat.land A LO) (fun A1 => strictN (Nat.shiftRight A N) (fun A2 =>
    strictN (Nat.land B LO) (fun B1 => strictN (Nat.shiftRight B N) (fun B2 =>
      mulLoop3 d N CI RM A1 A2 B1 B2 d (nat_lit 0) (nat_lit 0) (nat_lit 0)))))

@[expose] noncomputable def valid3 (N LO X : Nat) : Bool :=
  andB (Nat.beq (Nat.shiftRight X (Nat.add N N)) (nat_lit 0))
    (Nat.beq (Nat.land (Nat.land X LO) (Nat.shiftRight X N)) (nat_lit 0))

@[expose] noncomputable def vstep3 (d N RM v M k acc : Nat) : Nat :=
  (fun e1 e2 r1 r2 => add3 d (Nat.land acc RM) (Nat.shiftRight acc d)
      (Nat.add (Nat.mul e1 r1) (Nat.mul e2 r2)) (Nat.add (Nat.mul e1 r2) (Nat.mul e2 r1)))
    (Nat.land (Nat.shiftRight v k) (nat_lit 1)) (Nat.land (Nat.shiftRight v (Nat.add d k)) (nat_lit 1))
    (Nat.land (Nat.shiftRight M (Nat.mul d k)) RM) (Nat.land (Nat.shiftRight M (Nat.add N (Nat.mul d k))) RM)

@[expose] noncomputable def vec3 (d N RM v M : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun k acc => strictN acc (fun a => vstep3 d N RM v M k a)) d


@[expose] noncomputable def consts3OK (d f N LO RM CI ONE UP : Nat) : Bool :=
  andB (Nat.ble (nat_lit 1) d)
  (andB (Nat.ble d (Nat.shiftLeft (nat_lit 1) (Nat.sub f (nat_lit 1))))
  (andB (Nat.beq N (Nat.mul d d))
  (andB (Nat.beq LO (Nat.sub (Nat.shiftLeft (nat_lit 1) N) (nat_lit 1)))
  (andB (Nat.beq RM (Nat.sub (Nat.shiftLeft (nat_lit 1) d) (nat_lit 1)))
  (andB (Nat.beq CI (rep1 d d))
  (andB (Nat.beq ONE (rep1 (Nat.succ d) d))
    (Nat.beq UP (Nat.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun i acc => Nat.lor acc (Nat.shiftLeft
        (Nat.sub (Nat.shiftLeft (nat_lit 1) (Nat.sub (Nat.sub d i) (nat_lit 1))) (nat_lit 1))
        (Nat.succ (Nat.mul (Nat.succ d) i)))) d))))))))

end CFSG.KC.Ord

end
