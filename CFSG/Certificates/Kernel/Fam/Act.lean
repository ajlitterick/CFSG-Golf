module

public import CFSG.Certificates.Kernel.Fam.Lin

public section

namespace CFSG.KC.Fam

open CFSG.KC.Loop CFSG.KC.Ord

@[expose] noncomputable def tget (T : Nat → Nat) (sh rb i : Nat) : Nat :=
  strictN (Nat.shiftRight i sh) (fun j =>
    bitsN (T j) (Nat.mul rb (Nat.land i (Nat.sub (Nat.shiftLeft (nat_lit 1) sh) (nat_lit 1)))) rb)


@[expose] noncomputable def actRange (V P : Nat → Nat) (vm : Nat → Nat → Nat) (vldV : Nat → Bool) (M n lo m : Nat) :
    Bool :=
  andB (Nat.ble (Nat.add lo m) n) (Nat.rec (motive := fun _ => Bool) true
    (fun t ih => andB ih ((fun i => andB (vldV (V i)) (andB (Nat.blt (P i) n) (Nat.beq (vm (V i) M) (V (P i)))))
      (Nat.add lo t))) m)

@[expose] noncomputable def tposeOK (vld : Nat → Bool) (w S d A AT : Nat) : Bool :=
  andB (vld A) (andB (vld AT) (allBelow (Nat.mul d d) (Nat.add (Nat.shiftRight (Nat.mul d d) (nat_lit 6)) (nat_lit 1))
    (fun k => (fun i j => Nat.beq (bitsN A (Nat.add (Nat.mul S i) (Nat.mul w j)) w)
        (bitsN AT (Nat.add (Nat.mul S j) (Nat.mul w i)) w))
      (Nat.div k d) (Nat.mod k d))))


@[expose] noncomputable def kdiag (d i : Nat) : Nat :=
  Nat.sub (Nat.mul i d) (Nat.div (Nat.mul i (Nat.sub i (nat_lit 1))) (nat_lit 2))

@[expose] noncomputable def diagForm (w d l : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i acc => Nat.lor acc (Nat.shiftLeft (bitsN l (Nat.mul w i) (nat_lit 1)) (kdiag d i))) d


@[expose] noncomputable def laneMagic (w : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun k acc => Nat.lor acc (Nat.shiftLeft (nat_lit 1) (Nat.mul (Nat.sub w (nat_lit 1)) k))) w

@[expose] noncomputable def lanePack (w n x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun c acc => Nat.lor acc (Nat.shiftLeft
      (Nat.land (Nat.shiftRight (Nat.mul (bitsN x (Nat.mul (Nat.mul w w) c) (Nat.mul w w)) (laneMagic w))
        (Nat.mul (Nat.sub w (nat_lit 1)) (Nat.sub w (nat_lit 1)))) (Nat.sub (Nat.shiftLeft (nat_lit 1) w) (nat_lit 1)))
      (Nat.mul w c)))
    (Nat.div (Nat.add n (Nat.sub w (nat_lit 1))) w)

@[expose] noncomputable def laneLow (w n : Nat) : Nat :=
  Nat.div (Nat.sub (Nat.shiftLeft (nat_lit 1) (Nat.mul w n)) (nat_lit 1))
    (Nat.sub (Nat.shiftLeft (nat_lit 1) w) (nat_lit 1))

@[expose] noncomputable def bitMat (w S d C : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i acc => Nat.lor acc (Nat.shiftLeft
      (lanePack w d (Nat.land (bitsN C (Nat.mul S i) (Nat.mul w d)) (laneLow w d))) (Nat.mul d i))) d


@[expose] noncomputable def repsOK (LB : Nat → Nat) (RP rw r n : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun c ih => andB ih ((fun rho => andB (Nat.blt rho n) (Nat.beq (LB rho) c)) (bitsN RP (Nat.mul rw c) rw))) r


end CFSG.KC.Fam

end
