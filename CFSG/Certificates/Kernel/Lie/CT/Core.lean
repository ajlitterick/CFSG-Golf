module

public import CFSG.Certificates.Kernel.Common.Loop

public section

namespace CFSG.KLie.CT

@[expose] noncomputable def andB (a b : Bool) : Bool := Bool.rec false b a
@[expose] noncomputable def orB (a b : Bool) : Bool := Bool.rec b true a
@[expose] noncomputable def notB (a : Bool) : Bool := Bool.rec true false a

@[expose] noncomputable def pw2 (w : Nat) : Nat := Nat.shiftLeft (nat_lit 1) w

@[expose] noncomputable def maskN (w : Nat) : Nat := Nat.sub (pw2 w) (nat_lit 1)

@[expose] noncomputable def fget (X i w : Nat) : Nat :=
  Nat.land (Nat.shiftRight X (Nat.mul i w)) (maskN w)

@[expose] noncomputable def bit (X i : Nat) : Bool := Nat.beq (Nat.land (Nat.shiftRight X i) (nat_lit 1)) (nat_lit 1)

@[expose] noncomputable def allN (n : Nat) (f : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun i ih => andB (f i) ih) n

@[expose] noncomputable def anyN (n : Nat) (f : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) false (fun i ih => orB (f i) ih) n

@[expose] noncomputable def orN (n : Nat) (f : Nat → Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0) (fun i ih => Nat.lor (f i) ih) n

@[expose] noncomputable def sumN (n : Nat) (f : Nat → Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0) (fun i ih => Nat.add (f i) ih) n

@[expose] noncomputable def prodN (n : Nat) (f : Nat → Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 1) (fun i ih => Nat.mul (f i) ih) n

@[expose] noncomputable def maxN (n : Nat) (f : Nat → Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i ih => Bool.rec (motive := fun _ => Nat) ih (f i) (Nat.blt ih (f i))) n

@[expose] noncomputable def popc (w X : Nat) : Nat :=
  sumN w fun i => Nat.land (Nat.shiftRight X i) (nat_lit 1)


@[expose] noncomputable def sl (n : Nat) : Nat :=
  Nat.mul (pw2 n) (Nat.sub (pw2 (Nat.add n n)) (nat_lit 1))


@[expose] noncomputable def bitsOf (L : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun a _ ih => Nat.lor (pw2 a) ih) L

end CFSG.KLie.CT

end
