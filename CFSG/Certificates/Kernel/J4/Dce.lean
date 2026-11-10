module

public import CFSG.Certificates.Kernel.J4.M12

public section

namespace CFSG.KJ4

@[expose] def mask144 : Nat := nat_lit 22300745198530623141535718272648361505980415

@[expose] noncomputable def fIdx (F : Nat) : Nat := Nat.land F (nat_lit 1048575)
@[expose] noncomputable def fD (F : Nat) : Nat := Nat.land (Nat.shiftRight F (nat_lit 20)) (nat_lit 65535)
@[expose] noncomputable def fJ (F : Nat) : Nat := Nat.land (Nat.shiftRight F (nat_lit 36)) (nat_lit 65535)
@[expose] noncomputable def fDp (F : Nat) : Nat := Nat.land (Nat.shiftRight F (nat_lit 52)) (nat_lit 65535)
@[expose] noncomputable def fPi (F : Nat) : Nat := Nat.land (Nat.shiftRight F (nat_lit 68)) mask144
@[expose] noncomputable def fN (F : Nat) : Nat := Nat.shiftRight F (nat_lit 212)

@[expose] noncomputable def oJ (O : Nat) : Nat := Nat.land O (nat_lit 65535)
@[expose] noncomputable def oP (O : Nat) : Nat := Nat.land (Nat.shiftRight O (nat_lit 16)) (nat_lit 68719476735)
@[expose] noncomputable def oG (O : Nat) : Nat := Nat.land (Nat.shiftRight O (nat_lit 52)) mask144
@[expose] noncomputable def oGi (O : Nat) : Nat := Nat.shiftRight O (nat_lit 196)

@[expose] noncomputable def lamT (L : Nat) : Nat := Nat.land L mask144
@[expose] noncomputable def lamP (L : Nat) : Nat := Nat.shiftRight L (nat_lit 144)

@[expose] noncomputable def letAt (c : Nat) : Nat := Nat.land (Nat.shiftRight c (nat_lit 1)) (nat_lit 255)
@[expose] noncomputable def letsAt (c m : Nat) : Nat :=
  Nat.land (Nat.shiftRight c (nat_lit 1)) (Nat.sub (Nat.shiftLeft (nat_lit 1) (Nat.mul (nat_lit 8) m)) (nat_lit 1))
@[expose] noncomputable def adv (c m S : Nat) : Nat :=
  Nat.lor (Nat.lor (Nat.land c (nat_lit 1)) S)
    (Nat.shiftLeft (Nat.shiftRight c (Nat.add (nat_lit 1) (Nat.mul (nat_lit 8) m))) (nat_lit 1))
@[expose] noncomputable def wInit (W n : Nat) : Nat :=
  Nat.shiftLeft (Nat.lor W (Nat.shiftLeft (nat_lit 254) (Nat.mul (nat_lit 8) n))) (nat_lit 1)

abbrev St := Nat × (Nat × Nat)

@[expose] noncomputable def bad : St := Prod.mk (nat_lit 65535) (Prod.mk (nat_lit 0) (nat_lit 0))

@[expose] noncomputable def st (d p c : Nat) : St := Prod.mk d (Prod.mk p c)

@[expose] noncomputable def sN (a L : Nat) (s : St) : St :=
  Prod.rec (motive := fun _ => St) (fun d pc => Prod.rec (motive := fun _ => St) (fun p c =>
    Bool.rec bad (Prod.mk d (Prod.mk (mul12 p L) (adv c (nat_lit 1) (nat_lit 0))))
      (Nat.beq (letAt c) a)) pc) s


@[expose] noncomputable def inT (TH L h TAU : Nat) : Bool :=
  andB (chkPt TH TAU TH h) (Nat.beq (Nat.land TAU colMask) (Nat.land L colMask))


abbrev St4 := Nat × (Nat × (Nat × Nat))

@[expose] noncomputable def bad4 : St4 := Prod.mk (nat_lit 65535) (Prod.mk (nat_lit 0) (Prod.mk (nat_lit 0) (nat_lit 0)))

@[expose] noncomputable def st4 (d p n c : Nat) : St4 := Prod.mk d (Prod.mk p (Prod.mk n c))

@[expose] noncomputable def mN (SW m SG : Nat) (s : St4) : St4 :=
  Prod.rec (motive := fun _ => St4) (fun d r => Prod.rec (motive := fun _ => St4) (fun p r2 =>
    Prod.rec (motive := fun _ => St4) (fun n c =>
      Bool.rec bad4 (Prod.mk d (Prod.mk (mul12 p SG) (Prod.mk n (adv c m (nat_lit 0)))))
        (Nat.beq (letsAt c m) SW)) r2) r) s


@[expose] noncomputable def chkTree (F : Nat) : Bool :=
  andB (Nat.blt (fD F) (fDp F)) (andB (Nat.blt (nat_lit 0) (fJ F))
    (andB (Nat.beq (fPi F) ident12) (orB (Nat.beq (fN F) ident12) (Nat.beq (fN F) (nat_lit 0)))))


@[expose] noncomputable def chkOm (TH O H h : Nat) : Bool :=
  andB (Nat.blt (nat_lit 0) (oJ O)) (andB (ptOK (oP O)) (andB (chkPt TH (oG O) (oP O) h)
    (andB (Nat.beq (mul12 (oG O) (oGi O)) ident12) (Nat.beq (oG O) H))))

end CFSG.KJ4

end
