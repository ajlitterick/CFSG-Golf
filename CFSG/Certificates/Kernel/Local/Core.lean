module

public import CFSG.Certificates.Kernel.Enum.DefsM

public section

namespace CFSG.KC.Local

open CFSG.KC.Enum

@[expose] noncomputable def pmkL (w m p q : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun lo => fld(p, Nat.mul w fld(q, Nat.mul w lo, m), m))
    (fun d ih lo => Nat.lor (ih lo)
      (Nat.shiftLeft (ih (Nat.add lo (Nat.shiftLeft (nat_lit 1) d))) (Nat.mul w (Nat.shiftLeft (nat_lit 1) d))))

@[expose] noncomputable def pmkL8 (w m p q : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat)
    (fun lo => Nat.lor
      (Nat.lor
        (Nat.lor fld(p, Nat.mul w fld(q, Nat.mul w lo, m), m)
          (Nat.shiftLeft fld(p, Nat.mul w fld(q, Nat.mul w (Nat.add lo (nat_lit 1)), m), m) w))
        (Nat.shiftLeft
          (Nat.lor fld(p, Nat.mul w fld(q, Nat.mul w (Nat.add lo (nat_lit 2)), m), m)
            (Nat.shiftLeft fld(p, Nat.mul w fld(q, Nat.mul w (Nat.add lo (nat_lit 3)), m), m) w))
          (Nat.mul w (nat_lit 2))))
      (Nat.shiftLeft
        (Nat.lor
          (Nat.lor fld(p, Nat.mul w fld(q, Nat.mul w (Nat.add lo (nat_lit 4)), m), m)
            (Nat.shiftLeft fld(p, Nat.mul w fld(q, Nat.mul w (Nat.add lo (nat_lit 5)), m), m) w))
          (Nat.shiftLeft
            (Nat.lor fld(p, Nat.mul w fld(q, Nat.mul w (Nat.add lo (nat_lit 6)), m), m)
              (Nat.shiftLeft fld(p, Nat.mul w fld(q, Nat.mul w (Nat.add lo (nat_lit 7)), m), m) w))
            (Nat.mul w (nat_lit 2))))
        (Nat.mul w (nat_lit 4))))
    (fun d ih lo => Nat.lor (ih lo)
      (Nat.shiftLeft (ih (Nat.add lo (Nat.shiftLeft (nat_lit 8) d))) (Nat.mul w (Nat.shiftLeft (nat_lit 8) d))))

@[expose] noncomputable def pcompL (n w m p q : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ _ => nat_lit 0)
    (fun _ ih b rem => nIf(Nat.beq rem (nat_lit 0), nat_lit 0,
      nIf(Nat.beq (Nat.land rem (nat_lit 1)) (nat_lit 0), ih (Nat.succ b) (Nat.shiftRight rem (nat_lit 1)),
        strictN (Nat.sub n (Nat.shiftLeft rem b)) (fun lo =>
          Nat.lor (Nat.shiftLeft (nIf(Nat.blt b (nat_lit 3), pmkL w m p q b lo, pmkL8 w m p q (Nat.sub b (nat_lit 3)) lo))
              (Nat.mul w lo))
            (ih (Nat.succ b) (Nat.shiftRight rem (nat_lit 1)))))))
    (nat_lit 32) (nat_lit 0) n


@[expose] noncomputable def allB (b : Nat) (f : Nat → Bool) (len : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun l ih => bAnd(f (Nat.add b l), ih)) len

@[expose] noncomputable def allL (n : Nat) (f : Nat → Bool) : Bool :=
  (fun q => bAnd(allB (Nat.shiftLeft q (nat_lit 6)) f (Nat.land n (nat_lit 63)),
      Nat.rec (motive := fun _ => Bool) true
        (fun h ih => bAnd(allB (Nat.shiftLeft h (nat_lit 6)) f (nat_lit 64), ih)) q))
    (Nat.shiftRight n (nat_lit 6))

@[expose] noncomputable def rgetL (T : Nat → Nat) (sh lm rb rm i : Nat) : Nat :=
  strictN (Nat.shiftRight i sh) (fun b => fld(T b, Nat.mul rb (Nat.land i lm), rm))

@[expose] noncomputable def pop64 (x : Nat) : Nat :=
  (fun a => (fun b => (fun c =>
      Nat.shiftRight (Nat.land (Nat.mul c (nat_lit 72340172838076673)) (nat_lit 18446744073709551615)) (nat_lit 56))
    (Nat.land (Nat.add b (Nat.shiftRight b (nat_lit 4))) (nat_lit 1085102592571150095)))
    (Nat.add (Nat.land a (nat_lit 3689348814741910323)) (Nat.land (Nat.shiftRight a (nat_lit 2)) (nat_lit 3689348814741910323))))
    (Nat.sub x (Nat.land (Nat.shiftRight x (nat_lit 1)) (nat_lit 6148914691236517205)))

@[expose] noncomputable def wordFold (f : Nat → Nat → Nat) (base : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ s => s)
    (fun _ ih w s => nIf(Nat.beq w (nat_lit 0), s,
      (fun low => strictN (f (Nat.add base (pop64 (Nat.sub low (nat_lit 1)))) s) (fun s2 => ih (Nat.xor w low) s2))
      (Nat.land w (Nat.xor w (Nat.sub w (nat_lit 1))))))
    (nat_lit 64)

@[expose] noncomputable def foldBits (n : Nat) (f : Nat → Nat → Nat) (M s : Nat) : Nat :=
  (fun M' => Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ s => s)
    (fun _ ih j s => strictN (wordFold f (Nat.shiftLeft j (nat_lit 6))
        (Nat.land (Nat.shiftRight M' (Nat.shiftLeft j (nat_lit 6))) (nat_lit 18446744073709551615)) s)
      (fun s2 => ih (Nat.succ j) s2))
    (Nat.shiftRight (Nat.add n (nat_lit 63)) (nat_lit 6)) (nat_lit 0) s)
  (Nat.land M (Nat.sub (Nat.shiftLeft (nat_lit 1) n) (nat_lit 1)))

@[expose] noncomputable def wordAll (f : Nat → Bool) (base : Nat) : Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun _ ih w => bIf(Nat.beq w (nat_lit 0), true,
      (fun low => bAnd(f (Nat.add base (pop64 (Nat.sub low (nat_lit 1)))), ih (Nat.xor w low)))
      (Nat.land w (Nat.xor w (Nat.sub w (nat_lit 1))))))
    (nat_lit 64)

@[expose] noncomputable def allBits (n : Nat) (f : Nat → Bool) (M : Nat) : Bool :=
  (fun M' => Nat.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun _ ih j => bAnd(wordAll f (Nat.shiftLeft j (nat_lit 6))
        (Nat.land (Nat.shiftRight M' (Nat.shiftLeft j (nat_lit 6))) (nat_lit 18446744073709551615)),
      ih (Nat.succ j)))
    (Nat.shiftRight (Nat.add n (nat_lit 63)) (nat_lit 6)) (nat_lit 0))
  (Nat.land M (Nat.sub (Nat.shiftLeft (nat_lit 1) n) (nat_lit 1)))

@[expose] noncomputable def mulK (K a b c x y : Nat) : Nat :=
  nIf(Nat.beq K (nat_lit 0), pcompL a b c x y, mmul a b c x y)


@[expose] noncomputable def commK (K a b c x y : Nat) : Bool :=
  Nat.beq (mulK K a b c x y) (mulK K a b c y x)

@[expose] noncomputable def commAll (K a b c x : Nat) (l : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun y _ ih => bAnd(commK K a b c x y, ih)) l

@[expose] noncomputable def hd (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun x _ _ => x) l


@[expose] noncomputable def elt (T : Nat → Nat) (sh lm rb rm em i : Nat) : Nat :=
  Nat.land (rgetL T sh lm rb rm i) em


@[expose] noncomputable def restrOK (w m p PT pw pm k ρ rw rm : Nat) : Bool :=
  bAnd(Nat.blt ρ (Nat.shiftLeft (nat_lit 1) (Nat.mul rw k)),
    allL k (fun j => strictB (pg rw rm ρ j) (fun t =>
      bAnd(Nat.blt t k, Nat.beq (pg pw pm PT t) (pg w m p (pg pw pm PT j))))))

@[expose] noncomputable def ptsOK (n PT pw pm k : Nat) : Bool :=
  bAnd(Nat.blt (pg pw pm PT (Nat.sub k (nat_lit 1))) n,
    allL (Nat.sub k (nat_lit 1)) (fun j => Nat.blt (pg pw pm PT j) (pg pw pm PT (Nat.succ j))))


end CFSG.KC.Local

end
