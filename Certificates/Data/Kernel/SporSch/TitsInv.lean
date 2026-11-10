module

public import Certificates.Data.Kernel.SporSch.TitsEnum5
public import Certificates.Data.Kernel.Spor.Prim

public section

namespace CFSG.KS.SporSch

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.Mathieu

@[expose] noncomputable def pgR (p i : Nat) : Nat :=
  pg 11 (mask 11) (Nat.land (Nat.shiftRight p (Nat.mul (nat_lit 704) (Nat.div i (nat_lit 64))))
    (mask (nat_lit 704))) (Nat.mod i (nat_lit 64))


@[expose] noncomputable def allA {α : Type} (f : α → Bool) (A : List α) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun a _ ih => bAnd(f a, ih)) A

@[expose] noncomputable def zipA {α : Type} (f : α → Nat → Bool) (A : List α) : List Nat → Bool :=
  List.rec (motive := fun _ => List Nat → Bool)
    (fun L => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) L)
    (fun a _ ih L => List.rec (motive := fun _ => Bool) false (fun l L' _ => bAnd(f a l, ih L')) L)
    A

@[expose] noncomputable def conjB (S SI : Nat → Nat) (Z T : Nat) (bw : Bool × List Int) (y : Nat) :
    Bool :=
  Prod.rec (motive := fun _ => Bool) (fun b wd =>
    strictB (wordK 1755 11 (mask 11) (pidn 1755 11) S SI wd) (fun x =>
      Nat.beq (pcomp 1755 11 (mask 11) (pcomp 1755 11 (mask 11) x
        (Bool.rec (motive := fun _ => Nat) T Z b)) (pinvS 1755 11 (mask 11) x)) y)) bw


@[expose] noncomputable def memN (p : Nat) (L : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun y _ ih => bIf(Nat.beq p y, true, ih)) L


@[expose] noncomputable def gptR (t0 t1 t2 t3 t4 i : Nat) : Nat :=
  pgR t0 (pgR t1 (pgR t2 (pgR t3 (pgR t4 i))))

@[expose] noncomputable def sqGR (G t0 t1 t2 t3 t4 : Nat) : Bool :=
  allN 1755 (fun i => strictB (gptR t0 t1 t2 t3 t4 (pgR G i)) (fun j =>
    Nat.beq (gptR t0 t1 t2 t3 t4 (pgR G j)) i))

@[expose] noncomputable def sqR (t0 t1 t2 t3 t4 : Nat) : Bool :=
  allN 1755 (fun i => Nat.beq (gptR t0 t1 t2 t3 t4 (gptR t0 t1 t2 t3 t4 i)) i)

@[expose] noncomputable def eqR (Z t0 t1 t2 t3 t4 : Nat) : Bool :=
  allN 1755 (fun i => Nat.beq (gptR t0 t1 t2 t3 t4 i) (pgR Z i))

@[expose] noncomputable def memR (L : List Nat) (t0 t1 t2 t3 t4 : Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun y _ ih => bIf(eqR y t0 t1 t2 t3 t4, true, ih)) L

@[expose] noncomputable def conjR (T y t0 t1 t2 t3 t4 : Nat) : Bool :=
  allN 1755 (fun i => Nat.beq (gptR t0 t1 t2 t3 t4 (pgR T i)) (pgR y (gptR t0 t1 t2 t3 t4 i)))

@[expose] noncomputable def commR (G t0 t1 t2 t3 t4 : Nat) : Bool :=
  allN 1755 (fun i => Nat.beq (gptR t0 t1 t2 t3 t4 (pgR G i)) (pgR G (gptR t0 t1 t2 t3 t4 i)))


@[expose] noncomputable def wPt (S SI : Nat → Nat) (wd : List Int) (i : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun i => i)
    (fun z _ ih i => strictN (icode z) (fun c => strictN (ih i) (fun j =>
      pgR (nIf(Nat.beq (Nat.land c (nat_lit 1)) (nat_lit 0),
        S (Nat.sub (Nat.shiftRight c (nat_lit 1)) (nat_lit 1)),
        SI (Nat.sub (Nat.shiftRight c (nat_lit 1)) (nat_lit 1)))) j))) wd i

@[expose] noncomputable def conjW (S SI : Nat → Nat) (wd : List Int) (A y : Nat) : Bool :=
  bAnd(lettersK (nat_lit 13) wd,
    allN 1755 (fun i => Nat.beq (wPt S SI wd (pgR A i)) (pgR y (wPt S SI wd i))))

@[expose] noncomputable def exclW (S SI : Nat → Nat) (wd : List Int) (T y : Nat) : Bool :=
  bAnd(lettersK (nat_lit 13) wd,
    allN 1755 (fun i => Nat.beq (wPt S SI wd (pgR y i)) (pgR T (wPt S SI wd i))))


end CFSG.KS.SporSch

end
