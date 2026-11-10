module

public import CFSG.Certificates.Kernel.Common.Loop

public section

namespace CFSG.KLC.Fi22

open CFSG.KC.Loop

@[expose] noncomputable def sN (v : Nat) (k : Nat → Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (k (nat_lit 0)) (fun n _ => k (Nat.succ n)) v

@[expose] noncomputable def sB (v : Nat) (k : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) (k (nat_lit 0)) (fun n _ => k (Nat.succ n)) v

@[expose] noncomputable def andB (a b : Bool) : Bool := Bool.rec false b a
@[expose] noncomputable def orB (a b : Bool) : Bool := Bool.rec b true a
@[expose] noncomputable def notB (a : Bool) : Bool := Bool.rec true false a

@[expose] noncomputable def maskN (w : Nat) : Nat := Nat.sub (Nat.shiftLeft (nat_lit 1) w) (nat_lit 1)

@[expose] noncomputable def bt (x i : Nat) : Bool :=
  Nat.blt (nat_lit 0) (Nat.land x (Nat.shiftLeft (nat_lit 1) i))

@[expose] noncomputable def fw (X w k : Nat) : Nat :=
  Nat.land (Nat.shiftRight X (Nat.mul w k)) (maskN w)

@[expose] noncomputable def M4096 : Nat := maskN (nat_lit 4096)

@[expose] noncomputable def iterN (c : Nat) (f : Nat → Nat → Nat) (s : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun s => s)
    (fun i ih s => sN (f (Nat.sub (Nat.sub c (nat_lit 1)) i) s) ih) c s

@[expose] noncomputable def allLt (m : Nat) (f : Nat → Bool) : Bool :=
  allBelow m (Nat.add (Nat.shiftRight m (nat_lit 6)) (nat_lit 1)) f

@[expose] noncomputable def fsplitI (cb h : Nat) : Nat → Nat → ((Nat → Nat) → Bool) → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → ((Nat → Nat) → Bool) → Bool)
    (fun X base k => sB (Nat.lor (Nat.shiftLeft X (nat_lit 16)) base) (fun x => k (fun _ => x)))
    (fun j ih X base k => sB X (fun X =>
      sB (Nat.shiftLeft cb j) (fun w =>
        ih (Nat.land X (maskN w)) base (fun f0 =>
          ih (Nat.shiftRight X w) (Nat.add base (Nat.shiftLeft (nat_lit 1) j)) (fun f1 =>
            k (fun i => Bool.rec (motive := fun _ => Nat) (f0 i) (f1 i)
              (Nat.blt (nat_lit 0) (Nat.land i (Nat.shiftLeft (nat_lit 1) j))))))))) h

@[expose] noncomputable def fsplit (cb h : Nat) (X : Nat) (k : (Nat → Nat) → Bool) : Bool :=
  fsplitI cb h X (nat_lit 0) k

@[expose] noncomputable def ent (F : Nat → Nat) (p : Nat) : Nat :=
  sN (Nat.shiftRight p (nat_lit 6)) (fun c =>
    Nat.land (Nat.shiftRight (F c)
      (Nat.add (nat_lit 16) (Nat.shiftLeft (Nat.land p (nat_lit 63)) (nat_lit 4)))) (nat_lit 65535))

@[expose] noncomputable def rowAt (F : Nat → Nat) (u : Nat) : Nat :=
  sN (Nat.shiftRight u (nat_lit 4)) (fun c =>
    Nat.land (Nat.shiftRight (F c)
      (Nat.add (nat_lit 16) (Nat.shiftLeft (Nat.land u (nat_lit 15)) (nat_lit 12)))) M4096)

@[expose] noncomputable def stageDist (s : Nat) : Nat :=
  Nat.shiftLeft (nat_lit 1) (Nat.add (Nat.sub (nat_lit 11) s) (Nat.sub s (nat_lit 11)))

@[expose] noncomputable def nwMask (NW s : Nat) : Nat :=
  Nat.land (Nat.shiftRight NW (Nat.shiftLeft s (nat_lit 12))) M4096

@[expose] noncomputable def stage (X m d : Nat) : Nat :=
  sN (Nat.land (Nat.xor X (Nat.shiftRight X d)) m) (fun t => Nat.xor X (Nat.lor t (Nat.shiftLeft t d)))

@[expose] noncomputable def applyNW (NW R X : Nat) : Nat :=
  iterN (nat_lit 23) (fun s Y => stage Y (Nat.mul (nwMask NW s) R) (stageDist s)) X

@[expose] noncomputable def applyInvNW (NW R X : Nat) : Nat :=
  iterN (nat_lit 23) (fun s Y =>
    stage Y (Nat.mul (nwMask NW (Nat.sub (nat_lit 22) s)) R) (stageDist (Nat.sub (nat_lit 22) s))) X

@[expose] noncomputable def coord (j : Nat) : Nat :=
  Nat.mul (Nat.shiftLeft (maskN (Nat.shiftLeft (nat_lit 1) j)) (Nat.shiftLeft (nat_lit 1) j))
    (Nat.div M4096 (maskN (Nat.shiftLeft (nat_lit 1) (Nat.add j (nat_lit 1)))))

@[expose] noncomputable def dilMask (k : Nat) : Nat :=
  Nat.mul (Nat.shiftLeft (maskN (Nat.shiftLeft (nat_lit 1) k)) (Nat.shiftLeft (nat_lit 1) k))
    (Nat.div (maskN (nat_lit 65536)) (maskN (Nat.shiftLeft (nat_lit 1) (Nat.add k (nat_lit 5)))))

@[expose] noncomputable def dil (x : Nat) : Nat :=
  iterN (nat_lit 12) (fun i y => (fun k => sN (Nat.land y (dilMask k)) (fun h =>
      Nat.lor (Nat.xor y h) (Nat.shiftLeft h (Nat.mul (nat_lit 15) (Nat.shiftLeft (nat_lit 1) k)))))
    (Nat.sub (nat_lit 11) i)) x

@[expose] noncomputable def arrOf (pl : Nat → Nat) : Nat :=
  iterN (nat_lit 12) (fun j acc => Nat.lor acc (Nat.shiftLeft (dil (pl j)) j)) (nat_lit 0)

@[expose] noncomputable def arrNW (NW : Nat) : Nat := arrOf (fun j => applyNW NW (nat_lit 1) (coord j))

@[expose] noncomputable def arrInvNW (NW : Nat) : Nat := arrOf (fun j => applyInvNW NW (nat_lit 1) (coord j))

@[expose] noncomputable def REP : Nat :=
  Nat.div (maskN (nat_lit 14376960)) M4096

@[expose] noncomputable def hd (h x : Nat) : Nat :=
  Nat.lor (Nat.xor x (Nat.land x (nat_lit 4294967295))) h


@[expose] noncomputable def addPl (h : Nat) (L : List Nat) : Nat → (List Nat → Nat) → Nat :=
  List.rec (motive := fun _ => Nat → (List Nat → Nat) → Nat) (fun _ k => k List.nil)
    (fun P rest ih x k => Bool.rec (motive := fun _ => Nat)
      (sN (hd h (Nat.xor P x)) (fun Q => ih (Nat.land P x) (fun rest' => k (List.cons Q rest'))))
      (k (List.cons P rest)) (Nat.beq x (nat_lit 0))) L

@[expose] noncomputable def keysK (FS FI FT FM : Nat → Nat) (a r cnt : Nat) :
    Nat → List Nat → (Nat → List Nat → Nat) → Nat :=
  Nat.rec (motive := fun _ => Nat → List Nat → (Nat → List Nat → Nat) → Nat) (fun T L k => k T L)
    (fun i ih T L k => sN (Nat.add a (Nat.sub (Nat.sub cnt (nat_lit 1)) i)) (fun p => sN (ent FS p) (fun u =>
      (fun h => sN (hd h (Nat.lor T (Nat.shiftLeft (nat_lit 1) (Nat.add (nat_lit 32) (ent FI (ent FT u)))))) (fun T' =>
        addPl h L (Nat.shiftLeft (rowAt FM u) (nat_lit 32)) (fun L' => ih T' L' k)))
      (Nat.lor (Nat.shiftLeft r (nat_lit 16)) (Nat.add p (nat_lit 1)))))) cnt


@[expose] noncomputable def eqPl (P NS : Nat) : Bool :=
  Nat.beq (Nat.land (Nat.xor P (Nat.shiftLeft P (nat_lit 1))) (Nat.shiftLeft NS (nat_lit 32))) (nat_lit 0)

@[expose] noncomputable def eqCheck (T : Nat) (L : List Nat) (NS : Nat) : Bool :=
  andB (eqPl T NS) (List.rec (motive := fun _ => Bool) true (fun P _ ih => andB (eqPl P NS) ih) L)


@[expose] noncomputable def tdS (TD i : Nat) : Nat := Nat.land (Nat.shiftRight TD (Nat.mul (nat_lit 24) i)) (nat_lit 4095)
@[expose] noncomputable def tdE (TD i : Nat) : Nat :=
  Nat.land (Nat.shiftRight TD (Nat.add (Nat.mul (nat_lit 24) i) (nat_lit 12))) (nat_lit 4095)

@[expose] noncomputable def isCell (S n c e : Nat) : Bool :=
  andB (Nat.blt c e) (andB (Nat.ble e n) (andB (bt S c) (andB (orB (Nat.beq e n) (bt S e))
    (Nat.beq (Nat.land (Nat.shiftRight S (Nat.add c (nat_lit 1))) (maskN (Nat.sub (Nat.sub e c) (nat_lit 1))))
      (nat_lit 0)))))

@[expose] noncomputable def initOk (TD m S n : Nat) : Bool :=
  andB (Nat.blt (nat_lit 0) m) (andB (Nat.beq (tdS TD (nat_lit 0)) (nat_lit 0))
    (andB (Nat.beq (tdE TD (Nat.sub m (nat_lit 1))) n)
      (allLt m (fun i => andB (isCell S n (tdS TD i) (tdE TD i))
        (orB (Nat.beq i (nat_lit 0)) (Nat.beq (tdS TD i) (tdE TD (Nat.sub i (nat_lit 1)))))))))


@[expose] noncomputable def mkSt (r S l j : Nat) : Nat :=
  Nat.lor r (Nat.lor (Nat.shiftLeft S (nat_lit 16))
    (Nat.lor (Nat.shiftLeft l (nat_lit 4112)) (Nat.shiftLeft j (nat_lit 4128))))


@[expose] noncomputable def rangeOk (FS : Nat → Nat) (n : Nat) : Bool :=
  allLt n (fun p => Nat.blt (ent FS p) n)


@[expose] noncomputable def rootIn (n TA NW TD f ST0 : Nat) : Bool :=
  fsplit (nat_lit 1024) (nat_lit 6) (arrNW NW) (fun FS => fsplit (nat_lit 1024) (nat_lit 6) TA (fun FT =>
    andB (andB (andB (Nat.blt (nat_lit 0) f) (Nat.blt f n)) (rangeOk FS n))
      (andB (allLt n (fun p => sB (ent FS p) (fun v => Nat.beq (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (nat_lit 1)
          (Nat.beq (ent FT v) v)) (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (nat_lit 1) (Nat.blt p f)))))
        (sB (Nat.lor (nat_lit 1) (Nat.shiftLeft (nat_lit 1) f)) (fun Sin =>
          andB (initOk TD (nat_lit 2) Sin n) (Nat.beq ST0 (mkSt (nat_lit 0) Sin (nat_lit 2) (nat_lit 0))))))))


end CFSG.KLC.Fi22

end
