module

public import CFSG.Quasithin.Background.B3Chk

public section

namespace CFSG.Quasithin.B3


@[expose] def Tgl (n : ℕ) (b : Bool) : List Tab := if b then Tl n else (Tl n).filter isEvenT

@[expose] def cmask (n : ℕ) (k : Mod) (X : List Tab) (m : ℕ) : Bool :=
  X.all (fun h => inNk n k (actM n h m ^^^ m))

@[expose] def fmask (n : ℕ) (T : List Tab) (p : ℕ → Bool) (m : ℕ) : Bool :=
  T.all (fun t => p (actM n t m ^^^ m))


@[expose] def stabTab (n : ℕ) (k : Mod) (X : List Tab) (p : ℕ → Bool) : List Tab :=
  X.filter (fun h => (List.range (2 ^ n)).all (fun m => !inWk n k m || (p m == p (actM n h m))))

@[expose] def tabOf (n : ℕ) (p : ℕ → Bool) : List Bool := (List.range (2 ^ n)).map p

@[expose] def lkM (n : ℕ) (t : List Bool) (p : ℕ → Bool) (m : ℕ) : Bool :=
  if m < 2 ^ n then t.getD m false else p m


@[expose] def rTab (X T : List Tab) : List Tab :=
  T.filter (fun r => X.all (fun x => T.contains (mulT (mulT (invT x) r) x)))

@[expose] def subsetT (A B : List Tab) : Bool := A.all (fun a => B.contains a)

@[expose] def commT (a b : Tab) : Tab := mulT (mulT a b) (mulT (invT a) (invT b))

@[expose] def commGens (A B : List Tab) : List Tab := A.flatMap (fun a => B.map (commT a))

@[expose] def commSub (n : ℕ) (A B : List Tab) : List Tab := closeT n (commGens A B)


@[expose] def offsK (n : ℕ) (k : Mod) : List (List Tab) :=
  let DF := mkDF n k (Dl n)
  (Dl n).filter (fun K => offP DF (K, Fval n k K))

@[expose] def offsH (n : ℕ) (k : Mod) (b : Bool) : List (List Tab) :=
  (offsK n k).filter (fun K => subsetT K (Tgl n b))


structure FourD where
  T : List Tab
  H1 : List Tab
  H2 : List Tab
  R1 : List Tab
  R2 : List Tab
  L1 : List Tab
  L2T : List Tab
  L1d : List Tab
  A1p : List Tab
  w : ℕ


end CFSG.Quasithin.B3
