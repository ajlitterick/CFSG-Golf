module

public import CFSG.Sporadic.SmallOddCore.LocalCheck

public section

namespace CFSG.ComponentClassification.HarrisLit.P1

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore
  CFSG.Sporadic.SmallOddCore.Native

inductive RowKind where
  | inner
  | noFive
  | small (gens : List Table) (ord : Nat)
  | five (gens : List Table) (ord : Nat)
  | a6 (l₁ l₂ : Table) (w : List (Option Table))

@[expose] def RowKind.isA6 : RowKind → Bool
  | .a6 _ _ _ => true
  | _ => false

structure Row where
  row : ClassRow
  kind : RowKind

structure Run where
  u : Table
  sylowGens : List Table
  sylowOrder : Nat
  rows : List Row

instance : Inhabited Run := ⟨⟨#[], [], 0, []⟩⟩

@[expose] def a6a : Table := #[1, 2, 0, 3, 4, 5]

@[expose] def a6b : Table := #[0, 2, 3, 4, 5, 1]

@[expose] def diagT (n : Nat) (x y : Table) : Table :=
  Array.ofFn (n := n + 6) fun i =>
    if i.val < n then x[i.val]! else y[i.val - n]! + UInt32.ofNat n


@[expose] def ord8 (n : Nat) (x : Table) : Bool :=
  tblEq n (powT n 8 x) (idT n) && !tblEq n (powT n 4 x) (idT n)


@[expose] def extraOK (n : Nat) (pg : Array Table) (sift : Table → Bool) (u : Table) : Bool :=
  permOK n u && invOK n u (invT n u) && !sift (compT n u u) &&
    pg.all fun g => sift (conjT n u (invT n u) g)


end CFSG.ComponentClassification.HarrisLit.P1
