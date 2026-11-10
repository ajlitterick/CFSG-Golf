module

public import CFSG.Quasithin.Background.B3J
public import CFSG.Quasithin.Background.B3CaseA
public import CFSG.Quasithin.Background.B3CaseB

public section

namespace CFSG.Quasithin.B3

@[expose] def rankOK (n : ℕ) (k : Mod) (L : List Tab) (r s : ℕ) : Bool :=
  L.length == 2 ^ r && cntF n k L * 2 ^ s == cntF n k [idT n]

@[expose] def rkPair (n : ℕ) (k : Mod) (L : List Tab) : ℕ × ℕ :=
  (Nat.log 2 L.length, Nat.log 2 (cntF n k [idT n] / cntF n k L))


@[expose] def qRow (n : ℕ) (k : Mod) (snum sden : ℕ) (L : List Tab) : Bool :=
  rankOK n k L (rkPair n k L).1 (rkPair n k L).2 && decide (0 < (rkPair n k L).1) &&
    decide (snum * (rkPair n k L).1 ≤ sden * (rkPair n k L).2)

@[expose] def qWit (n : ℕ) (k : Mod) (snum sden : ℕ) (L : List Tab) : Bool :=
  decide (sden * (rkPair n k L).2 ≤ snum * (rkPair n k L).1)


@[expose] def suppCardT (t : Tab) : ℕ := (List.range t.length).countP (fun i => t.getD i 0 != i)


@[expose] def t12 (n : ℕ) : Tab := tab (ti n 0 * ti n 1)


end CFSG.Quasithin.B3
