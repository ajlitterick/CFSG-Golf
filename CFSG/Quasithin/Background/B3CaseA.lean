module

public import CFSG.Quasithin.Background.B3Named
public import CFSG.Quasithin.Background.B3Class

public section

namespace CFSG.Quasithin.B3

variable {n : ℕ}

@[expose] def isRepA (n : ℕ) (K : List Tab) : Bool :=
  (List.range (n / 2)).any (fun i => seteqT K (AmL n (i + 1)))

@[expose] def chkNamedA (n : ℕ) : Bool :=
  (List.range (n / 2)).all (fun i => chkGen n (gensAm n (i + 1)) && memD (Dl n) (AmL n (i + 1)))

@[expose] def chkA (n : ℕ) (k : Mod) (e m : ℕ) : Bool :=
  chkT n e m && chkClassify n k (isRepA n) && chkNamedA n


end CFSG.Quasithin.B3
