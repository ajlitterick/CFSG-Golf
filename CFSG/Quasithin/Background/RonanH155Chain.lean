module

public import CFSG.Quasithin.Background.RonanH154Base
public import CFSG.Quasithin.Background.HMathieuChain
public import CFSG.Quasithin.Background.RonanH154Vocab
public import CFSG.Quasithin.Background.RonanH155PG2

public section

open scoped Pointwise

namespace CFSG.Quasithin.RonanH155

open CFSG.Open CFSG.Monster.Code CFSG.Quasithin CFSG.Quasithin.H.Mathieu
  CFSG.Quasithin.H.Mathieu.H16Pf CFSG.QuasithinUnique.Setup.X1 CFSG.Quasithin.RonanH143
  CFSG.Quasithin.RonanH163 CFSG.Quasithin.RonanH154

@[expose] def compA24 (a b : Array ℕ) : Array ℕ :=
  ((List.range 24).map fun i => a[b[i]!]!).toArray

@[expose] def idA24 : Array ℕ := (List.range 24).toArray


@[expose] def arrP2 (s : PG2) : Array ℕ :=
  compA24 (compA24 (koArr s.t.val) (dArrs.getD s.j.val #[])) (if s.ε = 1 then eArr else idA24)


@[expose] def actP2 (s : PG2) (m : ℕ) : ℕ := act10 (arrP2 s) m


end CFSG.Quasithin.RonanH155
