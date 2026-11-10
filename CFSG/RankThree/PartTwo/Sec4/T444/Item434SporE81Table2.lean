module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporE81Table

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item434SporE81

open CFSG.Assembly (IsElemAbelian)

@[expose] def elemsOf (mul : ℕ → ℕ → ℕ) : List ℕ → List ℕ
  | [] => [0]
  | a :: gs =>
    let r := elemsOf mul gs
    r ++ r.map (mul a) ++ r.map (mul (mul a a))


end CFSG.RankThree.PartTwo.Sec4.Item434SporE81
