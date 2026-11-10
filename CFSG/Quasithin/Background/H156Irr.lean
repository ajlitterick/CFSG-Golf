module

public import CFSG.Quasithin.Background.H156Gen
public import CFSG.Quasithin.AppendixH.H14.Vocab

public section

open scoped Matrix

namespace CFSG.Quasithin.H156

open CFSG.ASVolI.ChH CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.Mathieu CFSG.Monster.Code


@[expose] def g3 : List (List ℕ) :=
  [[1, 3, 4], [1, 2, 5], [3, 2, 4], [1, 2, 6], [5, 2, 4], [1, 6, 4]]

@[expose] def g2 : List (List ℕ) := [[1, 3], [3, 2]]


@[expose] def kronL (cs : List ℕ) : List ℕ :=
  (List.range 6).map fun k => cs.getD (k % 3) 0 <<< (3 * (k / 3))

@[expose] def kronR (cs : List ℕ) : List ℕ :=
  (List.range 6).map fun k =>
    ((cs.getD (k / 3) 0 &&& 1) <<< (k % 3)) ||| (((cs.getD (k / 3) 0 >>> 1) &&& 1) <<< (k % 3 + 3))

@[expose] def gT : List (List ℕ) := g3.map kronL ++ g2.map kronR


end CFSG.Quasithin.H156
