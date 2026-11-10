module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoRu.SzCoverNative

public section

namespace CFSG.EvenSporadicStandard.TwoRu.CentCover

open CFSG.CosetTable CFSG.LieType.Multipliers CFSG.Sporadic.Presentation.Ru.Exact
  CFSG.Sporadic.Bridge.SurjD.Native CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Tits
  CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.LieType.Multipliers.Tits
  CFSG.Sporadic.Recognition.RuMultiplier CFSG.Sporadic.RuSchreier CFSG.Quasithin.KGC31.RuCover
  CFSG.EvenSporadicStandard.TwoRu.SzCover

@[expose] def invW (w : List ℤ) : List ℤ := w.reverse.map fun l => -l

@[expose] def commW (u v : List ℤ) : List ℤ := u ++ v ++ invW u ++ invW v

@[expose] def jW (k : ℕ) : List ℤ := ruJWords.getD k []

@[expose] def fW : ℕ → List ℤ
  | 0 => jW 4 ++ jW 4
  | 1 => commW (jW 0) (jW 1)
  | 2 => commW (jW 0) (jW 2)
  | 3 => commW (jW 0) (jW 3)
  | 4 => commW (jW 0) (jW 5)
  | 5 => commW (jW 1) (jW 2)
  | _ => []

@[expose] def etaW (m c : ℕ) : List ℤ :=
  (List.range m).foldl (fun acc j => if c.testBit j then acc ++ fW j else acc) []

@[expose] def gIdx : List ℕ := [0, 1, 2, 5]

@[expose] def gWm (m s : ℕ) : List ℤ :=
  (List.range m).foldl (fun acc b => if s.testBit b then acc ++ jW (gIdx.getD b 0) else acc) []

@[expose] def gW (s : ℕ) : List ℤ := gWm 4 s

@[expose] def y2W : List ℤ := jW 0 ++ jW 2 ++ jW 3

@[expose] def zW : List ℤ := List.replicate 10 1

@[expose] def y5W : List ℤ := [1, 2, -1, -1, -1, 2]

@[expose] def facTerms : ℕ → List (List ℤ × Bool)
  | 0 => [([1, 2], true), ([-1, -2, -1], false), ([1, 2, 1, -2], false), ([-2, 1, 2], true)]
  | 1 => [([1, 2], true), ([-1, -2, -1], false), ([1, 2, -1, 2, -1], false),
      ([1, -2, 1, -2], true)]
  | 2 => [([1, 2], true), ([-1, -2, -1], false), ([], true), ([1, 2, 1, 1, -2], false)]
  | 3 => [([1, 2], true), ([-1, -2, -1], false), ([1, 1, 1, 1, 1], true),
      ([1, -2, 1, 1, 2], false)]
  | 4 => [([-1, -1, 2, 1], true), ([-1, -2, -1, -1], false), ([1, 1, 1, 2], false),
      ([1, 2, -1, 2, 2], true)]
  | 5 => [([1, 2], true), ([-1, -2, -1], false), ([2, 1, -2], true), ([1, 1, 2, 1, -2], false)]
  | _ => []

@[expose] def termW (t : List ℤ × Bool) : List ℤ :=
  t.1 ++ (if t.2 then y5W else invW y5W) ++ invW t.1

@[expose] def facW (k : ℕ) : List ℤ := ((facTerms k).map termW).flatten


end CFSG.EvenSporadicStandard.TwoRu.CentCover
