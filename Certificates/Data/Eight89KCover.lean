module

public import CFSG.Certificates.CosetTablePresented
public import Mathlib

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.KData

open CFSG.CosetTable

@[expose] def coverWords (n i j k l : Nat) : List (List (Fin 3 × Bool)) :=
  [List.replicate n (2, true),
    [(0, false), (2, false), (0, true), (2, true)],
    [(1, false), (2, false), (1, true), (2, true)],
    [(0, true), (0, true)] ++ List.replicate (3 * i) (2, false),
    List.replicate 4 (1, true) ++ List.replicate (3 * j) (2, false),
    (List.replicate 5 [(0, true), (1, true)]).flatten ++ List.replicate k (2, false),
    (List.replicate 5 [(0, true), (1, true), (1, true)]).flatten ++ List.replicate l (2, false)]


end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.KData
