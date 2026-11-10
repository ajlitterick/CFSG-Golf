module

public import Certificates.Data.ONanCMNormal

public section

namespace CFSG.OddStandard.ONanRec.CM


@[expose] def wpow (w : List Nat) (n : Nat) : List Nat := (List.replicate n w).flatten


@[expose] def yW : List Nat := [11, 4, 10, 4]

@[expose] def zW : List Nat := [11, 6, 10, 6]

@[expose] def dW : List Nat := [6]

@[expose] def fW : List Nat := [8]

@[expose] def gW : List Nat := [10]

@[expose] def r1W : List Nat := [0, 2]

@[expose] def r2W : List Nat := invWord yW ++ r1W ++ yW

@[expose] def rW (i j : Nat) : List Nat := wpow r1W i ++ wpow r2W j

@[expose] def rWords : List (List Nat) :=
  (List.range 3).flatMap fun i => (List.range 3).map fun j => rW i j

@[expose] def sW (k l : Nat) : List Nat := wpow zW k ++ wpow dW l


@[expose] def rsWords : List (List Nat) :=
  (List.range 3).flatMap fun i => (List.range 3).flatMap fun j =>
    (List.range 4).flatMap fun k => (List.range 2).map fun l => rW i j ++ sW k l


@[expose] def tGens : List (List Nat) := [yW, dW, gW]

@[expose] def tWord (l : List Nat) : List Nat := l.flatMap fun k => tGens[k]!

@[expose] def tIdx : List (List Nat) :=
  [[], [0], [1], [2], [0, 0], [0, 1], [0, 2], [1, 2], [2, 0], [2, 1], [2, 2], [0, 0, 0],
    [0, 0, 1], [0, 0, 2], [0, 1, 2], [0, 2, 1], [0, 2, 2], [1, 2, 0], [1, 2, 1], [1, 2, 2],
    [2, 0, 1], [2, 0, 2], [2, 1, 2], [2, 2, 2], [0, 0, 0, 1], [0, 0, 1, 2], [0, 0, 2, 1],
    [0, 0, 2, 2], [0, 1, 2, 1], [0, 1, 2, 2], [0, 2, 1, 2], [0, 2, 2, 2], [1, 2, 0, 1],
    [1, 2, 0, 2], [1, 2, 1, 2], [1, 2, 2, 2], [2, 0, 1, 2], [2, 0, 2, 2], [2, 1, 2, 1],
    [2, 1, 2, 2], [0, 0, 1, 2, 1], [0, 0, 1, 2, 2], [0, 0, 2, 1, 2], [0, 0, 2, 2, 2],
    [0, 1, 2, 1, 2], [0, 1, 2, 2, 2], [0, 2, 1, 2, 1], [0, 2, 1, 2, 2], [1, 2, 0, 1, 2],
    [1, 2, 0, 2, 2], [1, 2, 1, 2, 1], [1, 2, 1, 2, 2], [2, 0, 1, 2, 1], [2, 0, 1, 2, 2],
    [2, 1, 2, 2, 2], [0, 0, 1, 2, 1, 2], [0, 0, 1, 2, 2, 2], [0, 0, 2, 1, 2, 1],
    [0, 0, 2, 1, 2, 2], [0, 1, 2, 1, 2, 1], [0, 1, 2, 1, 2, 2], [0, 2, 1, 2, 2, 2],
    [1, 2, 0, 1, 2, 2], [0, 0, 1, 2, 1, 2, 2]]

@[expose] def qWords : List (List Nat) :=
  (List.range 4).flatMap fun k => (List.range 2).map fun l => wpow yW k ++ wpow fW l

@[expose] def wPowWords (w : List Nat) : List (List Nat) := (List.range 4).map (wpow w)

@[expose] def swWords (w : List Nat) : List (List Nat) :=
  (List.range 4).flatMap fun k => (List.range 2).flatMap fun l =>
    (List.range 4).map fun m => sW k l ++ wpow w m


end CFSG.OddStandard.ONanRec.CM
