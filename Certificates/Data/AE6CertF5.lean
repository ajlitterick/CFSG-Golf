module

public import Certificates.Data.CFSGNative.SmallOddCore.Check
public import Mathlib.Data.List.Permutation

public section

namespace Certificates.AE6Model

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore.Native

@[expose] def fLetterHat : List (List ℕ) :=
  [[3, 4, 5, 0, 1, 2, 9, 11, 10, 6, 8, 7], [4, 5, 3, 2, 0, 1, 11, 10, 9, 8, 7, 6],
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11], [6, 7, 8, 9, 11, 10, 0, 1, 2, 3, 5, 4],
    [8, 6, 7, 10, 9, 11, 1, 2, 0, 4, 3, 5], [9, 10, 11, 6, 8, 7, 3, 5, 4, 0, 1, 2],
    [11, 9, 10, 7, 6, 8, 4, 3, 5, 1, 2, 0]]

@[expose] def fGammaHat : List (List ℕ) :=
  [[9, 11, 10, 3, 4, 5, 6, 7, 8, 0, 2, 1], [6, 8, 7, 3, 4, 5, 0, 2, 1, 9, 10, 11]]


end Certificates.AE6Model
