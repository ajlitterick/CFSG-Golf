module

public import Certificates.Data.CFSGNative.Ly.Certificate

public section

namespace CFSG.Sporadic.Ly.HH

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Fi23.Native CFSG.Sporadic.Ly.Native

@[expose] def hhWords : Array (List Int) := #[
  [2, 2, 2, -1, -2, -2, -2, -2, -2, -2, -2, -1, -2, -1, 2, 2, -1, -2, -1, 2, -1, 2, 2, 2, 2,
   2, -1, -2, 1, 2, 1, -2, -2, -2, -2, -2, 1, -2, 1, 2, 1, -2, -2, 1, 2, 1, 2, 2, 2, 2, 2, 2,
   2, 1, -2, -2, -2, 1],
  [1, 2, 1, -2, -2, -2, -2, -2, 1, -2, 1, 2, 1, -2, -2, 1, 2, 1, 2, 2, 2, 2, 2, 2, 2, 1, -2,
   -2, -2, 1, 3, 3, 3, 3, 3, 3, 3],
  [4, 4],
  [2, 2, 1, -2, 1, 2, 1, -2, 1, 2, 1, -2, 1, 2, 2],
  [1, 6, 1, -6],
  [5, 5, 5, 5, 5, 5, 5],
  [8, 7, -8],
  [9, 7, -9, -7]
]

@[expose] def hhRels : List (List Int × List Int) := [
  (List.replicate 21 5, []),
  ([1, 5], [5, 1]),
  (List.replicate 5 7, []),
  ([10, 7], [7, 10]),
  ([10, 9], [9, 10]),
  (List.replicate 5 10, []),
  ([8, 9, -8], List.replicate 4 7 ++ List.replicate 4 9 ++ List.replicate 3 10),
  ([9], [8, 7, -8]),
  ([10], [9, 7, -9, -7]),
  ([8], List.replicate 7 5)
]

@[expose] def hhNe : List (List Int × List Int × Nat) := [
  (List.replicate 7 5, [], 0),
  (List.replicate 3 5, [], 0),
  ([9], [7], 0)
]


end CFSG.Sporadic.Ly.HH
