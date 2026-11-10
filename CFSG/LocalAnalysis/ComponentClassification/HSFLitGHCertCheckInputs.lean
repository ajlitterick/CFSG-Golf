module

public import CFSG.Certificates.CosetTablePresented
public import Certificates.Data.CFSGNative.HS.Data
public meta import CFSG.Certificates.CosetTablePresented
public meta import Certificates.Data.CFSGNative.HS.Data
public meta import Mathlib
public import Mathlib

public section

namespace CFSG.ComponentClassification.HSFLit.GHCert

open CFSG.CosetTable CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.HS.Native

set_option compiler.extract_closed false

@[expose] def ghWordsD : List (List (Fin 9 × Bool)) :=
  [[(1, true), (1, true), (0, false)],
    [(2, true), (2, true), (0, false)],
    [(3, true), (3, true), (0, false)],
    [(4, true), (4, true), (0, false)],
    [(5, true), (5, true), (0, false)],
    [(0, true), (0, true)],
    [(6, true), (6, true)],
    [(7, true), (7, true)],
    [(8, true), (8, true)],
    [(2, false), (4, false), (2, true), (4, true), (0, false)],
    [(3, false), (5, false), (3, true), (5, true), (0, false)],
    [(6, false), (2, false), (6, true), (2, true), (0, false)],
    [(6, false), (3, false), (6, true), (3, true), (0, false)],
    [(7, false), (3, false), (7, true), (3, true), (0, false)],
    [(8, false), (1, false), (8, true), (1, true), (0, false)],
    [(6, false), (4, false), (6, true), (4, true), (2, false)],
    [(6, false), (5, false), (6, true), (5, true), (3, false)],
    [(7, false), (4, false), (7, true), (4, true), (1, false), (3, false), (2, false)],
    [(7, false), (5, false), (7, true), (5, true), (0, false), (1, false), (2, false)],
    [(8, false), (2, false), (8, true), (2, true), (0, false), (3, false), (2, false)],
    [(8, false), (3, false), (8, true), (3, true), (0, false), (3, false), (2, false)],
    [(8, false), (4, false), (8, true), (4, true), (0, false), (5, false), (4, false)],
    [(8, false), (5, false), (8, true), (5, true), (0, false), (5, false), (4, false)],
    [(8, false), (7, false), (8, true), (7, true), (0, false), (1, false), (3, false), (2, false),
      (6, false)],
    [(0, true), (1, true), (0, false), (1, false)],
    [(0, true), (2, true), (0, false), (2, false)],
    [(0, true), (3, true), (0, false), (3, false)],
    [(0, true), (4, true), (0, false), (4, false)],
    [(0, true), (5, true), (0, false), (5, false)],
    [(0, true), (6, true), (0, false), (6, false)],
    [(0, true), (7, true), (0, false), (7, false)],
    [(0, true), (8, true), (0, false), (8, false)],
    [(1, true), (2, true), (1, false), (2, false)],
    [(1, true), (3, true), (1, false), (3, false)],
    [(1, true), (4, true), (1, false), (4, false)],
    [(1, true), (5, true), (1, false), (5, false)],
    [(1, true), (6, true), (1, false), (6, false)],
    [(1, true), (7, true), (1, false), (7, false)],
    [(2, true), (3, true), (2, false), (3, false)],
    [(2, true), (5, true), (2, false), (5, false)],
    [(2, true), (7, true), (2, false), (7, false)],
    [(3, true), (4, true), (3, false), (4, false)],
    [(4, true), (5, true), (4, false), (5, false)],
    [(6, true), (7, true), (6, false), (7, false)],
    [(6, true), (8, true), (6, false), (8, false)]]

@[expose] def abWords : List (List ℤ) :=
  [[1],
    [2, 1, 2, 1, 2, 2, 1, -2, 1, 2, 1, -2, -2, 1, -2, -2, 1, 2, 1, -2, -1, 2, 2, -1, 2, -1, 2],
    [2, 1, -2, 1, -2, 1, -2, -2, 1, 2, 1, 2, 1, -2, 1, -2, -2, 1, -2, -1, -2, -2, -1, 2, 2, -1,
      -2, -1, 2, 2],
    [2, 1, 2, 1, 2, 2, 1, -2, 1, 2, 1, 2, 2, 1, 2, 1, -2, -2, 1, 2, -1, 2, -1, 2, 2, -1, -2, -1,
      2, 2, -1, -2],
    [-2, 1, -2, 1, -2, 1, -2, 1, 2, 1, -2, 1, -2, 1, 2, 2, 1, -2, -2, -1, -2, -1, 2, -1, -2, -1,
      2],
    [-2, 1, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, -1, -2, -2, -1, -2, -2, -1, -2],
    [-2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, -2, -2, 1, -2, -2, -1, 2, -1, 2, 2, -1, -2,
      -2, -1, -2, -2, -1],
    [2, 2, 1, -2, -2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 1, -2, -2, 1, -2, -1, -2, -1, 2, 2, -1, -2,
      -1, -2, -2, -1],
    [-2, -2, 1, 2, 1, -2, 1, 2, 1, 2, 1, 2, 1, 2, 2, 1, -2, -2, 1, -2, -1, -2, -1, -2, -1, 2, -1,
      -2, -1, 2, 2]]


@[expose] def gens9 (T Ti : Array Table) (c : ℤ) : Table :=
  if 0 < c then T[(c - 1).toNat]! else Ti[(-c - 1).toNat]!

@[expose] def nfCodes (k : ℕ) : List ℤ :=
  (List.range 9).filterMap fun i => if k.testBit i then some ((i : ℤ) + 1) else none


end CFSG.ComponentClassification.HSFLit.GHCert
