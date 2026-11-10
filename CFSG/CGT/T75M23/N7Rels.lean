module

public import CFSG.Certificates.CosetTablePresented
public import Mathlib.Algebra.Order.Ring.Star

public section

namespace CFSG.CGT.T75M23

open CFSG.CosetTable

@[expose] def rels7 : List (List (Fin 6 × Bool)) :=
  [[(0, true), (0, true)],
   [(1, true), (1, true), (1, true), (1, true), (1, true)],
   [(0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false),
    (0, true), (1, true), (0, true), (1, false)],
   [(1, false), (0, true), (1, false), (0, true), (1, false), (0, true), (1, false), (0, true),
    (1, false), (0, true), (1, false), (0, true), (1, false), (0, true)],
   [(0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true),
    (1, true), (0, true), (1, false), (0, true), (1, true), (1, true), (0, true), (1, false)],
   [(2, true), (2, true)],
   [(3, true), (3, true)],
   [(4, true), (4, true)],
   [(5, true), (5, true)],
   [(2, true), (3, true), (2, true), (3, true)],
   [(2, true), (4, true), (2, true), (4, true)],
   [(2, true), (5, true), (2, true), (5, true)],
   [(3, true), (4, true), (3, true), (4, true)],
   [(3, true), (5, true), (3, true), (5, true)],
   [(4, true), (5, true), (4, true), (5, true)],
   [(0, true), (2, true), (0, false), (5, false), (2, false)],
   [(0, true), (3, true), (0, false), (5, false), (3, false)],
   [(0, true), (4, true), (0, false), (5, false), (4, false), (3, false), (2, false)],
   [(0, true), (5, true), (0, false), (5, false)],
   [(1, true), (2, true), (1, false), (3, false)],
   [(1, true), (3, true), (1, false), (4, false), (3, false)],
   [(1, true), (4, true), (1, false), (5, false), (3, false)],
   [(1, true), (5, true), (1, false), (3, false), (2, false)]]

abbrev rels7K := restrictWords (subsetOf 6 [0, 1]) rels7


end CFSG.CGT.T75M23
