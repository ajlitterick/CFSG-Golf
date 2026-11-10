module

public import CFSG.Sporadic.Schreier.PairJ2CheckInputs
public import Certificates.Data.CFSGNative.PairSchreier.Counts
public meta import CFSG.Sporadic.Schreier.PairJ2CheckInputs
public meta import Certificates.Data.CFSGNative.PairSchreier.Core
public meta import Certificates.Data.CFSGNative.PairSchreier.Counts

public section

namespace CFSG.Quasithin.J2Cls

open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairNative

@[expose] def p15A : List Bool :=
  [true, true, false, true, false, true, true, false, true, true, false, true, false, true, false,
    true, true, false, true, false, true, true, false, true, false, true, false]


@[expose] def p5C : List Bool :=
  [true, true, false, true, true, false, true, false, true, false, true, true, false, true, false,
    true, true, false, true, false, true, false, true, true, false, true, false, true, false]


@[expose] def w15A : List (Array Nat) := patW PairJ2.wA PairJ2.wB p15A


@[expose] def w5C : List (Array Nat) := patW PairJ2.wA PairJ2.wB p5C


@[expose] def w3A : List (Array Nat) := (List.replicate 5 w15A).flatten

@[expose] def w5A : List (Array Nat) := (List.replicate 3 w15A).flatten


@[expose] def closureOf (w : List (Array Nat)) : Array (Array Nat) × Array Nat × Array Nat :=
  conjClosureNF 315 PairJ2.levels PairJ2.bs PairJ2.gens PairJ2.gensInv
    (decodeNF PairJ2.levels (baseImgs PairJ2.bs w).toArray) 100000


end CFSG.Quasithin.J2Cls
