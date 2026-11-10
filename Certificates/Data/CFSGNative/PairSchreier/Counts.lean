module

public import Certificates.Data.CFSGNative.PairSchreier.Preds

public section

namespace CFSG.Sporadic.Schreier.PairNative

@[expose] def countOrd (bs : List Nat) (m : Nat) (Bs : List (Array (Array Nat))) : Nat :=
  countW (ordPred bs m) Bs []

@[expose] def countPair (bs : List Nat) (my : Nat) (x : List (Array Nat))
    (conds : List (List Bool × Nat)) (Bs : List (Array (Array Nat))) : Nat :=
  countW (pairPred bs my x conds) Bs []


@[inline, expose] def add3 (a b : Nat × Nat × Nat) : Nat × Nat × Nat :=
  (a.1 + b.1, a.2.1 + b.2.1, a.2.2 + b.2.2)


end CFSG.Sporadic.Schreier.PairNative
