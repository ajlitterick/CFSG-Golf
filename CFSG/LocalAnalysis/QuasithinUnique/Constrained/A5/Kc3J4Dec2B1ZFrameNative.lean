module

public import CFSG.Sporadic.J4.QT2LocZCentNative
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4Dec2B1ZClNative
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4Dec2B1ZTabNative

public section

namespace CFSG.QuasithinUnique.A5

open CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2A CFSG.Sporadic.J4.QT2

@[expose] def zXi : Array V2 := x0GenRows[0]!

@[expose] def zXiInv : Array V2 := x0InvRows[0]!

@[expose] def zXiConj (T : Array V2) : Array V2 := mulRows (mulRows zXi T) zXiInv

@[expose] def zCjRows (T : Array V2) : Nat → Array V2
  | 0 => T
  | n + 1 => zXiConj (zCjRows T n)

@[expose] def zConjBy (gW : List Int) (T : Array V2) : Array V2 :=
  mulRows (mulRows (wR gW) T) (wR (invW gW))

@[expose] def zMsN (T₀ : Array V2) (gW : List Int) : Nat → Array V2
  | 0 => etaE 1
  | n + 1 => zConjBy gW (zCjRows T₀ (n + 1))

@[expose] def zMs (T₀ : Array V2) (gW : List Int) (i : Fin 4) : Array V2 := zMsN T₀ gW i

@[expose] def zYR (gW : List Int) : Array V2 := zConjBy gW zXi

@[expose] def zYiR (gW : List Int) : Array V2 := zConjBy gW zXiInv

@[expose] def zProdRows : List (Array V2) → Array V2
  | [] => idRows
  | r :: rs => mulRows r (zProdRows rs)

@[expose] def zS (i : Fin 4) : List (Fin 4) :=
  if i = 0 then [1] else if i = 1 then [2] else if i = 2 then [3] else [0, 1, 2, 3]


end CFSG.QuasithinUnique.A5
