module

public import Certificates.Data.CFSGNative.MonsterB.BinaryFiles
public import Certificates.Data.CFSGNative.MonsterB.BinaryElim
public import Certificates.Data.CFSGNative.SectionRank.F2Fast

public section

namespace CFSG.Monster.B.Binary.Native

open CFSG.Monster.B.Dyadic.Native CFSG.Sporadic.SmallF2.Native CFSG.SectionRank.Native

@[expose] def natFrom (b : ByteArray) (k : Nat) : Nat :=
  if k < b.size then (b.get! k).toNat + 256 * natFrom b (k + 1) else 0
termination_by b.size - k

@[expose] def rowNat (b : ByteArray) : Nat := natFrom b 0


@[expose] def plusId (m : Nat) (R : Array ByteArray) : List Nat :=
  (List.range m).map fun i => rowNat (R[i]!) ^^^ (1 <<< i)


@[expose] def allBelowB (b : Nat) (vs : List Nat) : Bool := vs.all fun v => decide (v < b)

@[expose] def allBelow (d : Nat) (vs : List Nat) : Bool := allBelowB (2 ^ d) vs


@[expose] def allRows (C : Array (Array ByteArray)) : List Nat :=
  (List.range 26).flatMap fun g => plusId 4371 (C[g]!)


@[expose] def fullTable (d : Nat) (T : Array Nat) : Bool :=
  T.size == d && allLt d fun p => T[p]! != 0


@[expose] def fullOpt (d : Nat) : Option (Array Nat) → Bool
  | none => false
  | some T => fullTable d T

@[expose] def rankOpt (d r : Nat) : Option (Array Nat) → Bool
  | none => false
  | some T => T.size == d && tableRank d T == r


@[expose] def rowsOKOf (vs : List Nat) : Bool :=
  allBelow 4371 vs && fullOpt 4371 (elimTable 4371 vs)

@[expose] def rankOKOf (vs : List Nat) (r : Nat) : Bool :=
  allBelow 4370 vs && rankOpt 4370 r (elimTable 4370 vs)


@[expose] def rowsOK (C : Array (Array ByteArray)) : Bool := rowsOKOf (allRows C)

@[expose] def rankOK (Q : Array (Array ByteArray)) (g r : Nat) : Bool :=
  rankOKOf (plusId 4370 (Q[g]!)) r


end CFSG.Monster.B.Binary.Native
