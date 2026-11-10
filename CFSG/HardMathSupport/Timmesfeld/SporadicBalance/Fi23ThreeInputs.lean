module

public import Certificates.Data.CFSGNative.Fi23.Certificate
public import Certificates.Data.E27Table
public meta import Certificates.Data.CFSGNative.Fi23.Certificate
public meta import Certificates.Data.E27Table

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23Native

open CFSG.Sporadic.Fi23.Native CFSG.Sporadic.Th.Native CFSG.HardMathSupport.Foote.E27

set_option compiler.extract_closed false

@[expose] def qWords : Array (List Nat) :=
  #[[3, 12, 7, 2, 0, 19, 9, 5, 9, 15, 12, 8, 8, 8, 15, 18, 12, 12, 17, 22, 17, 17, 17, 18, 22],
    [2, 17, 19, 7, 0, 15, 10, 19, 4, 20, 12, 17, 9, 13, 17, 22, 13, 22, 16, 16, 19, 17, 22, 20],
    [10, 3, 16, 7, 0, 14, 4, 17, 4, 10, 9, 13, 11, 12, 12, 16, 12, 18, 17, 17, 19, 16, 22, 20]]


@[expose] def qLettersT (letters : Array Table) (w : List Nat) : Table :=
  w.foldr (fun l T => compT 31671 letters[l]! T) (idT 31671)

@[expose] def qGens (letters : Array Table) : Array Table := qWords.map (qLettersT letters)

@[expose] def qKeyAt (img : Array Nat) (s : Nat) : UInt64 × UInt64 :=
  ((img[s]!).toUInt64 + ((img[s + 1]!).toUInt64 <<< 16) + ((img[s + 2]!).toUInt64 <<< 32) +
    ((img[s + 3]!).toUInt64 <<< 48), (img[s + 4]!).toUInt64 + ((img[s + 5]!).toUInt64 <<< 16))

structure QEnum where
  par : Array (Nat × Nat)
  img : Array Nat
  L : Array (Array Nat)
  H : Std.HashMap (UInt64 × UInt64) Nat

@[expose] def qStepImg (T : Table) (img : Array Nat) (s : Nat) : Array Nat :=
  #[ap T img[s]!, ap T img[s + 1]!, ap T img[s + 2]!, ap T img[s + 3]!, ap T img[s + 4]!,
    ap T img[s + 5]!]


@[expose] def qTreeOK (G : Array Table) (P : Array (Nat × Nat)) (img : Array Nat) (N : Nat) :
    Bool :=
  allIn 0 6 (fun t => img[t]! == t) &&
    allIn 1 N fun i => decide ((P[i]!).1 < i) && decide ((P[i]!).2 < G.size) &&
      allIn 0 6 fun t => img[6 * i + t]! == ap G[(P[i]!).2]! img[6 * (P[i]!).1 + t]!

@[expose] def qLeftOK (G : Array Table) (L : Array (Array Nat)) (img : Array Nat) (N : Nat) :
    Bool :=
  allIn 0 G.size fun j => allIn 0 N fun i => decide ((L[j]!)[i]! < N) &&
    allIn 0 6 fun t => img[6 * (L[j]!)[i]! + t]! == ap G[j]! img[6 * i + t]!

@[expose] def qInjOK (H : Std.HashMap (UInt64 × UInt64) Nat) (img : Array Nat) (N : Nat) : Bool :=
  allIn 0 N fun i => (H.get? (qKeyAt img (6 * i))).getD N == i


@[expose] def qActPt (P : Array (Nat × Nat)) (G : Array Table) (r x : Nat) : Nat :=
  if _h : (P[r]!).1 < r then ap G[(P[r]!).2]! (qActPt P G (P[r]!).1 x) else x
termination_by r
decreasing_by exact _h


end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23Native
