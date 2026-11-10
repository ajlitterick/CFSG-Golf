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


end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23Native
