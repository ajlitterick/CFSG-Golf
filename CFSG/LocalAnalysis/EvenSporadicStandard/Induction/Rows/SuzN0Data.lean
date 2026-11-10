module

public import CFSG.Sporadic.SuzOddCore.InvTCheckInputs
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.SuzN0Tbl
public import Certificates.Data.CFSGNative.PSL3Four.Basic
public meta import CFSG.Sporadic.SuzOddCore.InvTCheckInputs
public meta import CFSG.Sporadic.SuzOddCore.InvArrays
public meta import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.SuzN0Tbl
public meta import Certificates.Data.CFSGNative.PSL3Four.Basic
public meta import Certificates.Data.CFSGNative.Schreier.Check

public section

namespace CFSG.EvenSporadicStandard.SuzN0

open CFSG.PSL3Four.Native CFSG.Sporadic.SuzOddCore CFSG.Monster.B.Co2.Native
  CFSG.Certificates.Native

@[expose] def gens0 : Array Tab := invInnerGenArrs 0

@[expose] def xTab (j : Nat) : Tab :=
  commTab 1782 gens0[1]! gens0[j + 2]! (invTab 1782 gens0[1]!) (invTab 1782 gens0[j + 2]!)

@[expose] def xs : Array Tab := Array.ofFn (n := 5) fun j => xTab j.val

@[expose] def xsInv : Array Tab := xs.map (invTab 1782)

@[expose] def letterX (l : Int) : Tab :=
  if 0 < l then xs[l.toNat - 1]! else xsInv[(-l).toNat - 1]!

@[expose] def wordX (w : List Int) : Tab :=
  w.foldr (fun l acc => comp 1782 (letterX l) acc) (idTab 1782)


@[expose] def oddWords : List (List Int × Nat) :=
  [([-1], 3), ([1, 5, 5], 5), ([-1], 3), ([1, 4, 5, -4], 7), ([4, -1], 5), ([1, 4, -5], 7),
   ([-4], 5), ([-1, -2], 3), ([5, 2, 1], 3)]

@[expose] def oddTab (k : Nat) : Tab := wordX (oddWords.getD k ([], 1)).1

@[expose] def rTab (i : Nat) : Tab := comp 1782 (oddTab (2 * i)) (oddTab (2 * i + 1))

@[expose] def rTabs : Array Tab := Array.ofFn (n := 4) fun i => rTab i.val

@[expose] def wTab : Tab := oddTab 8

@[expose] def zWord : List Int := [-5, 4, 5, 4]

@[expose] def zTab : Tab := wordX zWord


@[expose] def levD1 (_ : Unit := ()) : Array Level :=
  rawLevels 1782 (invFullStrongArrs 1) (invFullBases.getD 1 []).toArray

@[expose] def gensN (hI : Tab) : Array Tab :=
  (rTabs.push wTab).map (conjTab 1782 hI hTab)


end CFSG.EvenSporadicStandard.SuzN0
