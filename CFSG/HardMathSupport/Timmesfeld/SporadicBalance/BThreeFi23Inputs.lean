module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeKleinInputs
public import Certificates.Data.CFSGNative.Bridge.Fi23GPL
public import Certificates.Data.CFSGNative.Fi23.Classes
public meta import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeKleinInputs
public meta import Certificates.Data.CFSGNative.Bridge.Fi23GPL
public meta import Certificates.Data.CFSGNative.Fi23.Classes

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeFi23Native

open CFSG.Sporadic.Fi23.Native CFSG.Sporadic.Th.Native CFSG.Perm.Native
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23Native
  CFSG.Sporadic.Bridge.Fi23GPL.Native

set_option compiler.extract_closed false


@[expose] def applyW (L : Array Table) (w : List Nat) (p : Nat) : Nat :=
  w.foldr (fun l q => ap L[l]! q) p


@[expose] def imgTab (O : WOrbit) (k : Nat) : Table :=
  wordT 31671 (genTables O) (imgWords ())[k]!

@[expose] def t3Tabs (O : WOrbit) (L : Array Table) : Array Table :=
  #[compT 31671 (imgTab O 2) (imgTab O 3), qLettersT L kleinZ,
    compT 31671 (compT 31671 (compT 31671 (imgTab O 4) (imgTab O 5)) (imgTab O 2)) (imgTab O 1),
    compT 31671 (compT 31671 (compT 31671 (compT 31671 (compT 31671 (imgTab O 5) (imgTab O 3))
      (imgTab O 7)) (imgTab O 0)) (imgTab O 6)) (imgTab O 1)]


end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeFi23Native
