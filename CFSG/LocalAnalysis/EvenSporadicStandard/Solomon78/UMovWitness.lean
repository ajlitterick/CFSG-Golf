module

public import CFSG.Sporadic.SmallOddCore.CentSpec

public section

namespace CFSG.EvenSporadicStandard.Solomon78

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native
open CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.SmallOddCore

@[expose] def umovWitOK (n : ℕ) (sift : Table → Bool) (l r r' : Table) : Bool :=
  permOK n l && sift l && invOK n l (invT n l) && permOK n r && permOK n r' &&
    commTT n (conjT n l (invT n l) r) r'


end CFSG.EvenSporadicStandard.Solomon78
