module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1ThreeInputs
public import Certificates.Data.CFSGNative.Timmesfeld.Co1Seven
public meta import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1ThreeInputs
public meta import Certificates.Data.CFSGNative.Timmesfeld.Co1Five
public meta import Certificates.Data.CFSGNative.Timmesfeld.Co1Seven

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.Co1Pump

open CFSG.Sporadic.Co1Schreier.Native CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1.TwoBNative
  CFSG.Sporadic.Co1.InvNative CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1T.Native
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1T.Data (rootWords)


@[expose] def wv (Ls Lis : List Rows) (w : List Nat) : Rows := word Ls Lis (decWord w)

end CFSG.HardMathSupport.Solomon.Coordinator.Co1Pump
