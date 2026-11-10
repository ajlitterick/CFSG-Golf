module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutExt.XModelData
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.InvCheck

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section4.XModel

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore
  CFSG.Sporadic.SmallOddCore.Native

@[inline, expose] def commB (x y : Table) : Bool :=
  ap x (ap y 0) == ap y (ap x 0) && ap x (ap y 1) == ap y (ap x 1)

@[inline, expose] def commB3 (u m t : Table) : Bool :=
  ap u (ap m (ap t 0)) == ap t (ap u (ap m 0)) && ap u (ap m (ap t 1)) == ap t (ap u (ap m 1))


end CFSG.EvenSporadicStandard.HNRecog.Section4.XModel
