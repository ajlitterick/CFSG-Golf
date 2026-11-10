module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Simple2S5.S2S5TSpecB
public import Certificates.Certificate442204

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Simple2S5

open CFSG.EvenSporadicStandard.HNRecog

section Cert

theorem dFacts_of_cert (hP : Nat.card ↥P1408 = 177408000) : DFacts :=
  Certificates.certificate442204 hP

end Cert

end CFSG.EvenSporadicStandard.HNRecog.Simple2S5
