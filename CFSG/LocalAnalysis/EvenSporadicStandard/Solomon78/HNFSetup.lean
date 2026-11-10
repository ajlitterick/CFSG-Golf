module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.HNFSound
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.HNFCount

public section

namespace CFSG.EvenSporadicStandard.Solomon78

open Subgroup CFSG.Sporadic.HNSchreier CFSG.ONSchreier CFSG.ONSchreier.Native
  CFSG.Sporadic.HNSchreier.Native


section Setup

attribute [local irreducible] pword pcomp pinvCand

variable
  {tA tAi tB tBi g1 g1i g2 g2i : Array Nat}


theorem hnfRepWords_ok : ∀ i < 9, plettersOK 2 hnfRepWords[i]! = true := by decide


end Setup

end CFSG.EvenSporadicStandard.Solomon78
