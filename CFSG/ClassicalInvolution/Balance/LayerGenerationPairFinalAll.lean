module

public import CFSG.ClassicalInvolution.Balance.LayerGenerationPairFinalTw
public import CFSG.ClassicalInvolution.Balance.LayerGenerationShortTwistedE6Frame
public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcE6Main
public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcE7Main
public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcE8Main
public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcF4Main
public import CFSG.ClassicalInvolution.Balance.LayerGenerationPairBoot
public import CFSG.ClassicalInvolution.Balance.LayerGenerationPairFinal
public import CFSG.ClassicalInvolution.RouteD.ExoticTwinProofExc

public section

namespace CFSG.ClassicalInvolution.Balance.Bootstrap

open CFSG.Assembly.LowTwoRank

theorem layerGenerationHybrid (p : ℕ) [Fact p.Prime] : LayerGenerationHybrid p :=
  layerGenerationHybrid_of_pairFrames
    (fun t e _ ht hp2 _ hadm => by
      rcases ht with rfl | rfl | rfl | rfl
      · exact ModelFacts.pairFrame_e6 hp2 hadm
      · exact ModelFacts.pairFrame_e7 hp2 hadm
      · exact ModelFacts.pairFrame_e8 hp2 hadm
      · exact ModelFacts.pairFrame_f4 hp2 hadm)
    (fun _ _ hadm hp2 _ => twistedE6_pairFrame hadm hp2)

end CFSG.ClassicalInvolution.Balance.Bootstrap
