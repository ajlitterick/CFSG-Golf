module

public import CFSG.ClassicalInvolution.Asc77.WP3SCUEndPos
public import CFSG.ClassicalInvolution.Asc77.WP3SCUModel4U

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG CFSG.Open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

section Proved

variable (p f : ℕ) [Fact p.Prime]

theorem chainFrameHyp51t_proved : ChainFrameHyp51t p f :=
  chainFrameHyp51t_of_psu p f fun _ _ hp2 h5 => rankFourFacts_psu _ hp2 h5

theorem chainFrameGenT_proved : ChainFrameGenT p f :=
  chainFrameGenT_of_psu p f fun _ _ hp2 h5 => rankFourFacts_psu _ hp2 h5

end Proved

end CFSG.ClassicalInvolution.Asc77
