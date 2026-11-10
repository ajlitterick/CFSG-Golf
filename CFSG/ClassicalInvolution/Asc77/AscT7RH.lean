module

public import CFSG.ClassicalInvolution.Asc77.AscT7FJ
public import CFSG.ClassicalInvolution.Asc77.AscT7RB
public import CFSG.ClassicalInvolution.Asc77.AscT7RG

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

variable {p f : ℕ} [Fact p.Prime]

theorem c21_3_of_hyp51 (hHt : TwinFrameHyp51t p f) (hHu : TwinFrameHyp51u p f) :
    C21_3 p f :=
  c21_3_of p f (twinFrameHyp51_of_cases (twinFrameHyp51z p f) hHt hHu)


end CFSG.ClassicalInvolution.Asc77
