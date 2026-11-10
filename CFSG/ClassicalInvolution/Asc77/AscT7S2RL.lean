module

public import CFSG.ClassicalInvolution.Asc77.AscT7RH
public import CFSG.ClassicalInvolution.Asc77.AscT7S2RE
public import CFSG.ClassicalInvolution.Asc77.AscT7S2RK

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

variable {p f : ℕ} [Fact p.Prime]

theorem c21_14_Y_disc_of_C3 (hC3 : C21_3 p f) : C21_14_Y_disc p f :=
  c21_14_Y_disc_of_S4 p f hC3 (T7S2R.ih8S4Star p f)

theorem c21_14_Y_disc_of_hyp51 (hHt : TwinFrameHyp51t p f) (hHu : TwinFrameHyp51u p f) :
    C21_14_Y_disc p f :=
  c21_14_Y_disc_of_C3 (c21_3_of_hyp51 hHt hHu)


end CFSG.ClassicalInvolution.Asc77
