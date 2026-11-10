module

public import CFSG.ClassicalInvolution.RouteD.TwinSmallSeven
public import CFSG.ClassicalInvolution.RouteD.TwinSmallSixMain

public section

namespace CFSG.ClassicalInvolution.RouteD

variable {p f : ℕ} [Fact p.Prime]

theorem twinTDSmallPattern7_of_45 (h4 : TwinTDCase p f 4) (h5 : TwinTDCase p f 5) :
    Gaps.TwinTDSmallPattern7 p f :=
  twinTDSmallPattern7_of_cases h4 h5 twinTDCase_six twinTDCase_seven

end CFSG.ClassicalInvolution.RouteD
