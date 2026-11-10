module

public import CFSG.ClassicalInvolution.Asc77.AscT8S26VClaims
public import CFSG.ClassicalInvolution.Asc77.AscP1Lem75
public import CFSG.ClassicalInvolution.Asc77.AscMuTabProved

public section

namespace CFSG.ClassicalInvolution.Asc77

variable {p f : ℕ} [Fact p.Prime]


theorem c26_2_of_c26_1_muZ2 (h1 : C26_1 p f) (hZ : S26XMuZ2 p f) : C26_2 p f :=
  c26_2_of_claims (l7_5_2_proved p f) ih8MuTableSect_proved (s26XTop_of_c26_1 h1) hZ


end CFSG.ClassicalInvolution.Asc77
