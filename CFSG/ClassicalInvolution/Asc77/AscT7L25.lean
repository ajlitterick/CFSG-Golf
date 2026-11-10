module

public import CFSG.ClassicalInvolution.Asc77.AscT7L15
public import CFSG.ClassicalInvolution.Asc77.AscT7L18
public import CFSG.ClassicalInvolution.Asc77.AscT7L21
public import CFSG.ClassicalInvolution.Asc77.AscT7L24

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.Asc77.ExactLayer CFSG.LieType.Universal

variable {p f : ℕ} [Fact p.Prime]

theorem e4TwinGen_proved : E4TwinGen p :=
  e4TwinGen_of_rows (T7L.e4GenSp p) (T7L.e4GenSL p) (T7L.e4GenSU p)

theorem c23_GammaU_proved : C23_GammaU p f :=
  c23_GammaU_of_e4 e4TwinGen_proved


end CFSG.ClassicalInvolution.Asc77
