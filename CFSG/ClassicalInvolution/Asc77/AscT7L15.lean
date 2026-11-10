module

public import CFSG.ClassicalInvolution.Asc77.AscT7L5
public import CFSG.ClassicalInvolution.Asc77.AscT7L9
public import CFSG.ClassicalInvolution.Asc77.AscT7L11
public import CFSG.ClassicalInvolution.Asc77.AscT7L12
public import CFSG.ClassicalInvolution.Asc77.AscT7L14

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.Asc77.ExactLayer CFSG.LieType.Universal

variable {p f : ℕ} [Fact p.Prime]

theorem twinCentralFact_proved : TwinCentralFact p :=
  twinCentralFact_of_rows (T7L.twinCentralSL p) (T7L.twinCentralSU p) (T7L.twinCentralSpin7 p)
    (T7L.twinCentralD4P p) (T7L.twinCentralD4M p)

theorem c23_5X_type_proved : C23_5X_type p f :=
  c23_5X_type_of_tcf twinCentralFact_proved

theorem c23_GammaU_of_e4 (hgen : E4TwinGen p) : C23_GammaU p f :=
  c23_GammaU_of_facts twinCentralFact_proved hgen


end CFSG.ClassicalInvolution.Asc77
