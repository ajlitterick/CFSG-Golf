module

public import CFSG.ClassicalInvolution.Asc77.AscT7L4
public import CFSG.ClassicalInvolution.Asc77.AscT7K11

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.Asc77.ExactLayer CFSG.LieType.Universal

variable {p f : ℕ} [Fact p.Prime]

theorem c23_5X_type_of_tcf (htcf : TwinCentralFact p) : C23_5X_type p f := by
  intro G _ _ _ Ω K K' W z u e g h
  have hs : Hyp23Setting p f Ω K K' z := h.std.setting
  have hd : Hyp23bData Ω K K' W z u e g := h.data
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hrl : rLayer Ω u = exactLayer Ω u :=
    rLayer_eq_exactLayer hs.stand.odd hs.stand.five hΩ hd.hu2
  rw [hrl]
  exact T7L.layer_u_tag htcf hs hd


end CFSG.ClassicalInvolution.Asc77
