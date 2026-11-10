module

public import CFSG.ClassicalInvolution.Asc77.AscT7ERIdx
public import CFSG.ClassicalInvolution.Asc77.AscT7DRFinalX

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

variable {p f : ℕ} [Fact p.Prime]


theorem c25_E4_of_idx (h17 : C25_17_idx p f) (h20 : C25_20 p f) : C25_E4 p f :=
  c25_E4_of_sylow (c25_2_t_proved p f) h17 h20


end CFSG.ClassicalInvolution.Asc77
