module

public import CFSG.ClassicalInvolution.Asc77.AscT7BFuse23
public import CFSG.ClassicalInvolution.Asc77.AscT7BExit23

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.LieType.Universal CFSG.ClassicalInvolution.RouteD

variable {p f : ℕ} [Fact p.Prime]

theorem c23_2_of_trans (hE : ThmEWithSylow p f) (htr : C23_2_trans p f) : C23_2 p f :=
  c23_2_of hE htr c23_2_fuse


end CFSG.ClassicalInvolution.Asc77
