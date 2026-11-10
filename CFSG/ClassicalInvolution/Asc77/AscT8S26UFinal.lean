module

public import CFSG.ClassicalInvolution.Asc77.AscT8S26ULift
public import CFSG.ClassicalInvolution.Asc77.AscT8S26UModU
public import CFSG.ClassicalInvolution.Asc77.AscT8S26NoF

public section

namespace CFSG.ClassicalInvolution.Asc77

variable {p f : ℕ} [Fact p.Prime]

theorem c26_2_u_of_c26_3 (h3 : C26_3_S4 p f) : C26_2_u p f :=
  c26_2_u_of_sec h3 (s26_aut164L p) (s26_aut164U p)

theorem c26_2_of_c26_3 (h3 : C26_3_S4 p f) : C26_2 p f :=
  c26_2_of_u (c26_2_u_of_c26_3 h3)


end CFSG.ClassicalInvolution.Asc77
