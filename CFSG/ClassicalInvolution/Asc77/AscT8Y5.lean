module

public import CFSG.ClassicalInvolution.Asc77.AscT8Y4
public import CFSG.ClassicalInvolution.Asc77.AscT8S26NoF

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

variable {p f : ℕ} [Fact p.Prime]

theorem c27_8nE4_of_c27_YnE4 (h : C27_YnE4 p f) : C27_8nE4 p f := by
  intro G _ _ _ Ω K J S R T W z t hs hdisc hE4
  have hx : z * t * (z * t) = 1 :=
    T8.mul_self_zt hs.stand.odd hs.stand.hyp hs.hz hs.hJ hs.ht
  exact T8.centralizer_le_sigmaNorm_of_layerJoin_le hs
    ((T8.layerJoin_le_rLayer hs.stand.odd hs.stand.five hs.stand.hyp hx).trans
      (h G Ω K J S R T W z t hs hdisc hE4))


end CFSG.ClassicalInvolution.Asc77
