module

public import CFSG.Quasithin.Recognition.CertPermList

public section

namespace CFSG.ASVolI

open CFSG.Quasithin

@[expose] def burnsideF48s_ev {G : Type*} [Group G] {m : ℕ} (h : Fin m → G)
    (w : List (Fin m × Bool)) : G :=
  (w.map fun l => cond l.2 (h l.1) (h l.1)⁻¹).prod

section Lists

variable {n : ℕ}


@[expose] def burnsideF48s_eInvW (w : List (Fin n × Bool)) : List (Fin n × Bool) :=
  (w.map fun l => (l.1, !l.2)).reverse

@[expose] def burnsideF48s_eCandRel (m : ℕ) (u v w : List (Fin n × Bool)) :
    List (Fin n × Bool) :=
  (List.replicate m (u ++ v)).flatten ++ burnsideF48s_eInvW w

@[expose] def burnsideF48s_eWs (R1 R2 : List (List (Fin n × Bool))) (m : ℕ)
    (u v w : List (Fin n × Bool)) : List (List (Fin n × Bool)) :=
  R1 ++ R2 ++ [burnsideF48s_eCandRel m u v w]

end Lists


end CFSG.ASVolI
