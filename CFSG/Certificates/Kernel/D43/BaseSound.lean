module

public import Certificates.Data.Kernel.D43.Base
public import CFSG.Milestones.ASVolI.F48.Small.Pres
import CFSG.Certificates.Kernel.Spor.PackFld

public section

namespace CFSG.KC.D43

open CFSG.ASVolI CFSG.KS.PackFld CFSG.KC.Enum

section Group

variable {G : Type*} [Group G]


theorem ev_invW {m : ℕ} (h : Fin m → G) (w : List (Fin m × Bool)) :
    burnsideF48s_ev h (invW w) = (burnsideF48s_ev h w)⁻¹ := by
  induction w with
  | nil => simp [invW, burnsideF48s_ev]
  | cons l w ih =>
    have e : invW (l :: w) = invW w ++ [(l.1, !l.2)] := by simp [invW]
    rw [e, burnsideF48s_ev_append, ih, burnsideF48s_ev_cons, burnsideF48s_ev_cons, mul_inv_rev]
    obtain ⟨j, b⟩ := l
    cases b <;> simp [burnsideF48s_ev]


end Group

section Points


end Points

end CFSG.KC.D43

end
